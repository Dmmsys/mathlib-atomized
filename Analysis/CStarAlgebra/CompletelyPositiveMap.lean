/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # Completely positive maps

A linear map `φ : A₁ →ₗ[ℂ] A₂` (where `A₁` and `A₂` are C⋆-algebras) is called
*completely positive (CP)* if `CStarMatrix.map (Fin k) (Fin k) φ` (i.e. applying `φ` to all
entries of a k × k matrix) is also positive for every `k : ℕ`.

This file defines completely positive maps and develops their basic API.

## Main results

+ `NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`: Non-unital star algebra
  homomorphisms are completely positive.

## Notation

+ `A₁ →CP A₂` denotes the type of CP maps from `A₁` to `A₂`. This notation is scoped to
  `CStarAlgebra`.

## Implementation notes

The morphism class `CompletelyPositiveMapClass` is designed to be part of the order hierarchy,
and only includes the order property; linearity is not mentioned at all. It is therefore meant
to be used in conjunction with `LinearMapClass`. This is meant to avoid mixing order and algebra
as much as possible.
-/

@[expose] public section

open scoped CStarAlgebra

/--
A linear map `φ : A₁ →ₗ[ℂ] A₂`  is called *completely positive (CP)* if
`CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all entries of a k × k matrix) is also
positive for every `k ∈ ℕ`.

Note that `Fin k` here is hardcoded to avoid having to quantify over types and introduce a new
universe parameter. See `CompletelyPositiveMap.map_cstarMatrix_nonneg` for a version of the
property that holds for matrices indexed by any finite type.
-/
/-
**CompletelyPositiveMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A₁ : Type u_1) →   (A₂ : Type u_2) →     [inst : NonUnitalCStarAlgebra A₁
] →       [inst_1 : NonUnitalCStarAlgebra A₂] →         [inst_2 : PartialOrder A
₁] →           [inst_3 : PartialOrder A₂] → [StarOrderedRing A₁] → [StarOrderedR
ing A₂] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map `φ : A₁ →ₗ[ℂ] A₂`  is called *completely positive (CP)* if
`CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all entries of a k × 
k matrix) is also
positive for every `k ∈ ℕ`.

Note that `Fin k` here is hardcoded to avoid having to quantify over types and i
ntroduce a new
universe parameter. See `CompletelyPositiveMap.map_cstarMatrix_nonneg` for a ver
sion of the
property that holds for matrices indexed by any finite type.
-/
structure CompletelyPositiveMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
      0 ≤ M.map toLinearMap

/--
A linear map `φ : A₁ →ₗ[ℂ] A₂`  is called *completely positive (CP)* if
`CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all entries of a k × k matrix) is also
positive for every `k ∈ ℕ`.

Note that `Fin k` here is hardcoded to avoid having to quantify over types and introduce a new
universe parameter. See `CompletelyPositiveMap.map_cstarMatrix_nonneg` for a version of the
property that holds for matrices indexed by any finite type.
-/
/-
**CompletelyPositiveMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (A₁ : Type u_2) →     (A₂ : Type u_3) →       [inst : N
onUnitalCStarAlgebra A₁] →         [inst_1 : NonUnitalCStarAlgebra A₂] →        
   [inst_2 : PartialOrder A₁] →             [inst_3 : PartialOrder A₂] → [StarOr
deredRing A₁] → [StarOrderedRing A₂] → [FunLike F A₁ A₂] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map `φ : A₁ →ₗ[ℂ] A₂`  is called *completely positive (CP)* if
`CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all entries of a k × 
k matrix) is also
positive for every `k ∈ ℕ`.

Note that `Fin k` here is hardcoded to avoid having to quantify over types and i
ntroduce a new
universe parameter. See `CompletelyPositiveMap.map_cstarMatrix_nonneg` for a ver
sion of the
property that holds for matrices indexed by any finite type.
-/
class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] where
  map_cstarMatrix_nonneg' (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

/-- Notation for a `CompletelyPositiveMap`. -/
scoped[CStarAlgebra] notation:25 A₁ " →CP " A₂:0 => CompletelyPositiveMap A₁ A₂

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
@[coe]
/-
**CompletelyPositiveMapClass.toCompletelyPositiveLinearMap** 是 Mathlib 中的一个定义，位于
命名空间 `CompletelyPositiveMapClass`。
形式化陈述：toCompletelyPositiveLinearMap [CompletelyPositiveMapClass F A₁ A₂] (f : F)
 : A₁ ->CP A₂
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyPositiveMapClass.map_cstarMatrix_nonneg'`：∀ {F : Type u_1} {A₁
 : Type u_2} {A₂ : Type u_3} {inst : NonUnitalCStarAlgebra A₁} {inst_1 : NonUnit
alCStarAlgebra A₂}   {inst_2 : PartialOr…

--- 原说明 ---
Reinterpret an element of a type of completely positive maps as a completely pos
itive linear
  map.
-/
def toCompletelyPositiveLinearMap [CompletelyPositiveMapClass F A₁ A₂] (f : F) : A₁ →CP A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' f }

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
map. -/
/-
**CompletelyPositiveMapClass.instCoeToCompletelyPositiveMap** 是 Mathlib 中的一个实例，位
于命名空间 `CompletelyPositiveMapClass`。
形式化陈述：instCoeToCompletelyPositiveMap [CompletelyPositiveMapClass F A₁ A₂] : CoeH
ead F (A₁ ->CP A₂) where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of completely positive maps as a completely pos
itive linear
map.
-/
instance instCoeToCompletelyPositiveMap [CompletelyPositiveMapClass F A₁ A₂] :
    CoeHead F (A₁ →CP A₂) where
  coe f := toCompletelyPositiveLinearMap f

set_option backward.isDefEq.respectTransparency false in
open CStarMatrix in
/-- Linear maps which are completely positive are order homomorphisms (i.e., positive maps). -/
/-
**CompletelyPositiveMapClass._root_.OrderHomClass.of_map_cstarMatrix_nonneg** 是 
Mathlib 中的一个引理，位于命名空间 `CompletelyPositiveMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear maps which are completely positive are order homomorphisms (i.e., positiv
e maps).
-/
lemma _root_.OrderHomClass.of_map_cstarMatrix_nonneg
    (h : ∀ (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map φ) :
    OrderHomClass F A₁ A₂ := .of_addMonoidHom <| by
  intro φ a ha
  simpa using! map_nonneg (toOneByOne (Fin 1) ℂ A₂).symm <|
    h φ 1 _ <| map_nonneg (toOneByOne (Fin 1) ℂ A₁) ha
/-
**CompletelyPositiveMapClass.** 是 Mathlib 中的一个实例，位于命名空间 `CompletelyPositiveMapCl
ass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompletelyPositiveMapClass F A₁ A₂] : OrderHomClass F A₁ A₂ :=
  .of_map_cstarMatrix_nonneg CompletelyPositiveMapClass.map_cstarMatrix_nonneg'

end CompletelyPositiveMapClass

namespace CompletelyPositiveMap

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]

/-
**CompletelyPositiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompletelyPositiveMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A₁ →CP A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h
/-
**CompletelyPositiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompletelyPositiveMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (A₁ →CP A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
/-
**CompletelyPositiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompletelyPositiveMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompletelyPositiveMapClass (A₁ →CP A₂) A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

open CStarMatrix in
/-
**CompletelyPositiveMap.map_cstarMatrix_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Comple
telyPositiveMap`。
形式化陈述：map_cstarMatrix_nonneg {n : Type*} [Fintype n] (φ : A₁ ->CP A₂) (M : CStar
Matrix n n A₁) (hM : 0 <= M) : 0 <= M.map φ
参数：φ : A₁ ->CP A₂；M : CStarMatrix n n A₁；hM : 0 <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyPositiveMap.instLinearMapClassComplex`：∀ {A₁ : Type u_1} {A₂ :
 Type u_2} [inst : NonUnitalCStarAlgebra A₁] [inst_1 : NonUnitalCStarAlgebra A₂]
   [inst_2 : PartialOrder A₁] [inst_3…
· 使用定理 `CompletelyPositiveMapClass.map_cstarMatrix_nonneg'`：∀ {F : Type u_1} {A₁
 : Type u_2} {A₂ : Type u_3} {inst : NonUnitalCStarAlgebra A₁} {inst_1 : NonUnit
alCStarAlgebra A₂}   {inst_2 : PartialOr…
· 使用定理 `CompletelyPositiveMap.instCompletelyPositiveMapClass`：∀ {A₁ : Type u_1} 
{A₂ : Type u_2} [inst : NonUnitalCStarAlgebra A₁] [inst_1 : NonUnitalCStarAlgebr
a A₂]   [inst_2 : PartialOrder A₁] [inst_3…
· 使用定理 `map_nonneg`：map_nonneg (ha : 0 <= a) : 0 <= f a
· 使用定理 `StarRingHomClass.instOrderHomClass`：∀ {F : Type u_3} {R : Type u_4} {S :
 Type u_5} [inst : NonUnitalSemiring R] [inst_1 : PartialOrder R]   [inst_2 : St
arRing R] [StarOrderedRi…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `instNonUnitalAlgHomClassOfNonUnitalAlgEquivClass`：∀ {F : Type u_1} {R : 
Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [inst_1 : NonUnitalNon
AssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarAlgHomClass.instNonUnitalStarRingHomClassOfStarHomClass`：∀ 
{F : Type u_1} {R : Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [i
nst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CStarMatrix.mapₗ_apply`：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} {
S : Type u_4} {A : Type u_5} {B : Type u_6} [inst : Semiring R]   [inst_1 : Semi
ring S] {σ :…
· 使用定理 `StarAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃⋆ₐ[R] B) : foral
l x, e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CStarMatrix.mapₗ_reindexₐ`：mapₗ_reindexₐ [Fintype m] [Fintype n] [Semiri
ng R] [AddCommMonoid A] [Mul A] [Module R A] [Star A] [AddCommMonoid B] [Mul B] 
[Module R B] [S…
-/
lemma map_cstarMatrix_nonneg {n : Type*} [Fintype n] (φ : A₁ →CP A₂) (M : CStarMatrix n n A₁)
    (hM : 0 ≤ M) : 0 ≤ M.map φ := by
  let k := Fintype.card n
  let e := Fintype.equivFinOfCardEq (rfl : Fintype.card n = k)
  have hmain : 0 ≤ (reindexₐ ℂ A₁ e M).mapₗ (φ : A₁ →ₗ[ℂ] A₂) := by
    simp only [mapₗ, LinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
    exact CompletelyPositiveMapClass.map_cstarMatrix_nonneg' _ k _ (map_nonneg _ hM)
  rw [← mapₗ_reindexₐ] at hmain
  simpa [reindexₐ_symm] using map_nonneg (reindexₐ ℂ A₂ e).symm hmain

end CompletelyPositiveMap

namespace NonUnitalStarAlgHomClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [NonUnitalAlgHomClass F ℂ A₁ A₂] [StarHomClass F A₁ A₂]

open CStarMatrix CFC in
/-- Non-unital star algebra homomorphisms are completely positive. -/
/-
**NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass** 是 Mathlib 中的一个实例，位于命
名空间 `NonUnitalStarAlgHomClass`。
形式化陈述：instCompletelyPositiveMapClass : CompletelyPositiveMapClass F A₁ A₂ where 
map_cstarMatrix_nonneg' φ k M hM
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nonneg`：map_nonneg (ha : 0 <= a) : 0 <= f a
· 使用定理 `StarRingHomClass.instOrderHomClass`：∀ {F : Type u_3} {R : Type u_4} {S :
 Type u_5} [inst : NonUnitalSemiring R] [inst_1 : PartialOrder R]   [inst_2 : St
arRing R] [StarOrderedRi…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHomClass.instNonUnitalStarRingHomClassOfStarHomClass`：∀ 
{F : Type u_1} {R : Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [i
nst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…

--- 原说明 ---
Non-unital star algebra homomorphisms are completely positive.
-/
instance instCompletelyPositiveMapClass : CompletelyPositiveMapClass F A₁ A₂ where
  map_cstarMatrix_nonneg' φ k M hM := by
    change 0 ≤ (mapₙₐ (φ : A₁ →⋆ₙₐ[ℂ] A₂)) M
    exact map_nonneg _ hM

end NonUnitalStarAlgHomClass

