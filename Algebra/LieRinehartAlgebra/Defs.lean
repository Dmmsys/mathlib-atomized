/-
Copyright (c) 2025 Sven Holtrop and Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Holtrop, Leonid Ryvkin
-/
module

public import Mathlib.RingTheory.Derivation.Lie

/-!
# Lie-Rinehart algebras

This file defines Lie-Rinehart algebras and their morphisms. It also shows that the derivations of
a commutative algebra over a commutative Ring form such a Lie-Rinehart algebra.
Lie-Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. The typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

* [Rinehart, G. S., Differential forms on general commutative algebras. Zbl 0113.26204
  Trans. Am. Math. Soc. 108, 195-222 (1963).][rinehart_1963]

-/

@[expose] public section

/-- A Lie-Rinehart ring is a pair consisting of a commutative ring `A` and a Lie ring `L` such that
`A` and `L` are each a module over the other, satisfying compatibility conditions. -/
/-
**LieRinehartRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) →   (L : Type u_2) → [inst : CommRing A] → [inst_1 : LieRin
g L] → [_root_.Module A L] → [LieRingModule L A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie-Rinehart ring is a pair consisting of a commutative ring `A` and a Lie rin
g `L` such that
`A` and `L` are each a module over the other, satisfying compatibility condition
s.
-/
class LieRinehartRing (A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] : Prop where
  lie_smul_eq_mul' (a b : A) (x : L) : ⁅a • x, b⁆ = a * ⁅x, b⁆
  leibniz_mul_right' (x : L) (a b : A) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
  leibniz_smul_right' (x y : L) (a : A) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

/-- A Lie-Rinehart algebra with coefficients in a commutative ring `R`, is a pair consisting of a
commutative `R`-algebra `A` and a Lie algebra `L` with coefficients in `R`, such that `A` and `L`
are each a module over the other, satisfying compatibility conditions.

As shown below, this data determines a linear map `L → Derivation R A A` satisfying a Leibniz-like
compatibility condition. This could even be taken as a definition, however the definition here has
the advantage of being `Prop`-valued, thus mitigating potential diamonds. -/
/-
**LieRinehartAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (L : Type u_3) →       [inst : Com
mRing A] →         [inst_1 : LieRing L] →           [inst_2 : _root_.Module A L]
 →             [inst_3 : LieRingModule L A] →               [LieRinehartRing A L
] → [inst_5 : CommRing R] → [Algebra R A] → [LieAlgebra R L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie-Rinehart algebra with coefficients in a commutative ring `R`, is a pair co
nsisting of a
commutative `R`-algebra `A` and a Lie algebra `L` with coefficients in `R`, such
 that `A` and `L`
are each a module over the other, satisfying compatibility conditions.

As shown below, this data determines a linear map `L → Derivation R A A` satisfy
ing a Leibniz-like
compatibility condition. This could even be taken as a definition, however the d
efinition here has
the advantage of being `Prop`-valued, thus mitigating potential diamonds.
-/
class LieRinehartAlgebra (R A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [CommRing R] [Algebra R A] [LieAlgebra R L] : Prop extends
    IsScalarTower R A L, LieModule R L A

variable {R A₁ L₁ A₂ L₂ A₃ L₃ : Type*} [CommRing R]
  [CommRing A₁] [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁]
  [CommRing A₂] [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂]
  [CommRing A₃] [LieRing L₃] [Module A₃ L₃] [LieRingModule L₃ A₃]
  [Algebra R A₁] [LieAlgebra R L₁] [Algebra R A₂] [LieAlgebra R L₂]
  [Algebra R A₃] [LieAlgebra R L₃]
  {σ₁₂ : A₁ →ₐ[R] A₂} {σ₂₃ : A₂ →ₐ[R] A₃}
/-
**LieRinehartRing.lie_smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartRing`。
形式化陈述：∀ {A₁ : Type u_2} {L₁ : Type u_3} [inst : CommRing A₁] [inst_1 : LieRing L
₁] [inst_2 : _root_.Module A₁ L₁]   [inst_3 : LieRingModule L₁ A₁] [LieRinehartR
ing A₁ L₁] (a b : A₁) (x : L₁), ⁅a • x, b⁆ = a * ⁅x, b⁆
参数：a b : A₁；x : L₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartRing.lie_smul_eq_mul'`：∀ {A : Type u_1} {L : Type u_2} {inst 
: CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}   {inst_3 : LieR
ingModule L A} [self :…
-/
@[simp] lemma LieRinehartRing.lie_smul_eq_mul [LieRinehartRing A₁ L₁] (a b : A₁) (x : L₁) :
  ⁅a • x, b⁆ = a * ⁅x, b⁆ := LieRinehartRing.lie_smul_eq_mul' a b x
/-
**LieRinehartRing.leibniz_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartRing`。
形式化陈述：∀ {A₁ : Type u_2} {L₁ : Type u_3} [inst : CommRing A₁] [inst_1 : LieRing L
₁] [inst_2 : _root_.Module A₁ L₁]   [inst_3 : LieRingModule L₁ A₁] [LieRinehartR
ing A₁ L₁] (x : L₁) (a b : A₁), ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
参数：x : L₁；a b : A₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartRing.leibniz_mul_right'`：∀ {A : Type u_1} {L : Type u_2} {ins
t : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}   {inst_3 : Li
eRingModule L A} [self :…
-/
@[simp] lemma LieRinehartRing.leibniz_mul_right [LieRinehartRing A₁ L₁] (x : L₁) (a b : A₁) :
  ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b := LieRinehartRing.leibniz_mul_right' x a b
/-
**LieRinehartRing.leibniz_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartRing`
。
形式化陈述：∀ {A₁ : Type u_2} {L₁ : Type u_3} [inst : CommRing A₁] [inst_1 : LieRing L
₁] [inst_2 : _root_.Module A₁ L₁]   [inst_3 : LieRingModule L₁ A₁] [LieRinehartR
ing A₁ L₁] (x y : L₁) (a : A₁), ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y
参数：x y : L₁；a : A₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartRing.leibniz_smul_right'`：∀ {A : Type u_1} {L : Type u_2} {in
st : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}   {inst_3 : L
ieRingModule L A} [self :…
-/
@[simp] lemma LieRinehartRing.leibniz_smul_right [LieRinehartRing A₁ L₁] (x y : L₁) (a : A₁) :
  ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y := LieRinehartRing.leibniz_smul_right' x y a
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRinehartRing A₁ (Derivation R A₁ A₁) where
  lie_smul_eq_mul' _ _ _ := rfl
  leibniz_mul_right' _ _ _ := by simp; ring
  leibniz_smul_right' _ _ _ := by ext; simp [Derivation.commutator_apply]; ring

/-- The derivations of a commutative Algebra themselves form a LieRinehart-Algebra. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivations of a commutative Algebra themselves form a LieRinehart-Algebra.
-/
instance : LieRinehartAlgebra R A₁ (Derivation R A₁ A₁) where

namespace LieRinehartAlgebra

/-- A morphism of Lie-Rinehart algebras, from `(A₁, L₁)` to `(A₂, L₂)`, consists of a pair of maps
`(σ, F)` where `σ : A₁ → A₂` is a morphism of algebras and `F` is a morphism of Lie algebras, which
respect the module structures.

Here we define the type of such morphisms with fixed `σ` (which can be regarded as functions
`L₁ → L₂`). In the future it may be useful to define the type of such morphisms with fixed `F`
(which can be regarded as functions `A₁ → A₂`) and the type of all such morphisms (which can be
regarded as functions `A₁ × L₁ → A₂ × L₂`). -/
/-
**LieRinehartAlgebra.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieRinehartAlgebra`。
形式化陈述：{R : Type u_1} →   {A₁ : Type u_2} →     {A₂ : Type u_4} →       [inst : C
ommRing R] →         [inst_1 : CommRing A₁] →           [inst_2 : CommRing A₂] →
             [inst_3 : Algebra R A₁] →               [inst_4 : Algebra R A₂] →  
               (A₁ →ₐ[R] A₂) →                   (L₁ : Type u_8) →              
       (L₂ : Type u_9) →                       [inst_5 : LieRing L₁] →          
               [_root_.Module A₁ L₁] →                           [LieRingModule 
L₁ A₁] →                             [LieAlgebra R L₁] →                        
       [inst_9 : LieRing L₂] →                                 [_root_.Module A₂
 L₂] → [LieRingModule L₂ A₂] → [LieAlgebra R L₂] → Type (max u_8 u_9)
参数：A₁ →ₐ[R] A₂；L₁ : Type u_8；L₂ : Type u_9；max u_8 u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie-Rinehart algebras, from `(A₁, L₁)` to `(A₂, L₂)`, consists of 
a pair of maps
`(σ, F)` where `σ : A₁ → A₂` is a morphism of algebras and `F` is a morphism of 
Lie algebras, which
respect the module structures.

Here we define the type of such morphisms with fixed `σ` (which can be regarded 
as functions
`L₁ → L₂`). In the future it may be useful to define the type of such morphisms 
with fixed `F`
(which can be regarded as functions `A₁ → A₂`) and the type of all such morphism
s (which can be
regarded as functions `A₁ × L₁ → A₂ × L₂`).
-/
structure Hom (σ : A₁ →ₐ[R] A₂) (L₁ L₂ : Type*)
    [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁] [LieAlgebra R L₁]
    [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂] [LieAlgebra R L₂]
    extends L₁ →ₗ⁅R⁆ L₂ where
  map_smul_apply' (a : A₁) (x : L₁) : toLieHom (a • x) = σ a • toLieHom x
  apply_lie' (a : A₁) (x : L₁) : σ ⁅x, a⁆ = ⁅toLieHom x, σ a⁆

@[inherit_doc]
scoped notation:25 L " →ₗ⁅" σ:25 "⁆ " L₂:0 => LieRinehartAlgebra.Hom σ L L₂

namespace Hom

/-
**LieRinehartAlgebra.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartAlgebra.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (L₁ →ₗ⁅σ₁₂⁆ L₂) (fun _ => L₁ → L₂) := ⟨fun f => f.toLieHom⟩

/-- This is `LieRinehartAlgebra.Hom.map_smul_apply'` restated using the coercion to function rather
than `LieRinehartAlgebra.Hom.toLieHom`. -/
/-
**LieRinehartAlgebra.Hom.map_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieRinehartAl
gebra.Hom`。
形式化陈述：map_smul_apply (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) : f (a • x) = σ₁₂ a 
• f x
参数：f : L₁ ->ₗ⁅σ₁₂⁆ L₂；a : A₁；x : L₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartAlgebra.Hom.map_smul_apply'`：∀ {R : Type u_1} {A₁ : Type u_2}
 {A₂ : Type u_4} [inst : CommRing R] [inst_1 : CommRing A₁] [inst_2 : CommRing A
₂]   [inst_3 : Algebra R A₁]…

--- 原说明 ---
This is `LieRinehartAlgebra.Hom.map_smul_apply'` restated using the coercion to 
function rather
than `LieRinehartAlgebra.Hom.toLieHom`.
-/
lemma map_smul_apply (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    f (a • x) = σ₁₂ a • f x :=
  f.map_smul_apply' a x

/-- This is `LieRinehartAlgebra.Hom.apply_lie'` restated using the coercion to function rather
than `LieRinehartAlgebra.Hom.toLieHom`. -/
/-
**LieRinehartAlgebra.Hom.apply_lie** 是 Mathlib 中的一个引理，位于命名空间 `LieRinehartAlgebra
.Hom`。
形式化陈述：apply_lie (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) : σ₁₂ ⁅x, a⁆ = ⁅f x, σ₁₂ 
a⁆
参数：f : L₁ ->ₗ⁅σ₁₂⁆ L₂；a : A₁；x : L₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartAlgebra.Hom.apply_lie'`：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ 
: Type u_4} [inst : CommRing R] [inst_1 : CommRing A₁] [inst_2 : CommRing A₂]   
[inst_3 : Algebra R A₁]…

--- 原说明 ---
This is `LieRinehartAlgebra.Hom.apply_lie'` restated using the coercion to funct
ion rather
than `LieRinehartAlgebra.Hom.toLieHom`.
-/
lemma apply_lie (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    σ₁₂ ⁅x, a⁆ = ⁅f x, σ₁₂ a⁆ :=
  f.apply_lie' a x

/-- A morphism of Lie-Rinehart algebras as a semilinear map. -/
/-
**LieRinehartAlgebra.Hom.toLinearMap'** 是 Mathlib 中的一个定义，位于命名空间 `LieRinehartAlge
bra.Hom`。
形式化陈述：toLinearMap' (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) : L₁ ->ₛₗ[σ₁₂.toRingHom] L₂ where toFun
参数：f : L₁ ->ₗ⁅σ₁₂⁆ L₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LieRinehartAlgebra.Hom.map_smul_apply`：map_smul_apply (f : L₁ ->ₗ⁅σ₁₂⁆ L
₂) (a : A₁) (x : L₁) : f (a • x) = σ₁₂ a • f x

--- 原说明 ---
A morphism of Lie-Rinehart algebras as a semilinear map.
-/
def toLinearMap' (f : L₁ →ₗ⁅σ₁₂⁆ L₂) : L₁ →ₛₗ[σ₁₂.toRingHom] L₂ where
  toFun := f
  map_add' := f.map_add'
  map_smul' := f.map_smul_apply
/-
**LieRinehartAlgebra.Hom.toLinearMap'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieRineha
rtAlgebra.Hom`。
形式化陈述：∀ {R : Type u_1} {A₁ : Type u_2} {L₁ : Type u_3} {A₂ : Type u_4} {L₂ : Typ
e u_5} [inst : CommRing R]   [inst_1 : CommRing A₁] [inst_2 : LieRing L₁] [inst_
3 : _root_.Module A₁ L₁] [inst_4 : LieRingModule L₁ A₁]   [inst_5 : CommRing A₂]
 [inst_6 : LieRing L₂] [inst_7 : _root_.Module A₂ L₂] [inst_8 : LieRingModule L₂
 A₂]   [inst_9 : Algebra R A₁] [inst_10 : LieAlgebra R L₁] [inst_11 : Algebra R 
A₂] [inst_12 : LieAlgebra R L₂]   {σ₁₂ : A₁ →ₐ[R] A₂} (f : LieRinehartAlgebra.Ho
m σ₁₂ L₁ L₂) (x : L₁), f.toLinearMap' x = f.toLieHom x
参数：f : LieRinehartAlgebra.Hom σ₁₂ L₁ L₂；x : L₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap'_apply (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (x : L₁) : f.toLinearMap' x = f x := rfl

/-- The composition of Lie-Rinehart algebra morphisms is again a morphism. -/
/-
**LieRinehartAlgebra.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `LieRinehartAlgebra.Hom`
。
形式化陈述：{R : Type u_1} →   {A₁ : Type u_2} →     {L₁ : Type u_3} →       {A₂ : Typ
e u_4} →         {L₂ : Type u_5} →           {A₃ : Type u_6} →             {L₃ :
 Type u_7} →               [inst : CommRing R] →                 [inst_1 : CommR
ing A₁] →                   [inst_2 : LieRing L₁] →                     [inst_3 
: _root_.Module A₁ L₁] →                       [inst_4 : LieRingModule L₁ A₁] → 
                        [inst_5 : CommRing A₂] →                           [inst
_6 : LieRing L₂] →                             [inst_7 : _root_.Module A₂ L₂] → 
                              [inst_8 : LieRingModule L₂ A₂] →                  
               [inst_9 : CommRing A₃] →                                   [inst_
10 : LieRing L₃] →                                     [inst_11 : _root_.Module 
A₃ L₃] →                                       [inst_12 : LieRingModule L₃ A₃] →
                                         [inst_13 : Algebra R A₁] →             
                              [inst_14 : LieAlgebra R L₁] →                     
                        [inst_15 : Algebra R A₂] →                              
                 [inst_16 : LieAlgebra R L₂] →                                  
               [inst_17 : Algebra R A₃] →                                       
            [inst_18 : LieAlgebra R L₃] →                                       
              {σ₁₂ : A₁ →ₐ[R] A₂} →                                             
          {σ₂₃ : A₂ →ₐ[R] A₃} →                                                 
        LieRinehartAlgebra.Hom σ₁₂ L₁ L₂ →                                      
                     LieRinehartAlgebra.Hom σ₂₃ L₂ L₃ →                         
                                    LieRinehartAlgebra.Hom (σ₂₃.comp σ₁₂) L₁ L₃
参数：σ₂₃.comp σ₁₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of Lie-Rinehart algebra morphisms is again a morphism.
-/
protected def comp (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (g : L₂ →ₗ⁅σ₂₃⁆ L₃) : L₁ →ₗ⁅σ₂₃.comp σ₁₂⁆ L₃ where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_smul_apply' _ _ := by simp [Hom.map_smul_apply]
  apply_lie' _ _ := by simp [f.apply_lie, g.apply_lie]

/-- The identity morphism of a Lie-Rinehart algebra over the identity algebra homomorphism of the
underlying algebra. -/
/-
**LieRinehartAlgebra.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `LieRinehartAlgebra.Hom`。
形式化陈述：{R : Type u_1} →   {A₁ : Type u_2} →     {L₁ : Type u_3} →       [inst : C
ommRing R] →         [inst_1 : CommRing A₁] →           [inst_2 : LieRing L₁] → 
            [inst_3 : _root_.Module A₁ L₁] →               [inst_4 : LieRingModu
le L₁ A₁] →                 [inst_5 : Algebra R A₁] → [inst_6 : LieAlgebra R L₁]
 → LieRinehartAlgebra.Hom (AlgHom.id R A₁) L₁ L₁
参数：AlgHom.id R A₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of a Lie-Rinehart algebra over the identity algebra homomo
rphism of the
underlying algebra.
-/
protected def id : L₁ →ₗ⁅AlgHom.id R A₁⁆ L₁ where
  __ := LieHom.id
  map_smul_apply' _ _ := by simp
  apply_lie' _ _ := by simp

end Hom

variable [LieRinehartRing A₁ L₁] [LieRinehartAlgebra R A₁ L₁]

variable (R A₁ L₁) in
/-- The anchor of a given Lie-Rinehart algebra `L` over `A` interpreted as a Lie-Rinehart morphism
to the module of derivations of `A`. -/
/-
**LieRinehartAlgebra.anchor** 是 Mathlib 中的一个定义，位于命名空间 `LieRinehartAlgebra`。
形式化陈述：anchor : L₁ ->ₗ⁅AlgHom.id R A₁⁆ Derivation R A₁ A₁ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartAlgebra.toLieModule`：∀ {R : Type u_1} {A : Type u_2} {L : Typ
e u_3} {inst : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}   {
inst_3 : LieRingModu…

--- 原说明 ---
The anchor of a given Lie-Rinehart algebra `L` over `A` interpreted as a Lie-Rin
ehart morphism
to the module of derivations of `A`.
-/
def anchor : L₁ →ₗ⁅AlgHom.id R A₁⁆ Derivation R A₁ A₁ where
  toFun x := .mk' (LieModule.toEnd R L₁ A₁ x) fun a b ↦ by
    simp [mul_comm b]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by ext; simp [Derivation.commutator_apply]
  map_smul_apply' _ _ := by ext; simp
  apply_lie' _ _ := by simp
/-
**LieRinehartAlgebra.anchor_derivation** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartAlg
ebra`。
形式化陈述：∀ {R : Type u_1} {A₁ : Type u_2} [inst : CommRing R] [inst_1 : CommRing A₁
] [inst_2 : Algebra R A₁],   LieRinehartAlgebra.anchor R A₁ (Derivation R A₁ A₁)
 = LieRinehartAlgebra.Hom.id
参数：Derivation R A₁ A₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instLieRinehartRingDerivation`：∀ {R : Type u_1} {A₁ : Type u_2} [inst : 
CommRing R] [inst_1 : CommRing A₁] [inst_2 : Algebra R A₁],   LieRinehartRing A₁
 (Derivation R A₁ A…
· 使用定理 `instLieRinehartAlgebraDerivation`：∀ {R : Type u_1} {A₁ : Type u_2} [inst
 : CommRing R] [inst_1 : CommRing A₁] [inst_2 : Algebra R A₁],   LieRinehartAlge
bra R A₁ (Derivation R…
-/
@[simp] lemma anchor_derivation : anchor R A₁ (Derivation R A₁ A₁) = Hom.id := rfl
/-
**LieRinehartAlgebra.anchor_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartAlgebra`
。
形式化陈述：∀ {R : Type u_1} {A₁ : Type u_2} {L₁ : Type u_3} [inst : CommRing R] [inst
_1 : CommRing A₁] [inst_2 : LieRing L₁]   [inst_3 : _root_.Module A₁ L₁] [inst_4
 : LieRingModule L₁ A₁] [inst_5 : Algebra R A₁] [inst_6 : LieAlgebra R L₁]   [in
st_7 : LieRinehartRing A₁ L₁] [inst_8 : LieRinehartAlgebra R A₁ L₁] (l : L₁) (a 
: A₁),   ((LieRinehartAlgebra.anchor R A₁ L₁).toLieHom l) a = ⁅l, a⁆
参数：l : L₁；a : A₁；(LieRinehartAlgebra.anchor R A₁ L₁).toLieHom l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma anchor_apply (l : L₁) (a : A₁) :
  (LieRinehartAlgebra.anchor R A₁ L₁ l) a = ⁅l, a⁆ := rfl

end LieRinehartAlgebra

