/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.WithConv
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Convolution product on linear maps from a coalgebra to an algebra

This file constructs the ring and algebra structure on linear maps `C → A` where `C` is a
coalgebra and `A` an algebra, where multiplication is given by
`(f * g)(x) = ∑ f x₍₁₎ * g x₍₂₎` in Sweedler notation or
```
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.

## Implementation notes

Because there is a global multiplication instance on `Module.End R A` (defined as composition),
which is mathematically distinct from this product, we provide this instance on
`WithConv (C →ₗ[R] A)`.
-/

@[expose] public section

suppress_compilation

open Coalgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R S A B C ι : Type*} [CommSemiring R]

namespace LinearMap
section NonUnitalNonAssocSemiring
variable
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- Convolution product on linear maps from a coalgebra to an algebra. -/
/-
**LinearMap.convMul** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convMul : Mul (WithConv (C ->ₗ[R] A)) where mul f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convolution product on linear maps from a coalgebra to an algebra.
-/
instance convMul : Mul (WithConv (C →ₗ[R] A)) where
  mul f g := toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul)
/-
**LinearMap.convMul_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：convMul_def (f g : WithConv (C ->ₗ[R] A)) : f * g = toConv (mul' R A ∘ₗ ma
p f.ofConv g.ofConv ∘ₗ comul)
参数：f g : WithConv (C ->ₗ[R] A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convMul_def (f g : WithConv (C →ₗ[R] A)) :
    f * g = toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul) := rfl

@[simp]
/-
**LinearMap.convMul_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：convMul_apply (f g : WithConv (C ->ₗ[R] A)) (c : C) : (f * g) c = mul' R A
 (.map f.ofConv g.ofConv (comul c))
参数：f g : WithConv (C ->ₗ[R] A)；c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convMul_apply (f g : WithConv (C →ₗ[R] A)) (c : C) :
    (f * g) c = mul' R A (.map f.ofConv g.ofConv (comul c)) := rfl
/-
**LinearMap._root_.Coalgebra.Repr.convMul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Coalgebra.Repr.convMul_apply {a : C} (𝓡 : Coalgebra.Repr R a ι)
    (f g : WithConv (C →ₗ[R] A)) : (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [convMul_def, ← 𝓡.eq]

/-- Non-unital and non-associative convolution semiring structure on linear maps from a
coalgebra to a non-unital non-associative algebra. -/
/-
**LinearMap.convNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (WithConv (C ->ₗ
[R] A)) where left_distrib f g h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital and non-associative convolution semiring structure on linear maps fro
m a
coalgebra to a non-unital non-associative algebra.
-/
instance convNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (WithConv (C →ₗ[R] A)) where
  left_distrib f g h := by ext; simp [map_add_right]
  right_distrib f g h := by ext; simp [map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [DistribMulAction S A] [SMulCommClass R S A] [IsScalarTower S A A] :
    IsScalarTower S (WithConv (C →ₗ[R] A)) (WithConv (C →ₗ[R] A)) where
  smul_assoc s f g := by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, smul_mul_assoc]
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [DistribMulAction S A] [SMulCommClass R S A] [SMulCommClass S A A] :
    SMulCommClass S (WithConv (C →ₗ[R] A)) (WithConv (C →ₗ[R] A)) where
  smul_comm s f g := by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, mul_smul_comm]
/-
**LinearMap.toSpanSingleton_convMul_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} [inst : CommSemiring R] [inst_1 : NonUnita
lNonAssocSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass R A 
A] [inst_4 : IsScalarTower R A A] (x y : A),   WithConv.toConv (LinearMap.toSpan
Singleton R A x) * WithConv.toConv (LinearMap.toSpanSingleton R A y) =     WithC
onv.toConv (LinearMap.toSpanSingleton R A (x * y))
参数：x y : A；LinearMap.toSpanSingleton R A x；LinearMap.toSpanSingleton R A y；Linea
rMap.toSpanSingleton R A (x * y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toSpanSingleton_convMul_toSpanSingleton (x y : A) :
    toConv (toSpanSingleton R A x) * toConv (toSpanSingleton R A y) =
      toConv (toSpanSingleton R A (x * y)) := by ext; simp
/-
**LinearMap._root_.TensorProduct.map_convMul_map** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TensorProduct.map_convMul_map {D : Type*} [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R B] [NonUnitalNonAssocSemiring D] [Module R D] [SMulCommClass R D D]
    [IsScalarTower R D D] {f h : WithConv (C →ₗ[R] A)} {g k : WithConv (B →ₗ[R] D)} :
    toConv (f.ofConv ⊗ₘ g.ofConv) * toConv (h.ofConv ⊗ₘ k.ofConv) =
      toConv ((f * h).ofConv ⊗ₘ (g * k).ofConv) := by
  simp_rw [convMul_def, comul_def, mul'_tensor, comp_assoc, AlgebraTensorModule.map_eq,
    ← comp_assoc _ _ (tensorTensorTensorComm R _ _ _ _).toLinearMap]
  nth_rw 2 [← comp_assoc, comp_assoc]
  simp [AlgebraTensorModule.tensorTensorTensorComm_eq, ← tensorTensorTensorComm_comp_map,
    ← comp_assoc, map_comp]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- Non-unital and non-associative convolution ring structure on linear maps from a
coalgebra to a non-unital and non-associative algebra. -/
/-
**LinearMap.convNonUnitalNonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {A : Type u_3} →     {C : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : NonUnitalNonAssocRing A] →           [inst_2 : 
_root_.Module R A] →             [SMulCommClass R A A] →               [IsScalar
Tower R A A] →                 [inst_5 : AddCommMonoid C] →                   [i
nst_6 : _root_.Module R C] → [CoalgebraStruct R C] → NonUnitalNonAssocRing (With
Conv (C →ₗ[R] A))
参数：WithConv (C →ₗ[R] A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital and non-associative convolution ring structure on linear maps from a
coalgebra to a non-unital and non-associative algebra.
-/
instance convNonUnitalNonAssocRing : NonUnitalNonAssocRing (WithConv (C →ₗ[R] A)) where

end NonUnitalNonAssocRing

section NonUnitalSemiring
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-
**LinearMap.nonUnitalAlgHom_comp_convMul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Line
arMap`。
形式化陈述：nonUnitalAlgHom_comp_convMul_distrib [NonUnitalNonAssocSemiring B] [Module
 R B] [SMulCommClass R B B] [IsScalarTower R B B] (h : A ->ₙₐ[R] B) (f g : WithC
onv (C ->ₗ[R] A)) : (h : A ->ₗ[R] B).comp (f * g).ofConv = (toConv ((h : A ->ₗ[R
] B).comp f.ofConv) * toConv ((h : A ->ₗ[R] B).comp g.ofConv)).ofConv
参数：h : A ->ₙₐ[R] B；f g : WithConv (C ->ₗ[R] A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `NonUnitalAlgHom.comp_mul'`：comp_mul' (f : A ->ₙₐ[R] B) : (f : A ->ₗ[R] B
) ∘ₗ μ = μ[R] ∘ₗ (f otimesₘ f)
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nonUnitalAlgHom_comp_convMul_distrib
    [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    (h : A →ₙₐ[R] B) (f g : WithConv (C →ₗ[R] A)) :
    (h : A →ₗ[R] B).comp (f * g).ofConv =
      (toConv ((h : A →ₗ[R] B).comp f.ofConv) * toConv ((h : A →ₗ[R] B).comp g.ofConv)).ofConv := by
  simp [convMul_def, map_comp, ← comp_assoc, NonUnitalAlgHom.comp_mul']
/-
**LinearMap.convMul_comp_coalgHom_distrib** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：convMul_comp_coalgHom_distrib [AddCommMonoid B] [Module R B] [CoalgebraStr
uct R B] (f g : WithConv (C ->ₗ[R] A)) (h : B ->ₗc[R] C) : (f * g).ofConv.comp h
.toLinearMap = (toConv (f.ofConv.comp h.toLinearMap) * toConv (g.ofConv.comp h.t
oLinearMap)).ofConv
参数：f g : WithConv (C ->ₗ[R] A)；h : B ->ₗc[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `CoalgHomClass.map_comp_comul`：∀ {F : Type u_1} {R : outParam (Type u_2)}
 {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {
inst_1 : AddCommMo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convMul_comp_coalgHom_distrib [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]
    (f g : WithConv (C →ₗ[R] A)) (h : B →ₗc[R] C) :
    (f * g).ofConv.comp h.toLinearMap =
      (toConv (f.ofConv.comp h.toLinearMap) * toConv (g.ofConv.comp h.toLinearMap)).ofConv := by
  simp [convMul_def, map_comp, comp_assoc]

/-- Non-unital convolution semiring structure on linear maps from a coalgebra to a
non-unital algebra. -/
/-
**LinearMap.convNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convNonUnitalSemiring : NonUnitalSemiring (WithConv (C ->ₗ[R] A)) where mu
l_assoc f g h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital convolution semiring structure on linear maps from a coalgebra to a
non-unital algebra.
-/
instance convNonUnitalSemiring : NonUnitalSemiring (WithConv (C →ₗ[R] A)) where
  mul_assoc f g h := toConv_injective.eq_iff.mpr <| calc
    _ = (μ ∘ₗ rTensor _ μ) ∘ₗ (((f.ofConv ⊗ₘ g.ofConv) ⊗ₘ h.ofConv) ∘ₗ
        (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ := by
      ext; simp [comp_assoc, coassoc_symm, convMul_def]
    _ = (μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm) ∘ₗ
        (f.ofConv ⊗ₘ (g.ofConv ⊗ₘ h.ofConv)) ∘ₗ lTensor C δ ∘ₗ δ := by
      simp only [map_map_comp_assoc_symm_eq, comp_assoc]
    _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f.ofConv ⊗ₘ (g.ofConv ⊗ₘ h.ofConv)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
      congr 1
      ext
      simp [mul_assoc]
    _ = μ ∘ₗ (f.ofConv ⊗ₘ μ ∘ₗ (g.ofConv ⊗ₘ h.ofConv) ∘ₗ δ) ∘ₗ δ := by ext; simp

end NonUnitalSemiring

section NonUnitalRing
variable [NonUnitalRing A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [Coalgebra R C]

/-- Non-unital convolution ring structure on linear maps from a coalgebra to a
non-unital algebra. -/
/-
**LinearMap.convNonUnitalRing** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {A : Type u_3} →     {C : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : NonUnitalRing A] →           [inst_2 : AddCommM
onoid C] →             [inst_3 : _root_.Module R A] →               [SMulCommCla
ss R A A] →                 [IsScalarTower R A A] →                   [inst_6 : 
_root_.Module R C] → [Coalgebra R C] → NonUnitalRing (WithConv (C →ₗ[R] A))
参数：WithConv (C →ₗ[R] A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital convolution ring structure on linear maps from a coalgebra to a
non-unital algebra.
-/
instance convNonUnitalRing : NonUnitalRing (WithConv (C →ₗ[R] A)) where

end NonUnitalRing

section Semiring
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [AddCommMonoid C] [Module R C]

section CoalgebraStruct
variable [CoalgebraStruct R C]

/-
**LinearMap.algHom_comp_convMul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：algHom_comp_convMul_distrib (h : A ->ₐ B) (f g : WithConv (C ->ₗ[R] A)) : 
h.toLinearMap.comp (f * g).ofConv = (toConv (h.toLinearMap.comp f.ofConv) * toCo
nv (h.toLinearMap.comp g.ofConv)).ofConv
参数：h : A ->ₐ B；f g : WithConv (C ->ₗ[R] A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `AlgHom.comp_mul'`：comp_mul' (f : A ->ₐ B) : f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ
 (f.toLinearMap otimesₘ f.toLinearMap)
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algHom_comp_convMul_distrib (h : A →ₐ B) (f g : WithConv (C →ₗ[R] A)) :
    h.toLinearMap.comp (f * g).ofConv =
      (toConv (h.toLinearMap.comp f.ofConv) * toConv (h.toLinearMap.comp g.ofConv)).ofConv := by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

end CoalgebraStruct

variable [Coalgebra R C]

/-- Convolution unit on linear maps from a coalgebra to an algebra. -/
/-
**LinearMap.convOne** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convOne : One (WithConv (C ->ₗ[R] A)) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convolution unit on linear maps from a coalgebra to an algebra.
-/
instance convOne : One (WithConv (C →ₗ[R] A)) where one := toConv (Algebra.linearMap R A ∘ₗ counit)
/-
**LinearMap.convOne_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：convOne_def : (1 : WithConv (C ->ₗ[R] A)) = toConv (Algebra.linearMap R A 
∘ₗ counit)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convOne_def : (1 : WithConv (C →ₗ[R] A)) = toConv (Algebra.linearMap R A ∘ₗ counit) := rfl
/-
**LinearMap.convOne_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {C : Type u_5} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : AddCommMonoid C] [inst_4 :
 _root_.Module R C] [inst_5 : Coalgebra R C] (c : C),   (WithConv.ofConv 1) c = 
(algebraMap R A) (CoalgebraStruct.counit c)
参数：c : C；WithConv.ofConv 1；algebraMap R A；CoalgebraStruct.counit c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma convOne_apply (c : C) :
    (1 : WithConv (C →ₗ[R] A)) c = algebraMap R A (counit (R := R) c) := rfl

/-- Convolution semiring structure on linear maps from a coalgebra to an algebra. -/
/-
**LinearMap.convSemiring** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convSemiring : Semiring (WithConv (C ->ₗ[R] A)) where one_mul f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Convolution semiring structure on linear maps from a coalgebra to an algebra.
-/
instance convSemiring : Semiring (WithConv (C →ₗ[R] A)) where
  one_mul f := by ext; simp [convOne_def, ← map_comp_rTensor]
  mul_one f := by ext; simp [convOne_def, ← map_comp_lTensor]

/-- Convolution algebra structure on linear maps from a coalgebra to an algebra. -/
/-
**LinearMap.convAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convAlgebra [CommSemiring S] [Algebra S A] [SMulCommClass R S A] : Algebra
 S (WithConv (C ->ₗ[R] A))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convolution algebra structure on linear maps from a coalgebra to an algebra.
-/
instance convAlgebra [CommSemiring S] [Algebra S A] [SMulCommClass R S A] :
    Algebra S (WithConv (C →ₗ[R] A)) :=
  .ofModule smul_mul_assoc mul_smul_comm

@[simp]
/-
**LinearMap.convAlgebraMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：convAlgebraMap_apply [CommSemiring S] [Algebra S A] [SMulCommClass R S A] 
(s : S) (c : C) : algebraMap S (WithConv (C ->ₗ[R] A)) s c = s • algebraMap R A 
(counit c)
参数：s : S；c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convAlgebraMap_apply [CommSemiring S] [Algebra S A] [SMulCommClass R S A] (s : S) (c : C) :
    algebraMap S (WithConv (C →ₗ[R] A)) s c = s • algebraMap R A (counit c) := rfl

end Semiring

section CommSemiring
variable [CommSemiring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

/-- Commutative convolution semiring structure on linear maps from a cocommutative coalgebra to an
algebra. -/
/-
**LinearMap.convCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：convCommSemiring : CommSemiring (WithConv (C ->ₗ[R] A)) where mul_comm f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commutative convolution semiring structure on linear maps from a cocommutative c
oalgebra to an
algebra.
-/
instance convCommSemiring : CommSemiring (WithConv (C →ₗ[R] A)) where
  mul_comm f g := by ext x; rw [convMul_apply, ← comm_comul R x, map_comm, mul'_comm, convMul_apply]

end CommSemiring

section Ring
variable [Ring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]

/-- Convolution ring structure on linear maps from a coalgebra to an algebra. -/
/-
**LinearMap.convRing** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {A : Type u_3} →     {C : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : Ring A] →           [inst_2 : AddCommMonoid C] 
→             [inst_3 : Algebra R A] → [inst_4 : _root_.Module R C] → [Coalgebra
 R C] → Ring (WithConv (C →ₗ[R] A))
参数：WithConv (C →ₗ[R] A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convolution ring structure on linear maps from a coalgebra to an algebra.
-/
instance convRing : Ring (WithConv (C →ₗ[R] A)) where

end Ring

section CommRing
variable [CommRing A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C] [IsCocomm R C]

/-- Commutative convolution ring structure on linear maps from a cocommutative coalgebra to an
algebra. -/
/-
**LinearMap.convCommRing** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {A : Type u_3} →     {C : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : CommRing A] →           [inst_2 : AddCommMonoid
 C] →             [inst_3 : Algebra R A] →               [inst_4 : _root_.Module
 R C] →                 [inst_5 : Coalgebra R C] → [Coalgebra.IsCocomm R C] → Co
mmRing (WithConv (C →ₗ[R] A))
参数：WithConv (C →ₗ[R] A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commutative convolution ring structure on linear maps from a cocommutative coalg
ebra to an
algebra.
-/
instance convCommRing : CommRing (WithConv (C →ₗ[R] A)) where

end CommRing
end LinearMap

