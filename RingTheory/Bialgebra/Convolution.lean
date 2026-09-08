/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution product on bialgebra homs

This file constructs the ring structure on algebra homs `C → A` where `C` is a bialgebra and `A` an
algebra, and also the ring structure on bialgebra homs `C → A` where `C` and `A` are bialgebras.
Both multiplications are given by
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
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra TensorProduct WithConv

variable {R A B C : Type*} [CommSemiring R]

namespace AlgHom
variable [CommSemiring A] [CommSemiring B] [Semiring C] [Bialgebra R C] [Algebra R A]

/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (WithConv <| C →ₐ[R] A) where
  one := toConv <| (Algebra.ofId R A).comp <| counitAlgHom R C
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (WithConv <| C →ₐ[R] A) where
  mul f g := toConv <| .comp (lmul' R) <| .comp (map f.ofConv g.ofConv) <| comulAlgHom R C
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (WithConv <| C →ₐ[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩
/-
**AlgHom.convOne_def** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：convOne_def : 1 = toConv ((Algebra.ofId R A).comp (counitAlgHom R C))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convOne_def : 1 = toConv ((Algebra.ofId R A).comp (counitAlgHom R C)) := rfl
/-
**AlgHom.convMul_def** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：convMul_def (f g : WithConv <| C ->ₐ[R] A) : f * g = toConv (.comp (lmul' 
R) <| .comp (map f.ofConv g.ofConv) <| comulAlgHom R C)
参数：f g : WithConv <| C ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convMul_def (f g : WithConv <| C →ₐ[R] A) :
    f * g = toConv (.comp (lmul' R) <| .comp (map f.ofConv g.ofConv) <| comulAlgHom R C) := rfl
/-
**AlgHom.convPow_succ** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma convPow_succ (f : WithConv <| C →ₐ[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

@[simp]
/-
**AlgHom.convOne_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：convOne_apply (c : C) : (1 : WithConv <| C ->ₐ[R] A) c = algebraMap R A (c
ounit c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convOne_apply (c : C) : (1 : WithConv <| C →ₐ[R] A) c = algebraMap R A (counit c) := rfl
/-
**AlgHom.convMul_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：convMul_apply (f g : WithConv <| C ->ₐ[R] A) (c : C) : (f * g) c = lift f.
ofConv g.ofConv (fun _ _ => .all ..) (comul c)
参数：f g : WithConv <| C ->ₐ[R] A；c : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bialgebra.comulAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.co
mulAlgHom R A) a …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.TensorProduct.lift_comp_includeLeft`：lift_comp_includeLeft (f : 
A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) : (lift f g
 hfg).comp includeLeft = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.TensorProduct.lift_comp_includeRight`：lift_comp_includeRight (f 
: A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) : ((lift 
f g hfg).restrictScalars R).comp i…
-/
lemma convMul_apply (f g : WithConv <| C →ₐ[R] A) (c : C) :
    (f * g) c = lift f.ofConv g.ofConv (fun _ _ ↦ .all ..) (comul c) := by
  simp only [convMul_def, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [← comp_apply]
  congr 1
  ext <;> simp

@[simp]
/-
**AlgHom.toLinearMap_convOne** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_convOne : toConv (1 : WithConv <| C ->ₐ[R] A).ofConv.toLinearM
ap = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_convOne : toConv (1 : WithConv <| C →ₐ[R] A).ofConv.toLinearMap = 1 := rfl

@[simp]
/-
**AlgHom.toLinearMap_convMul** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_convMul (f g : WithConv <| C ->ₐ[R] A) : toConv (f * g).ofConv
.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap
参数：f g : WithConv <| C ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_convMul (f g : WithConv <| C →ₐ[R] A) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  rfl

@[simp]
/-
**AlgHom.toLinearMap_convPow** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {C : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Semiring C]   [inst_3 : Bialgebra R C] [inst_4 
: Algebra R A] (f : WithConv (C →ₐ[R] A)) (n : ℕ),   WithConv.toConv (f ^ n).ofC
onv.toLinearMap = WithConv.toConv f.ofConv.toLinearMap ^ n
参数：f : WithConv (C →ₐ[R] A)；n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_convPow (f : WithConv <| C →ₐ[R] A) :
    ∀ n : ℕ, toConv (f ^ n).ofConv.toLinearMap = toConv f.ofConv.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, toLinearMap_convMul, toLinearMap_convPow, pow_succ]
/-
**AlgHom.convMul_comp_bialgHom_distrib** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：convMul_comp_bialgHom_distrib [Bialgebra R B] (f g : WithConv <| C ->ₐ[R] 
A) (h : B ->ₐc[R] C) : AlgHom.comp (f * g).ofConv (h : B ->ₐ[R] C) = ofConv (toC
onv (f.ofConv.comp h) * toConv (g.ofConv.comp h))
参数：f g : WithConv <| C ->ₐ[R] A；h : B ->ₐc[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.map_comp`：map_comp (f₂ : C ->ₐ[S] E) (f₁ : A ->ₐ[S
] C) (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D) : map (f₂.comp f₁) (g₂.comp g₁) = (map 
f₂ g₂).comp (map f₁ …
· 使用定理 `BialgHom.map_comp_comulAlgHom`：map_comp_comulAlgHom (f : A ->ₐc[R] B) : 
(Algebra.TensorProduct.map f f).comp (comulAlgHom R A) = (comulAlgHom R B).comp 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convMul_comp_bialgHom_distrib [Bialgebra R B] (f g : WithConv <| C →ₐ[R] A) (h : B →ₐc[R] C) :
    AlgHom.comp (f * g).ofConv (h : B →ₐ[R] C) =
      ofConv (toConv (f.ofConv.comp h) * toConv (g.ofConv.comp h)) := by
  simp [convMul_def, comp_assoc, Algebra.TensorProduct.map_comp]
/-
**AlgHom.comp_convMul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：comp_convMul_distrib [Algebra R B] (h : A ->ₐ[R] B) (f g : WithConv <| C -
>ₐ[R] A) : h.comp (f * g).ofConv = ofConv (toConv (h.comp f.ofConv) * toConv (h.
comp g.ofConv))
参数：h : A ->ₐ[R] B；f g : WithConv <| C ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用引理 `WithConv.toConv_injective`：toConv_injective : Function.Injective (@toCon
v A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_toLinearMap`：comp_toLinearMap (f : A ->ₐ[R] B) (g : B ->ₐ[R]
 C) : (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithConv.ofConv_toConv`：ofConv_toConv (x : A) : ofConv (toConv x) = x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `AlgHom.toLinearMap_convMul`：toLinearMap_convMul (f g : WithConv <| C ->ₐ
[R] A) : toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toCon
v g.ofConv.toLin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LinearMap.algHom_comp_convMul_distrib`：algHom_comp_convMul_distrib (h : 
A ->ₐ B) (f g : WithConv (C ->ₗ[R] A)) : h.toLinearMap.comp (f * g).ofConv = (to
Conv (h.toLinearMap.comp f.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_convMul_distrib [Algebra R B] (h : A →ₐ[R] B) (f g : WithConv <| C →ₐ[R] A) :
    h.comp (f * g).ofConv = ofConv (toConv (h.comp f.ofConv) * toConv (h.comp g.ofConv)) := by
  apply toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.comp_toLinearMap, ← ofConv_toConv (f * g).ofConv.toLinearMap, toLinearMap_convMul]
  simp [LinearMap.algHom_comp_convMul_distrib, toLinearMap_convMul]
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (WithConv <| C →ₐ[R] A) := fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).monoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

variable [IsCocomm R C]
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (WithConv <| C →ₐ[R] A) := fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end AlgHom

namespace BialgHom
variable [CommSemiring A] [Semiring C] [Bialgebra R A] [Bialgebra R C]

/-
**BialgHom.** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (WithConv <| C →ₐc[R] A) where
  one := toConv <| (unitBialgHom R A).comp <| counitBialgHom R C
/-
**BialgHom.convOne_def** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：convOne_def : 1 = toConv ((unitBialgHom R A).comp (counitBialgHom R C))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convOne_def : 1 = toConv ((unitBialgHom R A).comp (counitBialgHom R C)) := rfl

@[simp]
/-
**BialgHom.convOne_apply** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：convOne_apply (c : C) : (1 : WithConv <| C ->ₐc[R] A) c = algebraMap R A (
counit c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convOne_apply (c : C) : (1 : WithConv <| C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

@[simp]
/-
**BialgHom.toLinearMap_convOne** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：toLinearMap_convOne : toConv (SemilinearMapClass.semilinearMap (1 : WithCo
nv <| C ->ₐc[R] A).ofConv) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
lemma toLinearMap_convOne :
    toConv (SemilinearMapClass.semilinearMap (1 : WithConv <| C →ₐc[R] A).ofConv) = 1 := rfl
/-
**BialgHom.toAlgHom_convOne** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {C : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Semiring C]   [inst_3 : Bialgebra R A] [inst_4 
: Bialgebra R C], WithConv.toConv ↑(WithConv.ofConv 1) = 1
参数：WithConv.ofConv 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAlgHom_convOne : toConv (1 : WithConv <| C →ₐc[R] A).ofConv.toAlgHom = 1 := rfl

variable [IsCocomm R C]
/-
**BialgHom.** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (WithConv <| C →ₐc[R] A) where
  mul f g := toConv <| .comp (mulBialgHom R A) <| .comp (map f.ofConv g.ofConv) <| comulBialgHom R C
/-
**BialgHom.** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (WithConv <| C →ₐc[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩
/-
**BialgHom.convMul_def** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：convMul_def (f g : WithConv <| C ->ₐc[R] A) : f * g = toConv (.comp (mulBi
algHom R A) <| .comp (map f.ofConv g.ofConv) <| comulBialgHom R C)
参数：f g : WithConv <| C ->ₐc[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convMul_def (f g : WithConv <| C →ₐc[R] A) :
    f * g =
      toConv (.comp (mulBialgHom R A) <| .comp (map f.ofConv g.ofConv) <| comulBialgHom R C) :=
  rfl
/-
**BialgHom.convPow_succ** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma convPow_succ (f : WithConv <| C →ₐc[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

-- TODO: Make simp once `SemilinearMapClass.semilinearMap` is not simp nf anymore.
-- @[simp]
/-
**BialgHom.toLinearMap_convMul** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：toLinearMap_convMul (f g : WithConv <| C ->ₐc[R] A) : toConv (f * g).ofCon
v.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap
参数：f g : WithConv <| C ->ₐc[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_convMul (f g : WithConv <| C →ₐc[R] A) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  rfl

@[simp]
/-
**BialgHom.toAlgHom_convMul** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：toAlgHom_convMul (f g : WithConv <| C ->ₐc[R] A) : toConv (f * g).ofConv.t
oAlgHom = toConv f.ofConv.toAlgHom * toConv g.ofConv.toAlgHom
参数：f g : WithConv <| C ->ₐc[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_convMul (f g : WithConv <| C →ₐc[R] A) :
    toConv (f * g).ofConv.toAlgHom = toConv f.ofConv.toAlgHom * toConv g.ofConv.toAlgHom :=
  rfl

-- TODO: Make simp once `SemilinearMapClass.semilinearMap` is not simp nf anymore.
-- @[simp]
/-
**BialgHom.toLinearMap_convPow** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {C : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Semiring C]   [inst_3 : Bialgebra R A] [inst_4 
: Bialgebra R C] [inst_5 : Coalgebra.IsCocomm R C] (f : WithConv (C →ₐc[R] A))  
 (n : ℕ), WithConv.toConv (f ^ n).ofConv.toLinearMap = WithConv.toConv f.ofConv.
toLinearMap ^ n
参数：f : WithConv (C →ₐc[R] A)；n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_convPow (f : WithConv <| C →ₐc[R] A) :
    ∀ n, toConv (f ^ n).ofConv.toLinearMap = toConv f.ofConv.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toLinearMap_convMul, toLinearMap_convPow]

@[simp]
/-
**BialgHom.toAlgHom_convPow** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {C : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Semiring C]   [inst_3 : Bialgebra R A] [inst_4 
: Bialgebra R C] [inst_5 : Coalgebra.IsCocomm R C] (f : WithConv (C →ₐc[R] A))  
 (n : ℕ), WithConv.toConv ↑(f ^ n).ofConv = WithConv.toConv ↑f.ofConv ^ n
参数：f : WithConv (C →ₐc[R] A)；n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_convPow (f : WithConv <| C →ₐc[R] A) :
    ∀ n, toConv (f ^ n).ofConv.toAlgHom = toConv f.ofConv.toAlgHom ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toAlgHom_convMul, toAlgHom_convPow]
/-
**BialgHom.** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (WithConv <| C →ₐc[R] A) := fast_instance%
  (toConv_injective.comp <| coe_linearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end BialgHom

