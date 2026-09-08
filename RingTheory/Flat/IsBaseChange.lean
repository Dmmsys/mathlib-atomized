/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Basic

/-!

# Lemmas about `IsBaseChange` under exact sequences

In this file, we show that if `S` is a flat `R`-algebra, taking kernels commutes with base change
of modules from `R` to `S`.

# Main Results

For `S` an `R`-algebra, consider the following commutative diagram with exact rows,
`M₁` `M₂` `M₃` `R`-modules, `N₁` `N₂` `N₃` `S`-modules,
`R`-linear maps `f₁` `f₂` `i₁` `i₂` `i₃` and `S`-linear maps `g₁` `g₂`.

M₁ --f₁--> M₂ --f₂--> M₃
|          |          |
i₁         i₂         i₃
|          |          |
v          v          v
N₁ --g₁--> N₂ --g₂--> N₃

* `IsBaseChange.of_left_exact` : If `S` is flat over `R`, `f₁` and `g₁` are injective,
  `i₂` and `i₃` is base change by `S`, then `i₁` is base change by `S`.

-/

@[expose] public section

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃)
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}

/-
**IsBaseChange.of_left_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBaseChange.of_left_exact (comm₁ : h₂.comp f = (f'.restrictScalars R).com
p h₁) (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂) [Module.Flat R S] (is
b₂ : IsBaseChange S h₂) (isb₃ : IsBaseChange S h₃) (exact₁ : Function.Exact f g)
 (inj₁ : Function.Injective f) (exact₂ : Function.Exact f' g') (inj₂ : Function.
Injective f') : IsBaseChange S h₁
参数：comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁；comm₂ : h₃.comp g = (g'.re
strictScalars R).comp h₂；isb₂ : IsBaseChange S h₂；isb₃ : IsBaseChange S h₃；exact
₁ : Function.Exact f g；inj₁ : Function.Injective f；exact₂ : Function.Exact f' g'
；inj₂ : Function.Injective f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `LinearMap.bijective_of_bijective_of_injective_of_left_exact`：bijective_o
f_bijective_of_injective_of_left_exact (hi₂ : Function.Bijective i₂) (hi₃ : Func
tion.Injective i₃) (hf₀ : Function.Injective f₁) …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.Flat.lTensor_exact`：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
-/
lemma IsBaseChange.of_left_exact (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂) [Module.Flat R S]
    (isb₂ : IsBaseChange S h₂) (isb₃ : IsBaseChange S h₃)
    (exact₁ : Function.Exact f g) (inj₁ : Function.Injective f)
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ := by
  simp only [IsBaseChange, IsTensorProduct] at isb₂ isb₃ ⊢
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exact₂ isb₂ isb₃.1 ?_ inj₂
  · ext s m
    simpa using congr(s • ($comm₁ m)).symm
  · ext s m
    simpa using congr(s • ($comm₂ m)).symm
  · exact Module.Flat.lTensor_exact S exact₁
  · exact Module.Flat.lTensor_preserves_injective_linearMap f inj₁
