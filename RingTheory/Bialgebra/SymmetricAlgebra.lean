/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on `SymmetricAlgebra R M`

`SymmetricAlgebra R M` is the cocommutative commutative `R`-bialgebra on `M`
in which each generator `ι x` is primitive: `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and
`ε(ι x) = 0`.
-/

public noncomputable section

namespace SymmetricAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

open scoped TensorProduct

/-
**SymmetricAlgebra.instBialgebra** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
形式化陈述：instBialgebra : Bialgebra R (SymmetricAlgebra R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBialgebra : Bialgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom
    (lift <| (TensorProduct.mk R _ _).flip 1 ∘ₗ ι R M + TensorProduct.mk R _ _ 1 ∘ₗ ι R M)
    algebraMapInv
    (by
      ext x
      simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel)
    (by ext x; simp [algebraMapInv_ι])
    (by ext x; simp [algebraMapInv_ι])

@[simp]
/-
**SymmetricAlgebra.comul_** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comul_ι (x : M) :
    Coalgebra.comul (R := R) (ι R M x) = ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x :=
  lift_ι_apply _ x

@[simp]
/-
**SymmetricAlgebra.counit_** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counit_ι (x : M) :
    Coalgebra.counit (R := R) (ι R M x) = 0 :=
  algebraMapInv_ι x
/-
**SymmetricAlgebra.instIsCocomm** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
形式化陈述：instIsCocomm : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where comm_comp
_comul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SymmetricAlgebra.algHom_ext`：algHom_ext {F G : SymmetricAlgebra R M ->ₐ[
R] A} (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M ->ₗ[R] A)) : F = G
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bialgebra.comulAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.co
mulAlgHom R A) a …
· 使用定理 `SymmetricAlgebra.comul_ι`：comul_ι (x : M) : Coalgebra.comul (R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `_private.Mathlib.RingTheory.Bialgebra.SymmetricAlgebra.0.SymmetricAlgebr
a.instIsCocomm._abel_1`：∀ (R : Type u_1) [inst : CommSemiring R] (M : Type u_2) 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M),   1 ⊗ₜ[R] (Symm
etri…
-/
instance instIsCocomm : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
          (SymmetricAlgebra R M)).toAlgHom.comp (Bialgebra.comulAlgHom R _) =
        Bialgebra.comulAlgHom R (SymmetricAlgebra R M) := by
      ext x
      simp
      abel
    exact congr(($h).toLinearMap)

@[simp]
/-
**SymmetricAlgebra.counitAlgHom_eq** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
形式化陈述：counitAlgHom_eq : Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebr
aMapInv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebraMapInv := rfl

end SymmetricAlgebra

