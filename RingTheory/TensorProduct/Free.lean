/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Results on bases of tensor products

In the file we construct a basis for the base change of a module to an algebra,
and deduce that `Module.Free` is stable under base change.

## Main declarations

- `Algebra.TensorProduct.basis`: given a basis of a module `M` over a commutative semiring `R`,
  and an `R`-algebra `A`, this provides a basis for `A ⊗[R] M` over `A`.
- `Algebra.TensorProduct.instFree`: if `M` is free, then so is `A ⊗[R] M`.

-/

@[expose] public section

assert_not_exists Cardinal

open Module
open scoped TensorProduct

namespace Algebra

namespace TensorProduct

variable {R A : Type*}

section Basis

universe uM uι
variable {M : Type uM} {ι : Type uι}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable (A) in
/-- Given an `R`-algebra `A` and an `R`-basis of `M`, this is an `R`-linear isomorphism
`A ⊗[R] M ≃ (ι →₀ A)` (which is in fact `A`-linear). -/
/-
**Algebra.TensorProduct.basisAux** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：basisAux : A otimes[R] M ≃ₗ[R] ι ->₀ A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}

--- 原说明 ---
Given an `R`-algebra `A` and an `R`-basis of `M`, this is an `R`-linear isomorph
ism
`A ⊗[R] M ≃ (ι →₀ A)` (which is in fact `A`-linear).
-/
noncomputable def basisAux : A ⊗[R] M ≃ₗ[R] ι →₀ A :=
  _root_.TensorProduct.congr (Finsupp.uniqueLinearEquiv R A ()).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))
/-
**Algebra.TensorProduct.basisAux_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorP
roduct`。
形式化陈述：basisAux_tmul (a : A) (m : M) : basisAux A b (a otimesₜ m) = a • Finsupp.m
apRange (algebraMap R A) (map_zero _) (b.repr m)
参数：a : A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Finsupp.uniqueLinearEquiv_symm_apply`：∀ (R : Type u_1) {α : Type u_3} (M
 : Type u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.M
odule R M] [inst_3 : Subsi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `finsuppTensorFinsupp_apply`：finsuppTensorFinsupp_apply (f : ι ->₀ M) (g 
: κ ->₀ N) (i : ι) (k : κ) : finsuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, 
k) = f i otimesₜ…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisAux_tmul (a : A) (m : M) :
    basisAux A b (a ⊗ₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) := by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]
/-
**Algebra.TensorProduct.basisAux_map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：basisAux_map_smul (a : A) (x : A otimes[R] M) : basisAux A b (a • x) = a •
 basisAux A b x
参数：a : A；x : A otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.TensorProduct.basisAux_tmul`：basisAux_tmul (a : A) (m : M) : bas
isAux A b (a otimesₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.
repr m)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem basisAux_map_smul (a : A) (x : A ⊗[R] M) : basisAux A b (a • x) = a • basisAux A b x :=
  TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]

variable (A) in
/-- Given an `R`-algebra `A`, this is the `A`-basis of `A ⊗[R] M` induced by an `R`-basis of `M`. -/
/-
**Algebra.TensorProduct.basis** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：basis : Basis ι A (A otimes[R] M) where repr
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.TensorProduct.basisAux_map_smul`：basisAux_map_smul (a : A) (x : 
A otimes[R] M) : basisAux A b (a • x) = a • basisAux A b x

--- 原说明 ---
Given an `R`-algebra `A`, this is the `A`-basis of `A ⊗[R] M` induced by an `R`-
basis of `M`.
-/
noncomputable def basis : Basis ι A (A ⊗[R] M) where
  repr := { basisAux A b with map_smul' := basisAux_map_smul b }

@[simp]
/-
**Algebra.TensorProduct.basis_repr_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tenso
rProduct`。
形式化陈述：basis_repr_tmul (a : A) (m : M) : (basis A b).repr (a otimesₜ m) = a • Fin
supp.mapRange (algebraMap R A) (map_zero _) (b.repr m)
参数：a : A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.basisAux_tmul`：basisAux_tmul (a : A) (m : M) : bas
isAux A b (a otimesₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.
repr m)
-/
theorem basis_repr_tmul (a : A) (m : M) :
    (basis A b).repr (a ⊗ₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) :=
  basisAux_tmul b _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.TensorProduct.basis_repr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：basis_repr_symm_apply (a : A) (i : ι) : (basis A b).repr.symm (Finsupp.sin
gle i a) = a otimesₜ b.repr.symm (Finsupp.single i 1)
参数：a : A；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `Algebra.TensorProduct.basisAux_map_smul`：basisAux_map_smul (a : A) (x : 
A otimes[R] M) : basisAux A b (a • x) = a • basisAux A b x
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `finsuppTensorFinsupp_symm_single`：finsuppTensorFinsupp_symm_single (i : 
ι × κ) (m : M) (n : N) : (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single
 i (m otimesₜ n)) = Fi…
· 使用定理 `Finsupp.uniqueLinearEquiv_apply`：∀ (R : Type u_1) {α : Type u_3} (M : Ty
pe u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.Module
 R M] [inst_3 : Subsi…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basis_repr_symm_apply (a : A) (i : ι) :
    (basis A b).repr.symm (Finsupp.single i a) = a ⊗ₜ b.repr.symm (Finsupp.single i 1) := by
  simp [basis, Equiv.uniqueProd_symm_apply, basisAux]

@[simp]
/-
**Algebra.TensorProduct.basis_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：basis_apply (i : ι) : basis A b i = 1 otimesₜ b i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.basis_repr_symm_apply`：basis_repr_symm_apply (a : 
A) (i : ι) : (basis A b).repr.symm (Finsupp.single i a) = a otimesₜ b.repr.symm 
(Finsupp.single i 1)
-/
theorem basis_apply (i : ι) : basis A b i = 1 ⊗ₜ b i := basis_repr_symm_apply b 1 i
/-
**Algebra.TensorProduct.basis_repr_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：basis_repr_symm_apply' (a : A) (i : ι) : a • basis A b i = a otimesₜ b i
参数：a : A；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.basis_apply`：basis_apply (i : ι) : basis A b i = 1
 otimesₜ b i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.TensorProduct.basis_repr_symm_apply`：basis_repr_symm_apply (a : 
A) (i : ι) : (basis A b).repr.symm (Finsupp.single i a) = a otimesₜ b.repr.symm 
(Finsupp.single i 1)
-/
theorem basis_repr_symm_apply' (a : A) (i : ι) : a • basis A b i = a ⊗ₜ b i := by
  simpa using basis_repr_symm_apply b a i

section baseChange

open LinearMap

variable [Fintype ι]
variable {ι' N : Type*} [Fintype ι'] [DecidableEq ι'] [AddCommMonoid N] [Module R N]
variable (A : Type*) [CommSemiring A] [Algebra R A]

/-
**Algebra.TensorProduct._root_.Module.Basis.baseChange_linearMap** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.Basis.baseChange_linearMap (b : Basis ι R M) (b' : Basis ι' R N) (ij : ι × ι') :
    baseChange A (b'.linearMap b ij) = (basis A b').linearMap (basis A b) ij := by
  apply (basis A b').ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [Basis.linearMap_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

variable [DecidableEq ι]
/-
**Algebra.TensorProduct._root_.Module.Basis.baseChange_end** 是 Mathlib 中的一个引理，位于
命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.Basis.baseChange_end (b : Basis ι R M) (ij : ι × ι) :
    baseChange A (b.end ij) = (basis A b).end ij :=
  b.baseChange_linearMap A b ij

end baseChange

end Basis

/-
**Algebra.TensorProduct.instFree** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：instFree (R A M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [
Module.Free R M] [CommSemiring A] [Algebra R A] : Module.Free A (A otimes[R] M)
参数：R A M : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instFree (R A M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
    [CommSemiring A] [Algebra R A] :
    Module.Free A (A ⊗[R] M) :=
  Module.Free.of_basis <| Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)

end TensorProduct

end Algebra

namespace LinearMap

open Algebra.TensorProduct

variable {R M₁ M₂ ι ι₂ : Type*} (A : Type*)
  [Fintype ι] [Finite ι₂] [DecidableEq ι]
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

@[simp]
/-
**LinearMap.toMatrix_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMatrix_baseChange (f : M₁ ->ₗ[R] M₂) (b₁ : Basis ι R M₁) (b₂ : Basis ι₂ 
R M₂) : toMatrix (basis A b₁) (basis A b₂) (f.baseChange A) = (toMatrix b₁ b₂ f)
.map (algebraMap R A)
参数：f : M₁ ->ₗ[R] M₂；b₁ : Basis ι R M₁；b₂ : Basis ι₂ R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.basis_apply`：basis_apply (i : ι) : basis A b i = 1
 otimesₜ b i
· 使用定理 `Algebra.TensorProduct.basis_repr_tmul`：basis_repr_tmul (a : A) (m : M) :
 (basis A b).repr (a otimesₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zer
o _) (b.repr m)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMatrix_baseChange (f : M₁ →ₗ[R] M₂) (b₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂) :
    toMatrix (basis A b₁) (basis A b₂) (f.baseChange A) =
    (toMatrix b₁ b₂ f).map (algebraMap R A) := by
  ext; simp [toMatrix_apply]

end LinearMap

