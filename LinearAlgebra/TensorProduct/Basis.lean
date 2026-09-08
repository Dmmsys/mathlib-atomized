/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Bases and dimensionality of tensor products of modules

This file defines various bases on the tensor product of modules,
and shows that the tensor product of free modules is again free.
-/

@[expose] public section


noncomputable section

open LinearMap Module Set Submodule

open scoped TensorProduct

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

namespace Module.Basis

/-- If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`. -/
/-
**Module.Basis.tensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：tensorProduct (b : Basis ι S M) (c : Basis κ R N) : Basis (ι × κ) S (M oti
mes[R] N)
参数：b : Basis ι S M；c : Basis κ R N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι 
× κ → M ⊗ N`.
-/
def tensorProduct (b : Basis ι S M) (c : Basis κ R N) :
    Basis (ι × κ) S (M ⊗[R] N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R S _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]
/-
**Module.Basis.tensorProduct_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：tensorProduct_apply (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ) : 
tensorProduct b c (i, j) = b i otimesₜ c j
参数：b : Basis ι S M；c : Basis κ R N；i : ι；j : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_basisSingleOne`：coe_basisSingleOne : (Finsupp.basisSingleOne
 : ι -> ι ->₀ R) = fun i => Finsupp.single i 1
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `finsuppTensorFinsupp_symm_single`：finsuppTensorFinsupp_symm_single (i : 
ι × κ) (m : M) (n : N) : (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single
 i (m otimesₜ n)) = Fi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorProduct_apply (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ) :
    tensorProduct b c (i, j) = b i ⊗ₜ c j := by
  simp [tensorProduct]
/-
**Module.Basis.tensorProduct_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：tensorProduct_apply' (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ) : ten
sorProduct b c i = b i.1 otimesₜ c i.2
参数：b : Basis ι S M；c : Basis κ R N；i : ι × κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_basisSingleOne`：coe_basisSingleOne : (Finsupp.basisSingleOne
 : ι -> ι ->₀ R) = fun i => Finsupp.single i 1
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `finsuppTensorFinsupp_symm_single`：finsuppTensorFinsupp_symm_single (i : 
ι × κ) (m : M) (n : N) : (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single
 i (m otimesₜ n)) = Fi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorProduct_apply' (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ) :
    tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by
  simp [tensorProduct]

@[simp]
/-
**Module.Basis.tensorProduct_repr_tmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.B
asis`。
形式化陈述：tensorProduct_repr_tmul_apply (b : Basis ι S M) (c : Basis κ R N) (m : M) 
(n : N) (i : ι) (j : κ) : (tensorProduct b c).repr (m otimesₜ n) (i, j) = c.repr
 n j • b.repr m i
参数：b : Basis ι S M；c : Basis κ R N；m : M；n : N；i : ι；j : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `Finsupp.basisSingleOne_repr`：∀ {R : Type u_1} {ι : Type u_3} [inst : Sem
iring R], Finsupp.basisSingleOne.repr = LinearEquiv.refl R (ι →₀ R)
· 使用定理 `LinearEquiv.trans_refl`：trans_refl : e.trans (refl S M₂) = e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `finsuppTensorFinsupp_apply`：finsuppTensorFinsupp_apply (f : ι ->₀ M) (g 
: κ ->₀ N) (i : ι) (k : κ) : finsuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, 
k) = f i otimesₜ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorProduct_repr_tmul_apply (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (tensorProduct b c).repr (m ⊗ₜ n) (i, j) = c.repr n j • b.repr m i := by
  simp [tensorProduct]

variable (S : Type*) [Semiring S] [Algebra R S]

/-- The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`. -/
noncomputable
/-
**Module.Basis.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：baseChange (b : Basis ι R M) : Basis ι S (S otimes[R] M)
参数：b : Basis ι R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
def baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=
  (tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)

@[simp]
/-
**Module.Basis.baseChange_repr_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：baseChange_repr_tmul (b : Basis ι R M) (x y i) : (b.baseChange S).repr (x 
otimesₜ y) i = b.repr y i • x
参数：b : Basis ι R M；x y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `Finsupp.basisSingleOne_repr`：∀ {R : Type u_1} {ι : Type u_3} [inst : Sem
iring R], Finsupp.basisSingleOne.repr = LinearEquiv.refl R (ι →₀ R)
· 使用定理 `LinearEquiv.trans_refl`：trans_refl : e.trans (refl S M₂) = e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `Equiv.punitProd_symm_apply`：∀ (α : Type u_9) (a : α), (Equiv.punitProd α
).symm a = (PUnit.unit, a)
· 使用定理 `finsuppTensorFinsupp_apply`：finsuppTensorFinsupp_apply (f : ι ->₀ M) (g 
: κ ->₀ N) (i : ι) (k : κ) : finsuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, 
k) = f i otimesₜ…
· 使用定理 `Module.Basis.singleton_repr`：singleton_repr (ι R : Type*) [Unique ι] [Se
miring R] (x i) : (Basis.singleton ι R).repr x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_repr_tmul (b : Basis ι R M) (x y i) :
    (b.baseChange S).repr (x ⊗ₜ y) i = b.repr y i • x := by
  simp [baseChange, tensorProduct]

@[simp]
/-
**Module.Basis.baseChange_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：baseChange_apply (b : Basis ι R M) (i) : b.baseChange S i = 1 otimesₜ b i
参数：b : Basis ι R M；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Equiv.punitProd_symm_apply`：∀ (α : Type u_9) (a : α), (Equiv.punitProd α
).symm a = (PUnit.unit, a)
· 使用定理 `Finsupp.coe_basisSingleOne`：coe_basisSingleOne : (Finsupp.basisSingleOne
 : ι -> ι ->₀ R) = fun i => Finsupp.single i 1
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `finsuppTensorFinsupp_symm_single`：finsuppTensorFinsupp_symm_single (i : 
ι × κ) (m : M) (n : N) : (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single
 i (m otimesₜ n)) = Fi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Module.Basis.coe_singleton`：coe_singleton {ι R : Type*} [Unique ι] [Semi
ring R] : ⇑(Basis.singleton ι R) = 1
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_apply (b : Basis ι R M) (i) :
    b.baseChange S i = 1 ⊗ₜ b i := by
  simp [baseChange, tensorProduct]

end Module.Basis

section

variable [DecidableEq ι] [DecidableEq κ]
variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M ⊗[R] N)

/--
If `{𝒞ᵢ}` is a basis for the module `N`, then every elements of `x ∈ M ⊗ N` can be uniquely written
as `∑ᵢ mᵢ ⊗ 𝒞ᵢ` for some `mᵢ ∈ M`.
-/
/-
**TensorProduct.equivFinsuppOfBasisRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisRight : M otimes[R] N ≃ₗ[R] κ ->₀ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `{𝒞ᵢ}` is a basis for the module `N`, then every elements of `x ∈ M ⊗ N` can 
be uniquely written
as `∑ᵢ mᵢ ⊗ 𝒞ᵢ` for some `mᵢ ∈ M`.
-/
def TensorProduct.equivFinsuppOfBasisRight : M ⊗[R] N ≃ₗ[R] κ →₀ M :=
  LinearEquiv.lTensor M 𝒞.repr ≪≫ₗ TensorProduct.finsuppScalarRight R R M κ

@[simp]
/-
**TensorProduct.equivFinsuppOfBasisRight_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：TensorProduct.equivFinsuppOfBasisRight_apply_tmul (m : M) (n : N) : (Tenso
rProduct.equivFinsuppOfBasisRight 𝒞) (m otimesₜ n) = (𝒞.repr n).mapRange (· • m)
 (zero_smul _ _)
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppScalarRight_apply_tmul_apply`：finsuppScalarRight_ap
ply_tmul_apply (m : M) (p : ι ->₀ R) (i : ι) : finsuppScalarRight R S M ι (m oti
mesₜ[R] p) i = p i • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m ⊗ₜ n) =
    (𝒞.repr n).mapRange (· • m) (zero_smul _ _) := by
  ext; simp [equivFinsuppOfBasisRight]
/-
**TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply (m : M) (n : N) (i
 : κ) : (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m otimesₜ n) i = 𝒞.repr n i 
• m
参数：m : M；n : N；i : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_apply_tmul`：TensorProduct.equivFi
nsuppOfBasisRight_apply_tmul (m : M) (n : N) : (TensorProduct.equivFinsuppOfBasi
sRight 𝒞) (m otimesₜ n) = (𝒞.repr n).ma…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
    (m : M) (n : N) (i : κ) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m ⊗ₜ n) i =
    𝒞.repr n i • m := by
  simp only [equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]
/-
**TensorProduct.equivFinsuppOfBasisRight_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisRight_symm : (TensorProduct.equivFinsuppO
fBasisRight 𝒞).symm.toLinearMap = Finsupp.lsum R fun i => (TensorProduct.mk R M 
N).flip (𝒞 i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppScalarRight_symm_apply_single`：finsuppScalarRight_s
ymm_apply_single (i : ι) (m : M) : (finsuppScalarRight R S M ι).symm (Finsupp.si
ngle i m) = m otimesₜ[R] (Finsupp.single…
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.lsum_comp_lsingle`：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3
} {R : Type u_5} {R₂ : Type u_6} (S : Type u_8) [inst : Semiring R]   [inst_1 : 
Semiring R₂] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TensorProduct.equivFinsuppOfBasisRight_symm :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.toLinearMap =
    Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i) := by
  ext; simp [equivFinsuppOfBasisRight]

@[simp]
/-
**TensorProduct.equivFinsuppOfBasisRight_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：TensorProduct.equivFinsuppOfBasisRight_symm_apply (b : κ ->₀ M) : (TensorP
roduct.equivFinsuppOfBasisRight 𝒞).symm b = b.sum fun i m => m otimesₜ 𝒞 i
参数：b : κ ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_symm`：TensorProduct.equivFinsuppO
fBasisRight_symm : (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.toLinearMap =
 Finsupp.lsum R fun i => (TensorP…
-/
lemma TensorProduct.equivFinsuppOfBasisRight_symm_apply (b : κ →₀ M) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm b = b.sum fun i m ↦ m ⊗ₜ 𝒞 i :=
  congr($(TensorProduct.equivFinsuppOfBasisRight_symm 𝒞) b)

omit [DecidableEq κ] in
/-
**TensorProduct.sum_tmul_basis_right_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.sum_tmul_basis_right_injective : Function.Injective (Finsupp
.lsum R fun i => (TensorProduct.mk R M N).flip (𝒞 i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_symm`：TensorProduct.equivFinsuppO
fBasisRight_symm : (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.toLinearMap =
 Finsupp.lsum R fun i => (TensorP…
-/
lemma TensorProduct.sum_tmul_basis_right_injective :
    Function.Injective (Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i)) :=
  have := Classical.decEq κ
  (equivFinsuppOfBasisRight_symm (M := M) 𝒞).symm ▸
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective

omit [DecidableEq κ] in
/-
**TensorProduct.sum_tmul_basis_right_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.sum_tmul_basis_right_eq_zero (b : κ ->₀ M) (h : (b.sum fun i
 m => m otimesₜ[R] 𝒞 i) = 0) : b = 0
参数：b : κ ->₀ M；h : (b.sum fun i m => m otimesₜ[R] 𝒞 i) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_symm_apply`：TensorProduct.equivFi
nsuppOfBasisRight_symm_apply (b : κ ->₀ M) : (TensorProduct.equivFinsuppOfBasisR
ight 𝒞).symm b = b.sum fun i m => m oti…
-/
lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (b : κ →₀ M) (h : (b.sum fun i m ↦ m ⊗ₜ[R] 𝒞 i) = 0) : b = 0 :=
  have := Classical.decEq κ
  (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective (a₂ := 0) <| by simpa

/--
If `{ℬᵢ}` is a basis for the module `M`, then every elements of `x ∈ M ⊗ N` can be uniquely written
as `∑ᵢ ℬᵢ ⊗ nᵢ` for some `nᵢ ∈ N`.
-/
/-
**TensorProduct.equivFinsuppOfBasisLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisLeft : M otimes[R] N ≃ₗ[R] ι ->₀ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `{ℬᵢ}` is a basis for the module `M`, then every elements of `x ∈ M ⊗ N` can 
be uniquely written
as `∑ᵢ ℬᵢ ⊗ nᵢ` for some `nᵢ ∈ N`.
-/
def TensorProduct.equivFinsuppOfBasisLeft : M ⊗[R] N ≃ₗ[R] ι →₀ N :=
  TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

@[simp]
/-
**TensorProduct.equivFinsuppOfBasisLeft_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisLeft_apply_tmul (m : M) (n : N) : (Tensor
Product.equivFinsuppOfBasisLeft ℬ) (m otimesₜ n) = (ℬ.repr m).mapRange (· • n) (
zero_smul _ _)
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_apply_tmul`：TensorProduct.equivFi
nsuppOfBasisRight_apply_tmul (m : M) (n : N) : (TensorProduct.equivFinsuppOfBasi
sRight 𝒞) (m otimesₜ n) = (𝒞.repr n).ma…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m ⊗ₜ n) =
    (ℬ.repr m).mapRange (· • n) (zero_smul _ _) := by
  simp [equivFinsuppOfBasisLeft]
/-
**TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply (m : M) (n : N) (i 
: ι) : (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m otimesₜ n) i = ℬ.repr m i • 
n
参数：m : M；n : N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul`：TensorProduct.equivFin
suppOfBasisLeft_apply_tmul (m : M) (n : N) : (TensorProduct.equivFinsuppOfBasisL
eft ℬ) (m otimesₜ n) = (ℬ.repr m).mapR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply
    (m : M) (n : N) (i : ι) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m ⊗ₜ n) i =
    ℬ.repr m i • n := by
  simp only [equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]

/-- Given a basis `𝒞` of `N`, `x ∈ M ⊗ N` can be written as `∑ᵢ mᵢ ⊗ 𝒞 i`. The coefficient `mᵢ`
equals the `i`-th coordinate functional applied to the right tensor factor. -/
/-
**TensorProduct.equivFinsuppOfBasisRight_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisRight_apply (x : M otimes[R] N) (i : κ) :
 equivFinsuppOfBasisRight 𝒞 x i = TensorProduct.rid R M ((𝒞.coord i).lTensor _ x
)
参数：x : M otimes[R] N；i : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_apply_tmul`：TensorProduct.equivFi
nsuppOfBasisRight_apply_tmul (m : M) (n : N) : (TensorProduct.equivFinsuppOfBasi
sRight 𝒞) (m otimesₜ n) = (𝒞.repr n).ma…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…

--- 原说明 ---
Given a basis `𝒞` of `N`, `x ∈ M ⊗ N` can be written as `∑ᵢ mᵢ ⊗ 𝒞 i`. The coeff
icient `mᵢ`
equals the `i`-th coordinate functional applied to the right tensor factor.
-/
lemma TensorProduct.equivFinsuppOfBasisRight_apply (x : M ⊗[R] N) (i : κ) :
    equivFinsuppOfBasisRight 𝒞 x i = TensorProduct.rid R M ((𝒞.coord i).lTensor _ x) := by
  induction x <;> simp_all

/-- Given a basis `ℬ` of `M`, `x ∈ M ⊗ N` can be written as `∑ᵢ ℬ i ⊗ nᵢ`. The coefficient `nᵢ`
equals the `i`-th coordinate functional applied to the left tensor factor. -/
/-
**TensorProduct.equivFinsuppOfBasisLeft_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisLeft_apply (x : M otimes[R] N) (i : ι) : 
equivFinsuppOfBasisLeft ℬ x i = TensorProduct.lid R N ((ℬ.coord i).rTensor _ x)
参数：x : M otimes[R] N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul`：TensorProduct.equivFin
suppOfBasisLeft_apply_tmul (m : M) (n : N) : (TensorProduct.equivFinsuppOfBasisL
eft ℬ) (m otimesₜ n) = (ℬ.repr m).mapR…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…

--- 原说明 ---
Given a basis `ℬ` of `M`, `x ∈ M ⊗ N` can be written as `∑ᵢ ℬ i ⊗ nᵢ`. The coeff
icient `nᵢ`
equals the `i`-th coordinate functional applied to the left tensor factor.
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_apply (x : M ⊗[R] N) (i : ι) :
    equivFinsuppOfBasisLeft ℬ x i = TensorProduct.lid R N ((ℬ.coord i).rTensor _ x) := by
  induction x <;> simp_all
/-
**TensorProduct.equivFinsuppOfBasisLeft_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisLeft_symm : (TensorProduct.equivFinsuppOf
BasisLeft ℬ).symm.toLinearMap = Finsupp.lsum R fun i => (TensorProduct.mk R M N)
 (ℬ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_symm_apply`：TensorProduct.equivFi
nsuppOfBasisRight_symm_apply (b : κ ->₀ M) : (TensorProduct.equivFinsuppOfBasisR
ight 𝒞).symm b = b.sum fun i m => m oti…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.lsum_comp_lsingle`：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3
} {R : Type u_5} {R₂ : Type u_6} (S : Type u_8) [inst : Semiring R]   [inst_1 : 
Semiring R₂] [i…
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_symm :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.toLinearMap =
    Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i) := by
  ext; simp [equivFinsuppOfBasisLeft]

@[simp]
/-
**TensorProduct.equivFinsuppOfBasisLeft_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.equivFinsuppOfBasisLeft_symm_apply (b : ι ->₀ N) : (TensorPr
oduct.equivFinsuppOfBasisLeft ℬ).symm b = b.sum fun i n => ℬ i otimesₜ n
参数：b : ι ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_symm`：TensorProduct.equivFinsuppOf
BasisLeft_symm : (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.toLinearMap = Fi
nsupp.lsum R fun i => (TensorPro…
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_symm_apply (b : ι →₀ N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm b = b.sum fun i n ↦ ℬ i ⊗ₜ n :=
  congr($(TensorProduct.equivFinsuppOfBasisLeft_symm ℬ) b)

omit [DecidableEq κ] in
/-- Elements in `M ⊗ N` can be represented by sum of elements in `M` tensor elements of basis of
`N`. -/
/-
**TensorProduct.eq_repr_basis_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.eq_repr_basis_right : exists b : κ ->₀ M, b.sum (fun i m => 
m otimesₜ 𝒞 i) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TensorProduct.equivFinsuppOfBasisRight_symm_apply`：TensorProduct.equivFi
nsuppOfBasisRight_symm_apply (b : κ ->₀ M) : (TensorProduct.equivFinsuppOfBasisR
ight 𝒞).symm b = b.sum fun i m => m oti…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…

--- 原说明 ---
Elements in `M ⊗ N` can be represented by sum of elements in `M` tensor elements
 of basis of
`N`.
-/
lemma TensorProduct.eq_repr_basis_right :
    ∃ b : κ →₀ M, b.sum (fun i m ↦ m ⊗ₜ 𝒞 i) = x := by
  classical simpa using (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.surjective x

omit [DecidableEq ι] in
/-- Elements in `M ⊗ N` can be represented by sum of elements of basis of `M` tensor elements of
  `N`. -/
/-
**TensorProduct.eq_repr_basis_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.eq_repr_basis_left : exists (c : ι ->₀ N), (c.sum fun i n =>
 ℬ i otimesₜ n) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_symm_apply`：TensorProduct.equivFin
suppOfBasisLeft_symm_apply (b : ι ->₀ N) : (TensorProduct.equivFinsuppOfBasisLef
t ℬ).symm b = b.sum fun i n => ℬ i oti…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Elements in `M ⊗ N` can be represented by sum of elements of basis of `M` tensor
 elements of
  `N`.
-/
lemma TensorProduct.eq_repr_basis_left :
    ∃ (c : ι →₀ N), (c.sum fun i n ↦ ℬ i ⊗ₜ n) = x := by
  classical obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
  exact ⟨c, (TensorProduct.comm R M N).injective <| by simp [Finsupp.sum]⟩

omit [DecidableEq ι] in
/-
**TensorProduct.sum_tmul_basis_left_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.sum_tmul_basis_left_injective : Function.Injective (Finsupp.
lsum R fun i => (TensorProduct.mk R M N) (ℬ i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_symm`：TensorProduct.equivFinsuppOf
BasisLeft_symm : (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.toLinearMap = Fi
nsupp.lsum R fun i => (TensorPro…
-/
lemma TensorProduct.sum_tmul_basis_left_injective :
    Function.Injective (Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i)) :=
  have := Classical.decEq ι
  (equivFinsuppOfBasisLeft_symm (N := N) ℬ).symm ▸
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective

omit [DecidableEq ι] in
/-
**TensorProduct.sum_tmul_basis_left_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.sum_tmul_basis_left_eq_zero (b : ι ->₀ N) (h : (b.sum fun i 
n => ℬ i otimesₜ[R] n) = 0) : b = 0
参数：b : ι ->₀ N；h : (b.sum fun i n => ℬ i otimesₜ[R] n) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_symm_apply`：TensorProduct.equivFin
suppOfBasisLeft_symm_apply (b : ι ->₀ N) : (TensorProduct.equivFinsuppOfBasisLef
t ℬ).symm b = b.sum fun i n => ℬ i oti…
-/
lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (b : ι →₀ N) (h : (b.sum fun i n ↦ ℬ i ⊗ₜ[R] n) = 0) : b = 0 :=
  have := Classical.decEq ι
  (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective (a₂ := 0) <| by simpa

end

/-
**Module.Free.tensor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Free.tensor [Module.Free S M] [Module.Free R N] : Module.Free S (M 
otimes[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
instance Module.Free.tensor [Module.Free S M] [Module.Free R N] : Module.Free S (M ⊗[R] N) :=
  let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)

end CommSemiring

end

