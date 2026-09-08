/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.IsTensorProduct

/-!

# Tensor Product of (multivariate) polynomial rings

Let `Semiring R`, `Algebra R S` and `Module R N`.

* `MvPolynomial.rTensor` gives the linear equivalence
  `MvPolynomial σ S ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ (S ⊗[R] N)` characterized,
  for `p : MvPolynomial σ S`, `n : N` and `d : σ →₀ ℕ`, by
  `rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n`
* `MvPolynomial.scalarRTensor` gives the linear equivalence
  `MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N`
  such that `MvPolynomial.scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n`
  for `p : MvPolynomial σ R`, `n : N` and `d : σ →₀ ℕ`, by

* `MvPolynomial.rTensorAlgHom`, the algebra morphism from the tensor product
  of a polynomial algebra by an algebra to a polynomial algebra
* `MvPolynomial.rTensorAlgEquiv`, `MvPolynomial.scalarRTensorAlgEquiv`,
  the tensor product of a polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra

## TODO :
* `MvPolynomial.rTensor` could be phrased in terms of `AddMonoidAlgebra`, and
  `MvPolynomial.rTensor` then has `smul` by the polynomial algebra.
* `MvPolynomial.rTensorAlgHom` and `MvPolynomial.scalarRTensorAlgEquiv`
  are morphisms for the algebra structure by `MvPolynomial σ R`.
-/

@[expose] public section


universe u v

noncomputable section

namespace MvPolynomial

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {N : Type v} [CommSemiring R]

variable {σ ι : Type*}

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Algebra

variable [CommSemiring N] [Algebra R N]

/-- The algebra morphism from a tensor product of a polynomial algebra
  by an algebra to a polynomial algebra -/
/-
**MvPolynomial.rTensorAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：rTensorAlgEquiv : S otimes[R] MvPolynomial σ N ≃ₐ[S] MvPolynomial σ (S oti
mes[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra morphism from a tensor product of a polynomial algebra
  by an algebra to a polynomial algebra
-/
noncomputable def rTensorAlgEquiv : S ⊗[R] MvPolynomial σ N ≃ₐ[S] MvPolynomial σ (S ⊗[R] N) :=
  AddMonoidAlgebra.rTensorEquivAlgEquiv R ..

@[deprecated (since := "2026-06-18")] alias rTensorAlgHom := rTensorAlgEquiv

@[simp]
/-
**MvPolynomial.coeff_rTensorAlgEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomia
l`。
形式化陈述：coeff_rTensorAlgEquiv_tmul (s : S) (p : MvPolynomial σ N) (d : σ ->₀ Nat) 
: coeff d (rTensorAlgEquiv (s otimesₜ[R] p)) = s otimesₜ[R] coeff d p
参数：s : S；p : MvPolynomial σ N；d : σ ->₀ Nat。
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
· 使用定理 `AddMonoidAlgebra.rTensorEquiv_tmulAlgEquiv`：∀ {R : Type u_1} {M : Type u
_2} {S : Type u_4} {A : Type u_5} {B : Type u_6} [inst : CommSemiring R]   [inst
_1 : CommSemiring S] [inst_2 : C…
· 使用定理 `AddMonoidAlgebra.coeff_mapAlgHom`：∀ {R : Type u_1} {A : Type u_4} {B : T
ype u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_rTensorAlgEquiv_tmul (s : S) (p : MvPolynomial σ N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgEquiv (s ⊗ₜ[R] p)) = s ⊗ₜ[R] coeff d p := by
  simp [rTensorAlgEquiv, coeff, MvPolynomial, ← tmul_eq_smul_one_tmul]
/-
**MvPolynomial.coeff_rTensorAlgEquiv_monomial_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Mv
Polynomial`。
形式化陈述：coeff_rTensorAlgEquiv_monomial_tmul [DecidableEq σ] (e : σ ->₀ Nat) (s : S
) (n : N) (d : σ ->₀ Nat) : coeff d (rTensorAlgEquiv (s otimesₜ[R] monomial e n)
) = if e = d then s otimesₜ[R] n else 0
参数：e : σ ->₀ Nat；s : S；n : N；d : σ ->₀ Nat。
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
· 使用引理 `MvPolynomial.coeff_rTensorAlgEquiv_tmul`：coeff_rTensorAlgEquiv_tmul (s :
 S) (p : MvPolynomial σ N) (d : σ ->₀ Nat) : coeff d (rTensorAlgEquiv (s otimesₜ
[R] p)) = s otimesₜ[R] coeff …
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `TensorProduct.tmul_ite`：tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable
 P] : (x₁ otimesₜ[R] if P then x₂ else 0) = if P then x₁ otimesₜ x₂ else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_rTensorAlgEquiv_monomial_tmul [DecidableEq σ] (e : σ →₀ ℕ) (s : S) (n : N)
    (d : σ →₀ ℕ) :
    coeff d (rTensorAlgEquiv (s ⊗ₜ[R] monomial e n)) = if e = d then s ⊗ₜ[R] n else 0 := by
  simp [tmul_ite]

@[deprecated "Now a syntactic tautology" (since := "2026-06-18")]
/-
**MvPolynomial.rTensorAlgEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：rTensorAlgEquiv_apply (x : N otimes[R] MvPolynomial σ S) : rTensorAlgEquiv
 x = rTensorAlgHom x
参数：x : N otimes[R] MvPolynomial σ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma rTensorAlgEquiv_apply (x : N ⊗[R] MvPolynomial σ S) :
    rTensorAlgEquiv x = rTensorAlgHom x := rfl

/-- The tensor product of the polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra with
  coefficients in that algebra -/
/-
**MvPolynomial.scalarRTensorAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：scalarRTensorAlgEquiv : N otimes[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ 
N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of the polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra with
  coefficients in that algebra
-/
noncomputable def scalarRTensorAlgEquiv : N ⊗[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ N :=
  AddMonoidAlgebra.scalarTensorEquiv R N

variable (R)
variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- Tensoring `MvPolynomial σ R` on the left by an `R`-algebra `A` is algebraically
equivalent to `MvPolynomial σ A`. -/
/-
**MvPolynomial.algebraTensorAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：algebraTensorAlgEquiv : A otimes[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ 
A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring `MvPolynomial σ R` on the left by an `R`-algebra `A` is algebraically
equivalent to `MvPolynomial σ A`.
-/
noncomputable def algebraTensorAlgEquiv :
    A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A :=
  AddMonoidAlgebra.scalarTensorEquiv ..

@[simp]
/-
**MvPolynomial.algebraTensorAlgEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomia
l`。
形式化陈述：algebraTensorAlgEquiv_tmul (a : A) (p : MvPolynomial σ R) : algebraTensorA
lgEquiv R A (a otimesₜ p) = a • MvPolynomial.map (algebraMap R A) p
参数：a : A；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
-/
lemma algebraTensorAlgEquiv_tmul (a : A) (p : MvPolynomial σ R) :
    algebraTensorAlgEquiv R A (a ⊗ₜ p) = a • MvPolynomial.map (algebraMap R A) p :=
  AddMonoidAlgebra.scalarTensorEquiv_tmul ..

@[simp]
/-
**MvPolynomial.algebraTensorAlgEquiv_symm_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：algebraTensorAlgEquiv_symm_X (s : σ) : (algebraTensorAlgEquiv R A).symm (X
 s) = 1 otimesₜ X s
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_symm_single`：∀ {R : Type u_1} {M : Ty
pe u_2} {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2
 : Algebra R A]   [inst_3 : AddCommM…
-/
lemma algebraTensorAlgEquiv_symm_X (s : σ) :
    (algebraTensorAlgEquiv R A).symm (X s) = 1 ⊗ₜ X s :=
  AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]
/-
**MvPolynomial.algebraTensorAlgEquiv_symm_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Mv
Polynomial`。
形式化陈述：algebraTensorAlgEquiv_symm_monomial (m : σ ->₀ Nat) (a : A) : (algebraTens
orAlgEquiv R A).symm (monomial m a) = a otimesₜ monomial m 1
参数：m : σ ->₀ Nat；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_symm_single`：∀ {R : Type u_1} {M : Ty
pe u_2} {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2
 : Algebra R A]   [inst_3 : AddCommM…
-/
lemma algebraTensorAlgEquiv_symm_monomial (m : σ →₀ ℕ) (a : A) :
    (algebraTensorAlgEquiv R A).symm (monomial m a) = a ⊗ₜ monomial m 1 :=
  AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]
/-
**MvPolynomial.algebraTensorAlgEquiv_symm_comp_aeval** 是 Mathlib 中的一个引理，位于命名空间 `
MvPolynomial`。
形式化陈述：algebraTensorAlgEquiv_symm_comp_aeval : ((algebraTensorAlgEquiv (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapAlgHom_single`：∀ {R : Type u_1} {A : Type u_4} {B : 
Type u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2
 : Semiring B] [inst_3 …
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
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_symm_single`：∀ {R : Type u_1} {M : Ty
pe u_2} {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2
 : Algebra R A]   [inst_3 : AddCommM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraTensorAlgEquiv_symm_comp_aeval :
    ((algebraTensorAlgEquiv (σ := σ) R A).symm.toAlgHom.restrictScalars R).comp
      (MvPolynomial.mapAlgHom (R := R) (S₁ := R) (S₂ := A) (Algebra.ofId R A)) =
      Algebra.TensorProduct.includeRight := by
  ext; simp [mapAlgHom, algebraTensorAlgEquiv, X, monomial]

@[simp]
/-
**MvPolynomial.algebraTensorAlgEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyn
omial`。
形式化陈述：algebraTensorAlgEquiv_symm_map (x : MvPolynomial σ R) : (algebraTensorAlgE
quiv R A).symm (map (algebraMap R A) x) = 1 otimesₜ x
参数：x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MvPolynomial.algebraTensorAlgEquiv_symm_comp_aeval`：algebraTensorAlgEqui
v_symm_comp_aeval : ((algebraTensorAlgEquiv (σ
-/
lemma algebraTensorAlgEquiv_symm_map (x : MvPolynomial σ R) :
    (algebraTensorAlgEquiv R A).symm (map (algebraMap R A) x) = 1 ⊗ₜ x :=
  DFunLike.congr_fun (algebraTensorAlgEquiv_symm_comp_aeval R A) x
/-
**MvPolynomial.aeval_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_one_tmul (f : σ -> S) (p : MvPolynomial σ R) : (aeval fun x => (1 ot
imesₜ[R] f x : N otimes[R] S)) p = 1 otimesₜ[R] (aeval f) p
参数：f : σ -> S；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma aeval_one_tmul (f : σ → S) (p : MvPolynomial σ R) :
    (aeval fun x ↦ (1 ⊗ₜ[R] f x : N ⊗[R] S)) p = 1 ⊗ₜ[R] (aeval f) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, Algebra.TensorProduct.algebraMap_apply]
    rw [← mul_one ((algebraMap R N) a), ← Algebra.smul_def, smul_tmul, Algebra.smul_def, mul_one]
  | add p q hp hq => simp [hp, hq, tmul_add]
  | mul_X p i h => simp [h]

variable (S σ ι) in
/-- `S[X] ⊗[R] R[Y] ≃ S[X, Y]` -/
/-
**MvPolynomial.tensorEquivSum** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：tensorEquivSum : MvPolynomial σ S otimes[R] MvPolynomial ι R ≃ₐ[S] MvPolyn
omial (σ oplus ι) S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S[X] ⊗[R] R[Y] ≃ S[X, Y]`
-/
def tensorEquivSum :
    MvPolynomial σ S ⊗[R] MvPolynomial ι R ≃ₐ[S] MvPolynomial (σ ⊕ ι) S :=
  ((algebraTensorAlgEquiv _ _).restrictScalars _).trans
    ((sumAlgEquiv _ _ _).symm.trans (renameEquiv _ (.sumComm ι σ)))

variable {R}

attribute [local simp] Algebra.smul_def
/-
**MvPolynomial.tensorEquivSum_X_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {σ : Type u_1} {ι : Type u_2} {S : 
Type u_3} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] (i : σ),   (MvPolyn
omial.tensorEquivSum R σ ι S) (MvPolynomial.X i ⊗ₜ[R] 1) = MvPolynomial.X (Sum.i
nl i)
参数：i : σ；MvPolynomial.tensorEquivSum R σ ι S；MvPolynomial.X i ⊗ₜ[R] 1；Sum.inl i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
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
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_single`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : Zero γ] (b : β) (c : γ),   (Finsupp.sumElim 0 fun₀ | b => c) = fun₀ 
| Sum.inr b => c
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma tensorEquivSum_X_tmul_one (i) :
    tensorEquivSum R σ ι S (.X i ⊗ₜ 1) = .X (.inl i) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, X, C, monomial]
/-
**MvPolynomial.tensorEquivSum_C_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {σ : Type u_1} {ι : Type u_2} {S : 
Type u_3} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] (r : S), (MvPolynom
ial.tensorEquivSum R σ ι S) (MvPolynomial.C r ⊗ₜ[R] 1) = MvPolynomial.C r
参数：r : S；MvPolynomial.tensorEquivSum R σ ι S；MvPolynomial.C r ⊗ₜ[R] 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
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
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : Zero γ], Finsupp.sumElim 0 0 = 0
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma tensorEquivSum_C_tmul_one (r) :
    tensorEquivSum R σ ι S (.C r ⊗ₜ 1) = .C r := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]
/-
**MvPolynomial.tensorEquivSum_one_tmul_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {σ : Type u_1} {ι : Type u_2} {S : 
Type u_3} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] (i : ι),   (MvPolyn
omial.tensorEquivSum R σ ι S) (1 ⊗ₜ[R] MvPolynomial.X i) = MvPolynomial.X (Sum.i
nr i)
参数：i : ι；MvPolynomial.tensorEquivSum R σ ι S；1 ⊗ₜ[R] MvPolynomial.X i；Sum.inr i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
· 使用定理 `AddMonoidAlgebra.mapAlgHom_single`：∀ {R : Type u_1} {A : Type u_4} {B : 
Type u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2
 : Semiring B] [inst_3 …
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
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_single_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : Zero γ] (a : α) (c : γ),   (fun₀ | a => c).sumElim 0 = fun₀ | Sum.in
l a => c
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma tensorEquivSum_one_tmul_X (i) :
    tensorEquivSum R σ ι S (1 ⊗ₜ .X i) = .X (.inr i) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial]
/-
**MvPolynomial.tensorEquivSum_one_tmul_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {σ : Type u_1} {ι : Type u_2} {S : 
Type u_3} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] (r : R),   (MvPolyn
omial.tensorEquivSum R σ ι S) (1 ⊗ₜ[R] MvPolynomial.C r) = MvPolynomial.C ((alge
braMap R S) r)
参数：r : R；MvPolynomial.tensorEquivSum R σ ι S；1 ⊗ₜ[R] MvPolynomial.C r；(algebraMa
p R S) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
· 使用定理 `AddMonoidAlgebra.mapAlgHom_single`：∀ {R : Type u_1} {A : Type u_4} {B : 
Type u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2
 : Semiring B] [inst_3 …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : Zero γ], Finsupp.sumElim 0 0 = 0
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma tensorEquivSum_one_tmul_C (r) :
    tensorEquivSum R σ ι S (1 ⊗ₜ .C r) = .C (algebraMap R S r) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]
/-
**MvPolynomial.tensorEquivSum_C_tmul_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {σ : Type u_1} {ι : Type u_2} {S : 
Type u_3} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] (r : R) (s : S),   
(MvPolynomial.tensorEquivSum R σ ι S) (MvPolynomial.C s ⊗ₜ[R] MvPolynomial.C r) 
= MvPolynomial.C (r • s)
参数：r : R；s : S；MvPolynomial.tensorEquivSum R σ ι S；MvPolynomial.C s ⊗ₜ[R] MvPoly
nomial.C r；r • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
· 使用定理 `AddMonoidAlgebra.mapAlgHom_single`：∀ {R : Type u_1} {A : Type u_4} {B : 
Type u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2
 : Semiring B] [inst_3 …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : Zero γ], Finsupp.sumElim 0 0 = 0
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma tensorEquivSum_C_tmul_C (r : R) (s : S) :
    tensorEquivSum R σ ι S (.C s ⊗ₜ .C r) = .C (r • s) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial,
    mul_comm]
/-
**MvPolynomial.tensorEquivSum_X_tmul_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {σ : Type u_1} {ι : Type u_2} {S : 
Type u_3} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] (i : σ) (j : ι),   
(MvPolynomial.tensorEquivSum R σ ι S) (MvPolynomial.X i ⊗ₜ[R] MvPolynomial.X j) 
=     MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr j)
参数：i : σ；j : ι；MvPolynomial.tensorEquivSum R σ ι S；MvPolynomial.X i ⊗ₜ[R] MvPoly
nomial.X j；Sum.inl i；Sum.inr j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.scalarTensorEquiv_tmul`：∀ {R : Type u_1} {M : Type u_2}
 {A : Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Alge
bra R A]   [inst_3 : AddCommM…
· 使用定理 `AddMonoidAlgebra.mapAlgHom_single`：∀ {R : Type u_1} {A : Type u_4} {B : 
Type u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2
 : Semiring B] [inst_3 …
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
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_single_single`：∀ {α : Type u_1} {β : Type u_2} {M : Type
 u_5} [inst : AddMonoid M] (a : α) (b : β) (m₁ m₂ : M),   ((fun₀ | a => m₁).sumE
lim fun₀ | b => m₂)…
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂
（共 32 条，此处仅展示前 30 条）
-/
@[simp] lemma tensorEquivSum_X_tmul_X (i j) :
    tensorEquivSum R σ ι S (.X i ⊗ₜ .X j) = .X (.inl i) * .X (.inr j) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial,
    Finsupp.mapDomain_add, add_comm]

section Pushout

attribute [local instance] algebraMvPolynomial

/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R S (MvPolynomial σ R) (MvPolynomial σ S) :=
  AddMonoidAlgebra.instIsPushout
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S) := .symm inferInstance

end Pushout

end Algebra

end MvPolynomial

end

