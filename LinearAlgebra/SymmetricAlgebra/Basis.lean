/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.MvPolynomial

/-!
# A basis for `SymmetricAlgebra R M`

## Main definitions

* `SymmetricAlgebra.equivMvPolynomial b : SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R`:
  the isomorphism given by a basis `b : Basis I R M`.
* `Basis.symmetricAlgebra b : Basis (I →₀ ℕ) R (SymmetricAlgebra R M)`:
  the basis on the symmetric algebra given by a basis `b : Basis I R M`.

## Main results

* `SymmetricAlgebra.instFreeModule`: the symmetric algebra over `M` is free when `M` is free.
* `SymmetricAlgebra.rank_eq`: the rank of `SymmetricAlgebra R M` when `M` is a nontrivial free
  module is equal to `max (Module.rank R M) Cardinal.aleph0`.

## Implementation notes

This file closely mirrors the corresponding file for `TensorAlgebra`.
-/

@[expose] public section

open Module

namespace SymmetricAlgebra

universe uκ uR uM
variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
/-- `SymmetricAlgebra.equivMvPolynomial` gives an algebra isomorphism between the symmetric algebra
over a free module and multivariate polynomials over a basis. This is analogous to
`TensorAlgebra.equivFreeAlgebra`. -/
/-
**SymmetricAlgebra.equivMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricAlgebra
`。
形式化陈述：equivMvPolynomial (b : Basis κ R M) : SymmetricAlgebra R M ≃ₐ[R] MvPolynom
ial κ R
参数：b : Basis κ R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SymmetricAlgebra.equivMvPolynomial` gives an algebra isomorphism between the sy
mmetric algebra
over a free module and multivariate polynomials over a basis. This is analogous 
to
`TensorAlgebra.equivFreeAlgebra`.
-/
noncomputable def equivMvPolynomial (b : Basis κ R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial κ R :=
  .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i ↦ ι R M (b i))
    (MvPolynomial.algHom_ext fun i ↦ by simp)
    (algHom_ext <| b.ext fun i ↦ by simp)

@[simp]
/-
**SymmetricAlgebra.equivMvPolynomial_** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricAlgebr
a`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivMvPolynomial_ι_apply (b : Basis κ R M) (i : κ) :
    equivMvPolynomial b (ι R M (b i)) = .X (R := R) i :=
  (SymmetricAlgebra.lift_ι_apply _ _).trans <| by simp

@[simp]
/-
**SymmetricAlgebra.equivMvPolynomial_symm_X** 是 Mathlib 中的一个引理，位于命名空间 `Symmetric
Algebra`。
形式化陈述：equivMvPolynomial_symm_X (b : Basis κ R M) (i : κ) : (equivMvPolynomial b)
.symm (MvPolynomial.X i) = ι R M (b i)
参数：b : Basis κ R M；i : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SymmetricAlgebra.equivMvPolynomial_ι_apply`：equivMvPolynomial_ι_apply (b
 : Basis κ R M) (i : κ) : equivMvPolynomial b (ι R M (b i)) = .X (R
-/
lemma equivMvPolynomial_symm_X (b : Basis κ R M) (i : κ) :
    (equivMvPolynomial b).symm (MvPolynomial.X i) = ι R M (b i) :=
  (equivMvPolynomial b).toEquiv.symm_apply_eq.mpr <| equivMvPolynomial_ι_apply b i |>.symm

set_option backward.isDefEq.respectTransparency false in
/-
**SymmetricAlgebra.IsSymmetricAlgebra.mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `Sy
mmetricAlgebra.IsSymmetricAlgebra`。
形式化陈述：∀ {R : Type uR} {M : Type uM} [inst : CommSemiring R] [inst_1 : AddCommMon
oid M] [inst_2 : _root_.Module R M]   (I : Type u_1) (b : Module.Basis I R M), I
sSymmetricAlgebra ((b.constr R) MvPolynomial.X)
参数：I : Type u_1；b : Module.Basis I R M；(b.constr R) MvPolynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem IsSymmetricAlgebra.mvPolynomial (I : Type*) (b : Basis I R M) :
    IsSymmetricAlgebra (Basis.constr b R (.X : I → MvPolynomial I R)) :=
  (SymmetricAlgebra.equivMvPolynomial b).bijective

/-- A basis on `M` can be lifted to a basis on `SymmetricAlgebra R M`. -/
@[simps! repr_apply]
/-
**SymmetricAlgebra._root_.Module.Basis.symmetricAlgebra** 是 Mathlib 中的一个定义，位于命名空
间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis on `M` can be lifted to a basis on `SymmetricAlgebra R M`.
-/
noncomputable def _root_.Module.Basis.symmetricAlgebra (b : Basis κ R M) :
    Basis (κ →₀ ℕ) R (SymmetricAlgebra R M) :=
  (MvPolynomial.basisMonomials κ R).map <| (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv

/-- `SymmetricAlgebra R M` is free when `M` is. -/
/-
**SymmetricAlgebra.instModuleFree** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
形式化陈述：instModuleFree [Module.Free R M] : Module.Free R (SymmetricAlgebra R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…

--- 原说明 ---
`SymmetricAlgebra R M` is free when `M` is.
-/
instance instModuleFree [Module.Free R M] : Module.Free R (SymmetricAlgebra R M) :=
  let ⟨⟨_I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.symmetricAlgebra

/-- The `SymmetricAlgebra` of a free module over a commutative semiring with no zero-divisors has
no zero-divisors. -/
/-
**SymmetricAlgebra.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebr
a`。
形式化陈述：instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] : NoZeroDivisors (
SymmetricAlgebra R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.noZeroDivisors`：∀ {A : Type u_7} (B : Type u_8) [inst : MulZero
Class A] [inst_1 : MulZeroClass B] [NoZeroDivisors B] (e : A ≃* B),   NoZeroDivi
sors A
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)

--- 原说明 ---
The `SymmetricAlgebra` of a free module over a commutative semiring with no zero
-divisors has
no zero-divisors.
-/
instance instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] :
    NoZeroDivisors (SymmetricAlgebra R M) :=
  have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivMvPolynomial b).toMulEquiv.noZeroDivisors

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The `TensorAlgebra` of a free module over an integral domain is a domain. -/
/-
**SymmetricAlgebra.instIsDomain** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
形式化陈述：instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (SymmetricAlgebra R
 M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `SymmetricAlgebra.instNontrivial`：∀ {R : Type u_1} (M : Type u_2) [inst :
 CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nont
rivial R], Nontrivial…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
The `TensorAlgebra` of a free module over an integral domain is a domain.
-/
instance instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (SymmetricAlgebra R M) :=
  NoZeroDivisors.to_isDomain _

attribute [pp_with_univ] Cardinal.lift

open Cardinal in
/-
**SymmetricAlgebra.rank_eq** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricAlgebra`。
形式化陈述：rank_eq [Nontrivial M] [Module.Free R M] : Module.rank R (SymmetricAlgebra
 R M) = Cardinal.lift.{uR} (max (Module.rank R M) ℵ₀)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `MvPolynomial.rank_eq_lift`：rank_eq_lift : Module.rank K (MvPolynomial σ 
K) = lift.{v} #(σ ->₀ Nat)
· 使用定理 `Cardinal.mk_finsupp_nat`：mk_finsupp_nat (α : Type u) [Nonempty α] : #(α 
->₀ Nat) = max #α ℵ₀
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
lemma rank_eq [Nontrivial M] [Module.Free R M] :
    Module.rank R (SymmetricAlgebra R M) = Cardinal.lift.{uR} (max (Module.rank R M) ℵ₀) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have : Nonempty κ := Basis.index_nonempty b
  have : Nontrivial R := Module.nontrivial R M
  rw [(equivMvPolynomial b).toLinearEquiv.rank_eq, MvPolynomial.rank_eq_lift,
    Cardinal.mk_finsupp_nat, Basis.mk_eq_rank'' b]

end CommRing

end SymmetricAlgebra

