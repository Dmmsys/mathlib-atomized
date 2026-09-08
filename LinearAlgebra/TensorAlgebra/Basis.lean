/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# A basis for `TensorAlgebra R M`

## Main definitions

* `TensorAlgebra.equivMonoidAlgebra b : TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ`:
  the isomorphism given by a basis `b : Basis κ R M`.
* `Basis.tensorAlgebra b : Basis (FreeMonoid κ) R (TensorAlgebra R M)`:
  the basis on the tensor algebra given by a basis `b : Basis κ R M`.

## Main results

* `TensorAlgebra.instFreeModule`: the tensor algebra over `M` is free when `M` is
* `TensorAlgebra.rank_eq`

-/

@[expose] public section

open Module

namespace TensorAlgebra

universe uκ uR uM
variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A basis provides an algebra isomorphism with the free algebra, replacing each basis vector
with its index. -/
/-
**TensorAlgebra.equivFreeAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：equivFreeAlgebra (b : Basis κ R M) : TensorAlgebra R M ≃ₐ[R] FreeAlgebra R
 κ
参数：b : Basis κ R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis provides an algebra isomorphism with the free algebra, replacing each ba
sis vector
with its index.
-/
noncomputable def equivFreeAlgebra (b : Basis κ R M) :
    TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ :=
  AlgEquiv.ofAlgHom
    (TensorAlgebra.lift _ (Finsupp.linearCombination _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
    (FreeAlgebra.lift _ (ι R ∘ b))
    (by ext; simp)
    (hom_ext <| b.ext fun i => by simp)

@[simp]
/-
**TensorAlgebra.equivFreeAlgebra_** 是 Mathlib 中的一个引理，位于命名空间 `TensorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivFreeAlgebra_ι_apply (b : Basis κ R M) (i : κ) :
    equivFreeAlgebra b (ι R (b i)) = FreeAlgebra.ι R i :=
  (TensorAlgebra.lift_ι_apply _ _).trans <| by simp

@[simp]
/-
**TensorAlgebra.equivFreeAlgebra_symm_** 是 Mathlib 中的一个引理，位于命名空间 `TensorAlgebra`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivFreeAlgebra_symm_ι (b : Basis κ R M) (i : κ) :
    (equivFreeAlgebra b).symm (FreeAlgebra.ι R i) = ι R (b i) :=
  (equivFreeAlgebra b).toEquiv.symm_apply_eq.mpr <| equivFreeAlgebra_ι_apply b i |>.symm

/-- A basis on `M` can be lifted to a basis on `TensorAlgebra R M` -/
@[simps! repr_apply]
/-
**TensorAlgebra._root_.Module.Basis.tensorAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Ten
sorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis on `M` can be lifted to a basis on `TensorAlgebra R M`
-/
noncomputable def _root_.Module.Basis.tensorAlgebra (b : Basis κ R M) :
    Basis (FreeMonoid κ) R (TensorAlgebra R M) :=
  (FreeAlgebra.basisFreeMonoid R κ).map <| (equivFreeAlgebra b).symm.toLinearEquiv

/-- `TensorAlgebra R M` is free when `M` is. -/
/-
**TensorAlgebra.instModuleFree** 是 Mathlib 中的一个实例，位于命名空间 `TensorAlgebra`。
形式化陈述：instModuleFree [Module.Free R M] : Module.Free R (TensorAlgebra R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…

--- 原说明 ---
`TensorAlgebra R M` is free when `M` is.
-/
instance instModuleFree [Module.Free R M] : Module.Free R (TensorAlgebra R M) :=
  let ⟨⟨_κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.tensorAlgebra

/-- The `TensorAlgebra` of a free module over a commutative semiring with no zero-divisors has
no zero-divisors. -/
/-
**TensorAlgebra.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `TensorAlgebra`。
形式化陈述：instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] : NoZeroDivisors (
TensorAlgebra R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.noZeroDivisors`：∀ {A : Type u_7} (B : Type u_8) [inst : MulZero
Class A] [inst_1 : MulZeroClass B] [NoZeroDivisors B] (e : A ≃* B),   NoZeroDivi
sors A

--- 原说明 ---
The `TensorAlgebra` of a free module over a commutative semiring with no zero-di
visors has
no zero-divisors.
-/
instance instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] :
    NoZeroDivisors (TensorAlgebra R M) :=
  have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivFreeAlgebra b).toMulEquiv.noZeroDivisors

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The `TensorAlgebra` of a free module over an integral domain is a domain. -/
/-
**TensorAlgebra.instIsDomain** 是 Mathlib 中的一个实例，位于命名空间 `TensorAlgebra`。
形式化陈述：instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (TensorAlgebra R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `TensorAlgebra.instNontrivial`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontriv
ial R], Nontrivial…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
The `TensorAlgebra` of a free module over an integral domain is a domain.
-/
instance instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (TensorAlgebra R M) :=
  NoZeroDivisors.to_isDomain _

attribute [pp_with_univ] Cardinal.lift

open Cardinal in
/-
**TensorAlgebra.rank_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorAlgebra`。
形式化陈述：rank_eq [Nontrivial R] [Module.Free R M] : Module.rank R (TensorAlgebra R 
M) = Cardinal.lift.{uR} (sum fun n => Module.rank R M ^ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `FreeAlgebra.rank_eq`：rank_eq [CommRing R] [Nontrivial R] : Module.rank R
 (FreeAlgebra R X) = Cardinal.lift.{u} (Cardinal.mk (List X))
· 使用定理 `Cardinal.mk_list_eq_sum_pow`：mk_list_eq_sum_pow (α : Type u) : #(List α)
 = sum fun n => #α ^ n
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
lemma rank_eq [Nontrivial R] [Module.Free R M] :
    Module.rank R (TensorAlgebra R M) = Cardinal.lift.{uR} (sum fun n ↦ Module.rank R M ^ n) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [(equivFreeAlgebra b).toLinearEquiv.rank_eq, FreeAlgebra.rank_eq, mk_list_eq_sum_pow,
    Basis.mk_eq_rank'' b]

end CommRing

end TensorAlgebra

