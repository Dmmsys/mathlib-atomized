/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Basic facts about algebra representations

This file collects basic general facts about algebra representations. The purpose of this file is
to have general results so that when we prove a corresponding fact about group representations
(or Lie algebra representations etc), we can deduce them as special cases of facts from this file.

-/

public section

variable {A V : Type*} (k : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k]

/-- Schur's Lemma: If `V` is a representation of an algebra `A` over an algebraically closed field
`k`, then any endomorphism of `V` is scalar. -/
/-
**IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed : Function.Bijectiv
e (algebraMap k (Module.End A V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)
· 使用定理 `IsAlgClosed.algebraMap_bijective_of_isIntegral`：algebraMap_bijective_of_
isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K] [hk : IsAlgClosed k] [A
lgebra k K] [Algebra.IsIntegral k K]…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
Schur's Lemma: If `V` is a representation of an algebra `A` over an algebraicall
y closed field
`k`, then any endomorphism of `V` is scalar.
-/
theorem IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed :
    Function.Bijective (algebraMap k (Module.End A V)) := by
  have : Module.Finite k (Module.End A V) := .of_injective (LinearMap.restrictScalarsₗ k A V V k) <|
    LinearMap.restrictScalars_injective _
  classical exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)

variable (A V)

open scoped IsMulCommutative in
/-- Any finite-dimensional irreducible representation of a commutative algebra over an algebraically
closed field is one-dimensional. -/
/-
**IsSimpleModule.finrank_eq_one_of_isMulCommutative** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsSimpleModule.finrank_eq_one_of_isMulCommutative [IsMulCommutative A] : M
odule.finrank k V = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleModule.nontrivial`：IsSimpleModule.nontrivial [IsSimpleModule R M
] : Nontrivial M
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`：IsSimpleModule.a
lgebraMap_end_bijective_of_isAlgClosed : Function.Bijective (algebraMap k (Modul
e.End A V))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `finrank_eq_one_iff_of_nonzero`：finrank_eq_one_iff_of_nonzero (v : V) (nz
 : v != 0) : finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ where mp h
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤

--- 原说明 ---
Any finite-dimensional irreducible representation of a commutative algebra over 
an algebraically
closed field is one-dimensional.
-/
theorem IsSimpleModule.finrank_eq_one_of_isMulCommutative [IsMulCommutative A] :
    Module.finrank k V = 1 := by
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, v_nz⟩ := exists_ne (0 : V)
  set U : Submodule A V := { Submodule.span k {v} with
    smul_mem' a w hw := by
      have ⟨t, ht⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2
        (Module.toModuleEnd A V a)
      simpa only [← show _ = a • w from congr($ht w)] using! (k ∙ v).smul_mem t hw }
  obtain hU | hU := eq_bot_or_eq_top U
  · exact (v_nz <| hU.le <| Submodule.mem_span_singleton_self v).elim
  · rw [finrank_eq_one_iff_of_nonzero v v_nz]
    rwa [← top_le_iff] at hU ⊢
