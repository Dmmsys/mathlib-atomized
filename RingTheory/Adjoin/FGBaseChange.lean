/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Adjoin.FG

/-!
# Finitely generated subalgebras of a base change obtained from an element

## Main results
- `exists_fg_and_mem_baseChange`: given an element `x` of a tensor product `A ⊗[R] B` of two
  `R`-algebras `A` and `B`, there exists a finitely generated subalgebra `C` of `B` such that `x`
  is contained in `C ⊗[R] B`.

-/

public section

open TensorProduct

/-
**exists_fg_and_mem_baseChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_fg_and_mem_baseChange {R A B : Type*} [CommSemiring R] [CommSemirin
g A] [Semiring B] [Algebra R A] [Algebra R B] (x : A otimes[R] B) : exists C : S
ubalgebra R B, C.FG ∧ x in C.baseChange A
参数：x : A otimes[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.exists_finset`：exists_finset (x : M otimes[R] N) : exists 
S : Finset (M × N), x = S.sum fun i => i.1 otimesₜ[R] i.2
· 使用定理 `Subalgebra.fg_adjoin_finset`：fg_adjoin_finset (s : Finset A) : (Algebra.
adjoin R (↑s : Set A)).FG
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
· 使用引理 `Subalgebra.tmul_mem_baseChange`：Subalgebra.tmul_mem_baseChange {x : A} (
hx : x in C) (b : B) : b otimesₜ[R] x in C.baseChange B
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_fg_and_mem_baseChange {R A B : Type*} [CommSemiring R]
    [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (x : A ⊗[R] B) :
    ∃ C : Subalgebra R B, C.FG ∧ x ∈ C.baseChange A := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨Algebra.adjoin R (S.image fun j ↦ j.2), ?_, ?_⟩
  · exact Subalgebra.fg_adjoin_finset _
  · exact hS ▸ Subalgebra.sum_mem _ fun s hs ↦ (Subalgebra.tmul_mem_baseChange
      (Algebra.subset_adjoin (Finset.mem_image_of_mem _ hs)) s.1)
