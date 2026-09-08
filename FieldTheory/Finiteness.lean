/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A module over a division ring is Noetherian if and only if it is finite.

-/

@[expose] public section


universe u v

open Cardinal Submodule Module Function

namespace IsNoetherian

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A module over a division ring is Noetherian if and only if
its dimension (as a cardinal) is strictly less than the first infinite cardinal `ℵ₀`.
-/
/-
**IsNoetherian.iff_rank_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `IsNoetherian`。
形式化陈述：iff_rank_lt_aleph0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Cardinal.lt_aleph0_iff_set_finite`：lt_aleph0_iff_set_finite {S : Set α} 
: #S < ℵ₀ ↔ S.Finite
· 使用定理 `LinearIndependent.set_finite_of_isNoetherian`：LinearIndependent.set_fini
te_of_isNoetherian [Nontrivial R] {s : Set M} (hi : LinearIndependent R ((↑) : s
 -> M)) : s.Finite
· 使用定理 `Module.Basis.ofVectorSpaceIndex.linearIndependent`：∀ (K : Type u_3) (V :
 Type u_4) [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Mo
dule K V],   LinearIndependent K Subtyp…
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
· 使用定理 `isNoetherian_of_fg_of_noetherian`：isNoetherian_of_fg_of_noetherian {R M}
 [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) [I : IsNoetherianRin
g R] (hN : N.FG) : IsN…
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Module.Basis.coe_ofVectorSpace`：coe_ofVectorSpace : ⇑(ofVectorSpace K V)
 = ((↑) : _ -> _)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s

--- 原说明 ---
A module over a division ring is Noetherian if and only if
its dimension (as a cardinal) is strictly less than the first infinite cardinal 
`ℵ₀`.
-/
theorem iff_rank_lt_aleph0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀ := by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_rank'', lt_aleph0_iff_set_finite]
  constructor
  · intro
    exact (Basis.ofVectorSpaceIndex.linearIndependent K V).set_finite_of_isNoetherian
  · intro hbfinite
    refine
      @isNoetherian_of_linearEquiv K K (⊤ : Submodule K V) V _ _ _ _ _ _ (RingHom.id K) _ _ _
        (LinearEquiv.ofTop _ rfl) (id ?_)
    refine isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, ?_⟩
    rw [Set.Finite.coe_toFinset, ← b.span_eq, Basis.coe_ofVectorSpace, Subtype.range_coe]

/-- In a Noetherian module over a division ring, all bases are indexed by a finite type. -/
@[instance_reducible]
/-
**IsNoetherian.fintypeBasisIndex** 是 Mathlib 中的一个定义，位于命名空间 `IsNoetherian`。
形式化陈述：fintypeBasisIndex {ι : Type*} [IsNoetherian K V] (b : Basis ι K V) : Finty
pe ι
参数：b : Basis ι K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a Noetherian module over a division ring, all bases are indexed by a finite t
ype.
-/
noncomputable def fintypeBasisIndex {ι : Type*} [IsNoetherian K V] (b : Basis ι K V) : Fintype ι :=
  b.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K V)

/-- In a Noetherian module over a division ring,
`Basis.ofVectorSpace` is indexed by a finite type. -/
/-
**IsNoetherian.** 是 Mathlib 中的一个实例，位于命名空间 `IsNoetherian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a Noetherian module over a division ring,
`Basis.ofVectorSpace` is indexed by a finite type.
-/
noncomputable instance [IsNoetherian K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/-- In a Noetherian module over a division ring,
if a basis is indexed by a set, that set is finite. -/
/-
**IsNoetherian.finite_basis_index** 是 Mathlib 中的一个定理，位于命名空间 `IsNoetherian`。
形式化陈述：finite_basis_index {ι : Type*} {s : Set ι} [IsNoetherian K V] (b : Basis s
 K V) : s.Finite
参数：b : Basis s K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finite_index_of_rank_lt_aleph0`：Module.Basis.finite_index_o
f_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M) (h : Module.rank R M 
< ℵ₀) : s.Finite
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…

--- 原说明 ---
In a Noetherian module over a division ring,
if a basis is indexed by a set, that set is finite.
-/
theorem finite_basis_index {ι : Type*} {s : Set ι} [IsNoetherian K V] (b : Basis s K V) :
    s.Finite :=
  b.finite_index_of_rank_lt_aleph0 (rank_lt_aleph0 K V)

variable (K V)

/-- In a Noetherian module over a division ring,
there exists a finite basis. This is the indexing `Finset`. -/
/-
**IsNoetherian.finsetBasisIndex** 是 Mathlib 中的一个定义，位于命名空间 `IsNoetherian`。
形式化陈述：finsetBasisIndex [IsNoetherian K V] : Finset V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a Noetherian module over a division ring,
there exists a finite basis. This is the indexing `Finset`.
-/
noncomputable def finsetBasisIndex [IsNoetherian K V] : Finset V :=
  (finite_basis_index (Basis.ofVectorSpace K V)).toFinset

@[simp]
/-
**IsNoetherian.coe_finsetBasisIndex** 是 Mathlib 中的一个定理，位于命名空间 `IsNoetherian`。
形式化陈述：coe_finsetBasisIndex [IsNoetherian K V] : (↑(finsetBasisIndex K V) : Set V
) = Basis.ofVectorSpaceIndex K V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem coe_finsetBasisIndex [IsNoetherian K V] :
    (↑(finsetBasisIndex K V) : Set V) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coe_toFinset _

@[simp]
/-
**IsNoetherian.coeSort_finsetBasisIndex** 是 Mathlib 中的一个定理，位于命名空间 `IsNoetherian`
。
形式化陈述：coeSort_finsetBasisIndex [IsNoetherian K V] : (finsetBasisIndex K V : Type
 _) = Basis.ofVectorSpaceIndex K V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.coeSort_toFinset`：coeSort_toFinset : ↥hs.toFinset = ↥s
-/
theorem coeSort_finsetBasisIndex [IsNoetherian K V] :
    (finsetBasisIndex K V : Type _) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coeSort_toFinset _

/-- In a Noetherian module over a division ring, there exists a finite basis.
This is indexed by the `Finset` `IsNoetherian.finsetBasisIndex`.
This is in contrast to the result `finite_basis_index (Basis.ofVectorSpace K V)`,
which provides a set and a `Set.Finite`.
-/
/-
**IsNoetherian.finsetBasis** 是 Mathlib 中的一个定义，位于命名空间 `IsNoetherian`。
形式化陈述：finsetBasis [IsNoetherian K V] : Basis (finsetBasisIndex K V) K V
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
In a Noetherian module over a division ring, there exists a finite basis.
This is indexed by the `Finset` `IsNoetherian.finsetBasisIndex`.
This is in contrast to the result `finite_basis_index (Basis.ofVectorSpace K V)`
,
which provides a set and a `Set.Finite`.
-/
noncomputable def finsetBasis [IsNoetherian K V] : Basis (finsetBasisIndex K V) K V :=
  (Basis.ofVectorSpace K V).reindex (by rw [coeSort_finsetBasisIndex])

@[simp]
/-
**IsNoetherian.range_finsetBasis** 是 Mathlib 中的一个定理，位于命名空间 `IsNoetherian`。
形式化陈述：range_finsetBasis [IsNoetherian K V] : Set.range (finsetBasis K V) = Basis
.ofVectorSpaceIndex K V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNoetherian.finsetBasis.eq_1`：∀ (K : Type u) (V : Type v) [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : Is
Noetherian K V],   …
· 使用定理 `Module.Basis.range_reindex`：range_reindex : Set.range (b.reindex e) = Se
t.range b
· 使用定理 `Module.Basis.range_ofVectorSpace`：range_ofVectorSpace : range (ofVectorS
pace K V) = ofVectorSpaceIndex K V
-/
theorem range_finsetBasis [IsNoetherian K V] :
    Set.range (finsetBasis K V) = Basis.ofVectorSpaceIndex K V := by
  rw [finsetBasis, Basis.range_reindex, Basis.range_ofVectorSpace]

variable {K V}
/-
**IsNoetherian._root_.Module.card_eq_pow_finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsNo
etherian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.card_eq_pow_finrank [Fintype K] [Fintype V] :
    Fintype.card V = Fintype.card K ^ Module.finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b, ← Module.finrank_eq_card_basis b]
/-
**IsNoetherian._root_.Module.natCard_eq_pow_finrank** 是 Mathlib 中的一个定理，位于命名空间 `I
sNoetherian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.natCard_eq_pow_finrank [Module.Finite K V] :
    Nat.card V = Nat.card K ^ finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, finrank_eq_nat_card_basis b]

/-- A module over a division ring is Noetherian if and only if it is finitely generated. -/
/-
**IsNoetherian.iff_fg** 是 Mathlib 中的一个定理，位于命名空间 `IsNoetherian`。
形式化陈述：iff_fg : IsNoetherian K V ↔ Module.Finite K V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
A module over a division ring is Noetherian if and only if it is finitely genera
ted.
-/
theorem iff_fg : IsNoetherian K V ↔ Module.Finite K V :=
  ⟨fun _ ↦ IsNoetherian.finite _ _, fun _ ↦ isNoetherian_of_isNoetherianRing_of_finite _ _⟩

end IsNoetherian

