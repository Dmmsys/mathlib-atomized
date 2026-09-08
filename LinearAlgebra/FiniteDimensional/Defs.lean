/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Finite-dimensional vector spaces

This file defines finite-dimensional vector spaces and shows our definition is equivalent to
alternative definitions.

## Main definitions

Assume `V` is a vector space over a division ring `K`. There are (at least) three equivalent
definitions of finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is Noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `FiniteDimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the second point of view, i.e., as `Module.Finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `FiniteDimensional`):

- `Module.finBasis` and `Module.finBasisOfFinrankEq`
  are bases for finite-dimensional vector spaces, where the index type
  is `Fin` (in `Mathlib/LinearAlgebra/Dimension/Free.lean`)
- `fintypeBasisIndex` states that a finite-dimensional
  vector space has a finite basis
- `Module.Basis.finiteDimensional_of_finite` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `of_finrank_pos` states that a nonzero `finrank` (implying non-infinite dimension)
  implies finite-dimensionality
- `IsNoetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is Noetherian (in `Mathlib/FieldTheory/Finiteness.lean`)

We make use of `finrank`, the dimension of a finite-dimensional space, returning a `Nat`, as
opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`. `finrank` is not defined using `FiniteDimensional`.
For basic results that do not need the `FiniteDimensional` class, import
`Mathlib/LinearAlgebra/Dimension/Finrank.lean`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- linear equivs, in `LinearEquiv.finiteDimensional`

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general finitely generated modules (see
`Mathlib/RingTheory/Finiteness/Basic.lean`) or Noetherian modules (see
`Mathlib/RingTheory/Noetherian/Basic.lean`).
-/

@[expose] public section

assert_not_exists Module.Projective Subalgebra

universe u v v' w

open Cardinal Module Submodule

/-- `FiniteDimensional` vector spaces are defined to be finite modules.
Use `Module.Basis.finiteDimensional_of_finite` to prove finite dimension from another definition. -/
/-
**FiniteDimensional** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module 
K V]
参数：K V : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FiniteDimensional` vector spaces are defined to be finite modules.
Use `Module.Basis.finiteDimensional_of_finite` to prove finite dimension from an
other definition.
-/
abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V

variable {K : Type u} {V : Type v}

namespace FiniteDimensional
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- If the codomain of an injective linear map is finite dimensional, the domain must be as well. -/
/-
**FiniteDimensional.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`。
形式化陈述：of_injective (f : V ->ₗ[K] V₂) (w : Function.Injective f) [FiniteDimension
al K V₂] : FiniteDimensional K V
参数：f : V ->ₗ[K] V₂；w : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
If the codomain of an injective linear map is finite dimensional, the domain mus
t be as well.
-/
theorem of_injective (f : V →ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] :
    FiniteDimensional K V :=
  Module.Finite.of_injective f w

/-- If the domain of a surjective linear map is finite dimensional, the codomain must be as well. -/
/-
**FiniteDimensional.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`。
形式化陈述：of_surjective (f : V ->ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensi
onal K V] : FiniteDimensional K V₂
参数：f : V ->ₗ[K] V₂；w : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P

--- 原说明 ---
If the domain of a surjective linear map is finite dimensional, the codomain mus
t be as well.
-/
theorem of_surjective (f : V →ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w

variable (K V)
/-
**FiniteDimensional.finiteDimensional_pi** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDimens
ional`。
形式化陈述：finiteDimensional_pi {ι : Type*} [Finite ι] : FiniteDimensional K (ι -> K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finiteDimensional_pi {ι : Type*} [Finite ι] : FiniteDimensional K (ι → K) :=
  Finite.pi
/-
**FiniteDimensional.finiteDimensional_pi'** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDimen
sional`。
形式化陈述：finiteDimensional_pi' {ι : Type*} [Finite ι] (M : ι -> Type*) [forall i, A
ddCommGroup (M i)] [forall i, Module K (M i)] [forall i, FiniteDimensional K (M 
i)] : FiniteDimensional K (forall i, M i)
参数：M : ι -> Type*；M i；M i；M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finiteDimensional_pi' {ι : Type*} [Finite ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)] : FiniteDimensional K (∀ i, M i) :=
  Finite.pi

variable {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
/-
**FiniteDimensional._root_.Module.Basis.finiteDimensional_of_finite** 是 Mathlib 
中的一个定理，位于命名空间 `FiniteDimensional`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a vector space has a finite basis, then it is finite-dimensional.
-/
theorem _root_.Module.Basis.finiteDimensional_of_finite {ι : Type w} [Finite ι] (h : Basis ι K V) :
    FiniteDimensional K V :=
  Module.Finite.of_basis h

/-- If a vector space is `FiniteDimensional`, all bases are indexed by a finite type -/
@[instance_reducible]
/-
**FiniteDimensional.fintypeBasisIndex** 是 Mathlib 中的一个定义，位于命名空间 `FiniteDimension
al`。
形式化陈述：fintypeBasisIndex {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V) : 
Fintype ι
参数：b : Basis ι K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a vector space is `FiniteDimensional`, all bases are indexed by a finite type
-/
noncomputable def fintypeBasisIndex {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V) :
    Fintype ι :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis b)

/-- If a vector space is `FiniteDimensional`, `Basis.ofVectorSpace` is indexed by
  a finite type. -/
/-
**FiniteDimensional.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDimensional`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a vector space is `FiniteDimensional`, `Basis.ofVectorSpace` is indexed by
  a finite type.
-/
noncomputable instance [FiniteDimensional K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
/-
**FiniteDimensional.of_finite_basis** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional
`。
形式化陈述：of_finite_basis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finit
e s) : FiniteDimensional K V
参数：h : Basis s K V；hs : Set.Finite s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional.
-/
theorem of_finite_basis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s) :
    FiniteDimensional K V :=
  haveI := hs.fintype
  h.finiteDimensional_of_finite

/-- A subspace of a finite-dimensional space is also finite-dimensional.

This is a shortcut instance to simplify inference in the presence of `[FiniteDimensional K V]`.
-/
/-
**FiniteDimensional.finiteDimensional_submodule** 是 Mathlib 中的一个实例，位于命名空间 `Finit
eDimensional`。
形式化陈述：finiteDimensional_submodule [FiniteDimensional K V] (S : Submodule K V) : 
FiniteDimensional K S
参数：S : Submodule K V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
A subspace of a finite-dimensional space is also finite-dimensional.

This is a shortcut instance to simplify inference in the presence of `[FiniteDim
ensional K V]`.
-/
instance finiteDimensional_submodule [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K S := by
  infer_instance

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
/-
**FiniteDimensional.finiteDimensional_quotient** 是 Mathlib 中的一个实例，位于命名空间 `Finite
Dimensional`。
形式化陈述：finiteDimensional_quotient [FiniteDimensional K V] (S : Submodule K V) : F
initeDimensional K (V ⧸ S)
参数：S : Submodule K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quotient of a finite-dimensional space is also finite-dimensional.
-/
instance finiteDimensional_quotient [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K (V ⧸ S) :=
  Module.Finite.quotient K S
/-
**FiniteDimensional.of_finrank_pos** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`
。
形式化陈述：of_finrank_pos (h : 0 < finrank K V) : FiniteDimensional K V
参数：h : 0 < finrank K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem of_finrank_pos (h : 0 < finrank K V) : FiniteDimensional K V :=
  Module.finite_of_finrank_pos h
/-
**FiniteDimensional.of_finrank_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensio
nal`。
形式化陈述：of_finrank_eq_succ {n : Nat} (hn : finrank K V = n.succ) : FiniteDimension
al K V
参数：hn : finrank K V = n.succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finrank_eq_succ`：finite_of_finrank_eq_succ {n : Nat} (h
n : finrank R M = n.succ) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) :
    FiniteDimensional K V :=
  Module.finite_of_finrank_eq_succ hn

/-- We can infer `FiniteDimensional K V` in the presence of `[Fact (finrank K V = n + 1)]`.
Use `have : FiniteDimensional K V := .of_fact_finrank_eq_succ` when needed.

This is not an instance because `n` cannot be inferred.
-/
/-
**FiniteDimensional.of_fact_finrank_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDim
ensional`。
形式化陈述：of_fact_finrank_eq_succ (n : Nat) [hn : Fact (finrank K V = n + 1)] : Fini
teDimensional K V
参数：n : Nat；finrank K V = n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
We can infer `FiniteDimensional K V` in the presence of `[Fact (finrank K V = n 
+ 1)]`.
Use `have : FiniteDimensional K V := .of_fact_finrank_eq_succ` when needed.

This is not an instance because `n` cannot be inferred.
-/
theorem of_fact_finrank_eq_succ (n : ℕ) [hn : Fact (finrank K V = n + 1)] :
    FiniteDimensional K V :=
  of_finrank_eq_succ hn.out
/-
**FiniteDimensional.of_fact_finrank_eq_two** 是 Mathlib 中的一个引理，位于命名空间 `FiniteDime
nsional`。
形式化陈述：of_fact_finrank_eq_two [Fact (finrank K V = 2)] : FiniteDimensional K V
参数：finrank K V = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_fact_finrank_eq_succ`：of_fact_finrank_eq_succ (n : 
Nat) [hn : Fact (finrank K V = n + 1)] : FiniteDimensional K V
-/
lemma of_fact_finrank_eq_two [Fact (finrank K V = 2)] : FiniteDimensional K V :=
  of_fact_finrank_eq_succ 1

end FiniteDimensional

namespace Module

variable (K V)
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. This is a copy of `finrank_eq_rank _ _` which creates easier typeclass searches. -/
/-
**Module.finrank_eq_rank'** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_rank' [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = 
Module.rank K V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
In a finite-dimensional space, its dimension (seen as a cardinal) coincides with
 its
`finrank`. This is a copy of `finrank_eq_rank _ _` which creates easier typeclas
s searches.
-/
theorem finrank_eq_rank' [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V :=
  finrank_eq_rank _ _

variable {K V}
/-
**Module.finrank_of_infinite_dimensional** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_of_infinite_dimensional (h : ¬FiniteDimensional K V) : finrank K V
 = 0
参数：h : ¬FiniteDimensional K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_of_not_finite`：finrank_of_not_finite (h : ¬Module.Finite 
R M) : finrank R M = 0
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem finrank_of_infinite_dimensional (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  Module.finrank_of_not_finite h
/-
**Module.finiteDimensional_iff_of_rank_eq_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e`。
形式化陈述：finiteDimensional_iff_of_rank_eq_nsmul {W} [AddCommGroup W] [Module K W] {
n : Nat} (hn : n != 0) (hVW : Module.rank K V = n • Module.rank K W) : FiniteDim
ensional K V ↔ FiniteDimensional K W
参数：hn : n != 0；hVW : Module.rank K V = n • Module.rank K W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_iff_of_rank_eq_nsmul`：finite_iff_of_rank_eq_nsmul {W} [Add
CommMonoid W] [Module R W] [Module.Free R W] {n : Nat} (hn : n != 0) (hVW : Modu
le.rank R M = n • Module…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem finiteDimensional_iff_of_rank_eq_nsmul {W} [AddCommGroup W] [Module K W] {n : ℕ}
    (hn : n ≠ 0) (hVW : Module.rank K V = n • Module.rank K W) :
    FiniteDimensional K V ↔ FiniteDimensional K W :=
  Module.finite_iff_of_rank_eq_nsmul hn hVW

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
/-
**Module.finrank_eq_card_basis'** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_card_basis' [FiniteDimensional K V] {ι : Type w} (h : Basis ι K
 V) : (finrank K V : Cardinal.{w}) = #ι
参数：h : Basis ι K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.mk_finrank_eq_card_basis`：mk_finrank_eq_card_basis [Module.Finite
 R M] {ι : Type w} (h : Basis ι R M) : (finrank R M : Cardinal.{w}) = #ι
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
If a vector space is finite-dimensional, then the cardinality of any basis is eq
ual to its
`finrank`.
-/
theorem finrank_eq_card_basis' [FiniteDimensional K V] {ι : Type w} (h : Basis ι K V) :
    (finrank K V : Cardinal.{w}) = #ι :=
  Module.mk_finrank_eq_card_basis h

end Module

namespace FiniteDimensional
section DivisionRing
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

variable (K)

/-
**FiniteDimensional.finiteDimensional_self** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDime
nsional`。
形式化陈述：finiteDimensional_self : FiniteDimensional K K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finiteDimensional_self : FiniteDimensional K K := inferInstance

/-- The submodule generated by a finite set is finite-dimensional. -/
/-
**FiniteDimensional.span_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`
。
形式化陈述：span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Subm
odule.span K A)
参数：hA : Set.Finite A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.span_of_finite`：span_of_finite {A : Set M} (hA : Set.Finit
e A) : Module.Finite R (span R A)

--- 原说明 ---
The submodule generated by a finite set is finite-dimensional.
-/
theorem span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  Module.Finite.span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
/-
**FiniteDimensional.span_singleton** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDimensional`
。
形式化陈述：span_singleton (x : V) : FiniteDimensional K (K ∙ x)
参数：x : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule generated by a single element is finite-dimensional.
-/
instance span_singleton (x : V) : FiniteDimensional K (K ∙ x) :=
  Module.Finite.span_singleton K x

/-- The submodule generated by a finset is finite-dimensional. -/
/-
**FiniteDimensional.span_finset** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDimensional`。
形式化陈述：span_finset (s : Finset V) : FiniteDimensional K (span K (s : Set V))
参数：s : Finset V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule generated by a finset is finite-dimensional.
-/
instance span_finset (s : Finset V) : FiniteDimensional K (span K (s : Set V)) :=
  Module.Finite.span_finset K s

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
/-
**FiniteDimensional.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteDimensional`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforwards of finite-dimensional submodules are finite-dimensional.
-/
instance (f : V →ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
    FiniteDimensional K (p.map f) :=
  Module.Finite.map _ _

end DivisionRing

section Tower

variable (F K A : Type*) [DivisionRing F] [DivisionRing K] [AddCommGroup A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]

/-
**FiniteDimensional.trans** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`。
形式化陈述：trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional 
F A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
-/
theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
  Module.Finite.trans K A

end Tower

end FiniteDimensional

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
/-
**Submodule.fg_iff_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_iff_finiteDimensional (s : Submodule K V) : s.FG ↔ FiniteDimensional K 
s
参数：s : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG

--- 原说明 ---
A submodule is finitely generated if and only if it is finite-dimensional
-/
theorem fg_iff_finiteDimensional (s : Submodule K V) : s.FG ↔ FiniteDimensional K s :=
  Module.Finite.iff_fg.symm

end DivisionRing

end Submodule

namespace LinearEquiv

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- Finite dimensionality is preserved under linear equivalence. -/
/-
**LinearEquiv.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup
 V] [inst_2 : _root_.Module K V]   {V₂ : Type v'} [inst_3 : AddCommGroup V₂] [in
st_4 : _root_.Module K V₂] (f : V ≃ₗ[K] V₂) [FiniteDimensional K V],   FiniteDim
ensional K V₂
参数：f : V ≃ₗ[K] V₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N

--- 原说明 ---
Finite dimensionality is preserved under linear equivalence.
-/
protected theorem finiteDimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.equiv f

end LinearEquiv

