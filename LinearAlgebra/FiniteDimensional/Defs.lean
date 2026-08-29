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

/--
Definition of `FiniteDimensional` / `FiniteDimensional` 的定义

English:
abbreviation FiniteDimensional
  signature: (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
  body: Module.Finite K V

中文:
缩写 有限维
  签名: (K V : 类型) [除环 K] [加法交换群 V] [模 K V]
  定义体: Module.Finite K V

Depends on / 依赖: Finite, Module, Module.Finite
-/
abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V

variable {K : Type u} {V : Type v}

namespace FiniteDimensional
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: (f : V ->ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂]
  proof: Module.Finite.of_injective f w

中文:
定理 of_injective
  条件: (f : V ->ₗ[K] V₂) (w : 函数.单射 f) [有限维 K V₂]
  证明: Module.Finite.of_injective f w

Depends on / 依赖: Finite, Module, Module.Finite.of_injective, of_injective
-/
theorem of_injective (f : V ->ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] :
    FiniteDimensional K V :=
  Module.Finite.of_injective f w

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : V ->ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V]
  proof: Module.Finite.of_surjective f w

中文:
定理 of_surjective
  条件: (f : V ->ₗ[K] V₂) (w : 函数.满射 f) [有限维 K V]
  证明: Module.Finite.of_surjective f w

Depends on / 依赖: Finite, Module, Module.Finite.of_surjective, of_surjective
-/
theorem of_surjective (f : V ->ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w

variable (K V)

/--
Instance `finiteDimensional_pi` / 实例 `finiteDimensional_pi`

English:
instance finiteDimensional_pi
  signature: {ι : Type*} [Finite ι]
  body: Finite.pi

中文:
实例 finiteDimensional_pi
  签名: {ι : 类型} [有限 ι]
  定义体: Finite.pi

Depends on / 依赖: Finite, Finite.pi
-/
instance finiteDimensional_pi {ι : Type*} [Finite ι] : FiniteDimensional K (ι -> K) :=
  Finite.pi

/--
Instance `finiteDimensional_pi'` / 实例 `finiteDimensional_pi'`

English:
instance finiteDimensional_pi'
  signature: {ι : Type*} [Finite ι] (M : ι -> Type*) [forall i, AddCommGroup (M i)]
  body: Finite.pi

中文:
实例 finiteDimensional_pi'
  签名: {ι : 类型} [有限 ι] (M : ι -> 类型) [对任意 i, 加法交换群 (M i)]
  定义体: Finite.pi

Depends on / 依赖: Finite, Finite.pi
-/
instance finiteDimensional_pi' {ι : Type*} [Finite ι] (M : ι -> Type*) [forall i, AddCommGroup (M i)]
    [forall i, Module K (M i)] [forall i, FiniteDimensional K (M i)] : FiniteDimensional K (forall i, M i) :=
  Finite.pi

variable {K V}

/--
theorem `_root_.Module.Basis.finiteDimensional_of_finite` / 定理 `_root_.Module.Basis.finiteDimensional_of_finite`

English:
theorem _root_.Module.Basis.finiteDimensional_of_finite
  given: {ι : Type w} [Finite ι] (h : Basis ι K V)
  proof: Module.Finite.of_basis h

中文:
定理 _root_.模.基.finiteDimensional_of_finite
  条件: {ι : 类型 w} [有限 ι] (h : 基 ι K V)
  证明: Module.Finite.of_basis h

Depends on / 依赖: Finite, Module, Module.Finite.of_basis, of_basis
-/
theorem _root_.Module.Basis.finiteDimensional_of_finite {ι : Type w} [Finite ι] (h : Basis ι K V) :
    FiniteDimensional K V :=
  Module.Finite.of_basis h

/-- If a vector space is `FiniteDimensional`, all bases are indexed by a finite type -/
@[instance_reducible]
/--
Definition of `fintypeBasisIndex` / `fintypeBasisIndex` 的定义

English:
definition fintypeBasisIndex
  signature: {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V)
  body: @Fintype.ofFinite _ (Module.Finite.finite_basis b)

中文:
定义 fintypeBasisIndex
  签名: {ι : 类型} [有限维 K V] (b : 基 ι K V)
  定义体: @Fintype.ofFinite _ (Module.Finite.finite_basis b)

Depends on / 依赖: Finite, Fintype, Fintype.ofFinite, Module, Module.Finite.finite_basis, finite_basis, ofFinite
-/
noncomputable def fintypeBasisIndex {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V) :
    Fintype ι :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteDimensional
  signature: K V] : Fintype (Basis.ofVectorSpaceIndex K V)
  body: fintypeBasisIndex (Basis.ofVectorSpace K V)

中文:
实例 [有限维
  签名: K V] : 有限类型 (基.ofVectorSpaceIndex K V)
  定义体: fintypeBasisIndex (Basis.ofVectorSpace K V)

Depends on / 依赖: Basis.ofVectorSpace, fintypeBasisIndex, ofVectorSpace
-/
noncomputable instance [FiniteDimensional K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/--
theorem `of_finite_basis` / 定理 `of_finite_basis`

English:
theorem of_finite_basis
  given: {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s)
  proof: haveI := hs.fintype
  h.finiteDimensional_of_finite

中文:
定理 of_finite_basis
  条件: {ι : 类型 w} {s : 集合 ι} (h : 基 s K V) (hs : 集合.有限 s)
  证明: haveI := hs.fintype
  h.finiteDimensional_of_finite

Depends on / 依赖: finiteDimensional_of_finite, fintype, h.finiteDimensional_of_finite, hs.fintype
-/
theorem of_finite_basis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s) :
    FiniteDimensional K V :=
  haveI := hs.fintype
  h.finiteDimensional_of_finite

/--
Instance `finiteDimensional_submodule` / 实例 `finiteDimensional_submodule`

English:
instance finiteDimensional_submodule
  signature: [FiniteDimensional K V] (S : Submodule K V)
  body: by
  infer_instance

中文:
实例 finiteDimensional_submodule
  签名: [有限维 K V] (S : 子模 K V)
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance finiteDimensional_submodule [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K S := by
  infer_instance

/--
Instance `finiteDimensional_quotient` / 实例 `finiteDimensional_quotient`

English:
instance finiteDimensional_quotient
  signature: [FiniteDimensional K V] (S : Submodule K V)
  body: Module.Finite.quotient K S

中文:
实例 finiteDimensional_quotient
  签名: [有限维 K V] (S : 子模 K V)
  定义体: Module.Finite.quotient K S

Depends on / 依赖: Finite, Module, Module.Finite.quotient, quotient
-/
instance finiteDimensional_quotient [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K (V ⧸ S) :=
  Module.Finite.quotient K S

/--
theorem `of_finrank_pos` / 定理 `of_finrank_pos`

English:
theorem of_finrank_pos
  given: (h : 0 < finrank K V)
  statement: FiniteDimensional K V
  proof: Module.finite_of_finrank_pos h

中文:
定理 of_finrank_pos
  条件: (h : 0 < finrank K V)
  结论: 有限维 K V
  证明: Module.finite_of_finrank_pos h

Depends on / 依赖: Module, Module.finite_of_finrank_pos, finite_of_finrank_pos
-/
theorem of_finrank_pos (h : 0 < finrank K V) : FiniteDimensional K V :=
  Module.finite_of_finrank_pos h

/--
theorem `of_finrank_eq_succ` / 定理 `of_finrank_eq_succ`

English:
theorem of_finrank_eq_succ
  given: {n : Nat} (hn : finrank K V = n.succ)
  proof: Module.finite_of_finrank_eq_succ hn

中文:
定理 of_finrank_eq_succ
  条件: {n : 自然数} (hn : finrank K V = n.succ)
  证明: Module.finite_of_finrank_eq_succ hn

Depends on / 依赖: Module, Module.finite_of_finrank_eq_succ, finite_of_finrank_eq_succ
-/
theorem of_finrank_eq_succ {n : Nat} (hn : finrank K V = n.succ) :
    FiniteDimensional K V :=
  Module.finite_of_finrank_eq_succ hn

/--
theorem `of_fact_finrank_eq_succ` / 定理 `of_fact_finrank_eq_succ`

English:
theorem of_fact_finrank_eq_succ
  given: (n : Nat) [hn : Fact (finrank K V = n + 1)]
  proof: of_finrank_eq_succ hn.out

中文:
定理 of_fact_finrank_eq_succ
  条件: (n : 自然数) [hn : Fact (finrank K V = n + 1)]
  证明: of_finrank_eq_succ hn.out

Depends on / 依赖: hn.out, of_finrank_eq_succ
-/
theorem of_fact_finrank_eq_succ (n : Nat) [hn : Fact (finrank K V = n + 1)] :
    FiniteDimensional K V :=
  of_finrank_eq_succ hn.out

/--
lemma `of_fact_finrank_eq_two` / 引理 `of_fact_finrank_eq_two`

English:
lemma of_fact_finrank_eq_two
  given: [Fact (finrank K V = 2)]
  statement: FiniteDimensional K V
  proof: of_fact_finrank_eq_succ 1

中文:
引理 of_fact_finrank_eq_two
  条件: [Fact (finrank K V = 2)]
  结论: 有限维 K V
  证明: of_fact_finrank_eq_succ 1

Depends on / 依赖: of_fact_finrank_eq_succ
-/
lemma of_fact_finrank_eq_two [Fact (finrank K V = 2)] : FiniteDimensional K V :=
  of_fact_finrank_eq_succ 1

end FiniteDimensional

namespace Module

variable (K V)
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `finrank_eq_rank'` / 定理 `finrank_eq_rank'`

English:
theorem finrank_eq_rank'
  given: [FiniteDimensional K V]
  statement: (finrank K V : Cardinal.{v}) = Module.rank K V
  proof: finrank_eq_rank _ _

中文:
定理 finrank_eq_rank'
  条件: [有限维 K V]
  结论: (finrank K V : 基数.{v}) = 模.rank K V
  证明: finrank_eq_rank _ _

Depends on / 依赖: finrank_eq_rank
-/
theorem finrank_eq_rank' [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V :=
  finrank_eq_rank _ _

variable {K V}

/--
theorem `finrank_of_infinite_dimensional` / 定理 `finrank_of_infinite_dimensional`

English:
theorem finrank_of_infinite_dimensional
  given: (h : ¬FiniteDimensional K V)
  statement: finrank K V = 0
  proof: Module.finrank_of_not_finite h

中文:
定理 finrank_of_infinite_dimensional
  条件: (h : ¬有限维 K V)
  结论: finrank K V = 0
  证明: Module.finrank_of_not_finite h

Depends on / 依赖: Module, Module.finrank_of_not_finite, finrank_of_not_finite
-/
theorem finrank_of_infinite_dimensional (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  Module.finrank_of_not_finite h

/--
theorem `finiteDimensional_iff_of_rank_eq_nsmul` / 定理 `finiteDimensional_iff_of_rank_eq_nsmul`

English:
theorem finiteDimensional_iff_of_rank_eq_nsmul
  statement: {W} [AddCommGroup W] [Module K W] {n : Nat}
  proof: Module.finite_iff_of_rank_eq_nsmul hn hVW

中文:
定理 finiteDimensional_iff_of_rank_eq_nsmul
  结论: {W} [加法交换群 W] [模 K W] {n : 自然数}
  证明: Module.finite_iff_of_rank_eq_nsmul hn hVW

Depends on / 依赖: Module, Module.finite_iff_of_rank_eq_nsmul, finite_iff_of_rank_eq_nsmul
-/
theorem finiteDimensional_iff_of_rank_eq_nsmul {W} [AddCommGroup W] [Module K W] {n : Nat}
    (hn : n != 0) (hVW : Module.rank K V = n • Module.rank K W) :
    FiniteDimensional K V ↔ FiniteDimensional K W :=
  Module.finite_iff_of_rank_eq_nsmul hn hVW

/--
theorem `finrank_eq_card_basis'` / 定理 `finrank_eq_card_basis'`

English:
theorem finrank_eq_card_basis'
  given: [FiniteDimensional K V] {ι : Type w} (h : Basis ι K V)
  proof: Module.mk_finrank_eq_card_basis h

中文:
定理 finrank_eq_card_basis'
  条件: [有限维 K V] {ι : 类型 w} (h : 基 ι K V)
  证明: Module.mk_finrank_eq_card_basis h

Depends on / 依赖: Module, Module.mk_finrank_eq_card_basis, mk_finrank_eq_card_basis
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

/--
Instance `finiteDimensional_self` / 实例 `finiteDimensional_self`

English:
instance finiteDimensional_self
  signature: : FiniteDimensional K K
  body: inferInstance

中文:
实例 finiteDimensional_self
  签名: : 有限维 K K
  定义体: inferInstance
-/
instance finiteDimensional_self : FiniteDimensional K K := inferInstance

/--
theorem `span_of_finite` / 定理 `span_of_finite`

English:
theorem span_of_finite
  given: {A : Set V} (hA : Set.Finite A)
  statement: FiniteDimensional K (Submodule.span K A)
  proof: Module.Finite.span_of_finite K hA

中文:
定理 span_of_finite
  条件: {A : 集合 V} (hA : 集合.有限 A)
  结论: 有限维 K (子模.span K A)
  证明: Module.Finite.span_of_finite K hA

Depends on / 依赖: Finite, Module, Module.Finite.span_of_finite, span_of_finite
-/
theorem span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  Module.Finite.span_of_finite K hA

/--
Instance `span_singleton` / 实例 `span_singleton`

English:
instance span_singleton
  signature: (x : V)
  body: Module.Finite.span_singleton K x

中文:
实例 span_singleton
  签名: (x : V)
  定义体: Module.Finite.span_singleton K x

Depends on / 依赖: Finite, Module, Module.Finite.span_singleton, span_singleton
-/
instance span_singleton (x : V) : FiniteDimensional K (K ∙ x) :=
  Module.Finite.span_singleton K x

/--
Instance `span_finset` / 实例 `span_finset`

English:
instance span_finset
  signature: (s : Finset V)
  body: Module.Finite.span_finset K s

中文:
实例 span_finset
  签名: (s : 有限集 V)
  定义体: Module.Finite.span_finset K s

Depends on / 依赖: Finite, Module, Module.Finite.span_finset, span_finset
-/
instance span_finset (s : Finset V) : FiniteDimensional K (span K (s : Set V)) :=
  Module.Finite.span_finset K s

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V ->ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
    FiniteDimensional K (p.map f) :=
  Module.Finite.map _ _

end DivisionRing

section Tower

variable (F K A : Type*) [DivisionRing F] [DivisionRing K] [AddCommGroup A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: [FiniteDimensional F K] [FiniteDimensional K A]
  statement: FiniteDimensional F A
  proof: Module.Finite.trans K A

中文:
定理 trans
  条件: [有限维 F K] [有限维 K A]
  结论: 有限维 F A
  证明: Module.Finite.trans K A

Depends on / 依赖: Finite, Module, Module.Finite.trans
-/
theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
  Module.Finite.trans K A

end Tower

end FiniteDimensional

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `fg_iff_finiteDimensional` / 定理 `fg_iff_finiteDimensional`

English:
theorem fg_iff_finiteDimensional
  given: (s : Submodule K V)
  statement: s.FG ↔ FiniteDimensional K s
  proof: Module.Finite.iff_fg.symm

中文:
定理 fg_iff_finiteDimensional
  条件: (s : 子模 K V)
  结论: s.FG ↔ 有限维 K s
  证明: Module.Finite.iff_fg.symm

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg.symm, iff_fg
-/
theorem fg_iff_finiteDimensional (s : Submodule K V) : s.FG ↔ FiniteDimensional K s :=
  Module.Finite.iff_fg.symm

end DivisionRing

end Submodule

namespace LinearEquiv

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `finiteDimensional` / 定理 `finiteDimensional`

English:
theorem finiteDimensional
  given: (f : V ≃ₗ[K] V₂) [FiniteDimensional K V]
  proof: Module.Finite.equiv f

中文:
定理 finiteDimensional
  条件: (f : V ≃ₗ[K] V₂) [有限维 K V]
  证明: Module.Finite.equiv f
-/
protected theorem finiteDimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.equiv f

end LinearEquiv
