/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Definition of Brauer group of a field K

We introduce the definition of Brauer group of a field K, which is the quotient of the set of
all finite-dimensional central simple algebras over K modulo the Brauer Equivalence where two
central simple algebras `A` and `B` are Brauer Equivalent if there exist `n, m ∈ ℕ+` such
that `Mₙ(A) ≃ₐ[K] Mₘ(B)`.

## TODOs
1. Prove that the Brauer group is an abelian group where multiplication is defined as tensor
   product.
2. Prove that the Brauer group is a functor from the category of fields to the category of groups.
3. Prove that over a field, being Brauer equivalent is the same as being Morita equivalent.

## References
* [Algebraic Number Theory, *J.W.S Cassels*][cassels1967algebraic]

## Tags
Brauer group, Central simple algebra, Galois Cohomology
-/

@[expose] public section

universe u v

/--
Definition of `CSA` / `CSA` 的定义

English:
structure CSA
  parameters: (K : Type u) [Field K]
  extends: AlgCat.{v} K
  axioms and operations (3):
    - [isCentral : Algebra.IsCentral K carrier]
    - [isSimple : IsSimpleRing carrier]
    - [fin_dim : FiniteDimensional K carrier]

中文:
结构 CSA
  参数: (K : 类型u) [Field K]
  继承: AlgCat.{v} K
  公理与运算 (3 个):
    - [isCentral : Algebra.IsCentral K carrier]
    - [isSimple : IsSimpleRing carrier]
    - [fin_dim : FiniteDimensional K carrier]
-/
structure CSA (K : Type u) [Field K] extends AlgCat.{v} K where
  /-- Any member of `CSA` is central. -/
  [isCentral : Algebra.IsCentral K carrier]
  /-- Any member of `CSA` is simple. -/
  [isSimple : IsSimpleRing carrier]
  /-- Any member of `CSA` is finite-dimensional. -/
  [fin_dim : FiniteDimensional K carrier]

variable {K : Type u} [Field K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CSA.{u, v} K) (Type v)
  body: ⟨(·.carrier)⟩

中文:
实例 :
  签名: CoeSort (CSA.{u, v} K) (类型v)
  定义体: ⟨(·.carrier)⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (CSA.{u, v} K) (Type v) := ⟨(·.carrier)⟩

attribute [instance] CSA.isCentral CSA.isSimple CSA.fin_dim

/--
Definition of `IsBrauerEquivalent` / `IsBrauerEquivalent` 的定义

English:
abbreviation IsBrauerEquivalent
  signature: (A B : CSA K)
  body: exists n m : Nat, n != 0 ∧ m != 0 ∧ (Nonempty <| Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

中文:
缩写 IsBrauerEquivalent
  签名: (A B : CSA K)
  定义体: exists n m : Nat, n != 0 ∧ m != 0 ∧ (Nonempty <| Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

Depends on / 依赖: Matrix, Nonempty
-/
abbrev IsBrauerEquivalent (A B : CSA K) : Prop :=
  exists n m : Nat, n != 0 ∧ m != 0 ∧ (Nonempty <| Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

namespace IsBrauerEquivalent

@[refl]
/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (A : CSA K)
  statement: IsBrauerEquivalent A A
  proof: ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.refl⟩⟩

@[symm]

中文:
引理 refl
  条件: (A : CSA K)
  结论: IsBrauerEquivalent A A
  证明: ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.refl⟩⟩

@[symm]

Depends on / 依赖: AlgEquiv, AlgEquiv.refl, one_ne_zero
-/
lemma refl (A : CSA K) : IsBrauerEquivalent A A :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.refl⟩⟩

@[symm]
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: {A B : CSA K} (h : IsBrauerEquivalent A B)
  statement: IsBrauerEquivalent B A
  proof: let ⟨n, m, hn, hm, ⟨iso⟩⟩ := h
  ⟨m, n, hm, hn, ⟨iso.symm⟩⟩

中文:
引理 symm
  条件: {A B : CSA K} (h : IsBrauerEquivalent A B)
  结论: IsBrauerEquivalent B A
  证明: let ⟨n, m, hn, hm, ⟨iso⟩⟩ := h
  ⟨m, n, hm, hn, ⟨iso.symm⟩⟩

Depends on / 依赖: iso.symm
-/
lemma symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A :=
  let ⟨n, m, hn, hm, ⟨iso⟩⟩ := h
  ⟨m, n, hm, hn, ⟨iso.symm⟩⟩

open Matrix in
@[trans]
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C)
  proof: by
  obtain ⟨n, m, hn, hm, ⟨iso1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨iso2⟩⟩ := hBC
  exact ⟨p * n, m * q, by simp_all, by simp_all,
.symm.trans .symm.trans compAlgEquiv _ _ _ _ ⟨reindexAlgEquiv _ _ finProdFinEquiv
.trans .trans compAlgEquiv _ _ _ _ iso1.mapMatrix (m := Fin p)
.trans .symm.trans compAl

中文:
引理 trans
  条件: {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C)
  证明: by
  obtain ⟨n, m, hn, hm, ⟨iso1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨iso2⟩⟩ := hBC
  exact ⟨p * n, m * q, by simp_all, by simp_all,
.symm.trans .symm.trans compAlgEquiv _ _ _ _ ⟨reindexAlgEquiv _ _ finProdFinEquiv
.trans .trans compAlgEquiv _ _ _ _ iso1.mapMatrix (m := Fin p)
.trans .symm.trans compAl

Depends on / 依赖: compAlgEquiv, finProdFinEquiv, iso1.mapMatrix, iso2.mapMatrix.trans, mapMatrix, prodComm, reindexAlgEquiv, symm.trans
-/
lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, hn, hm, ⟨iso1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨iso2⟩⟩ := hBC
  exact ⟨p * n, m * q, by simp_all, by simp_all,
.symm.trans .symm.trans compAlgEquiv _ _ _ _ ⟨reindexAlgEquiv _ _ finProdFinEquiv
.trans .trans compAlgEquiv _ _ _ _ iso1.mapMatrix (m := Fin p)
.trans .symm.trans compAlgEquiv _ _ _ _ reindexAlgEquiv K B (.prodComm (Fin p) (Fin m))
iso2.mapMatrix.trans .trans reindexAlgEquiv _ _ finProdFinEquiv⟩⟩ compAlgEquiv _ _ _ _

/--
lemma `is_eqv` / 引理 `is_eqv`

English:
lemma is_eqv
  statement: Equivalence (IsBrauerEquivalent (K := K)) where
  proof: refl
  symm := symm
  trans := trans

中文:
引理 is_eqv
  结论: Equivalence (IsBrauerEquivalent (K := K)) where
  证明: refl
  symm := symm
  trans := trans
-/
lemma is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

variable (K)

/-- `CSA` equipped with Brauer Equivalence is indeed a setoid. -/
@[instance_reducible]
/--
Definition of `Brauer.CSA_Setoid` / `Brauer.CSA_Setoid` 的定义

English:
definition Brauer.CSA_Setoid
  signature: : Setoid (CSA K) where
  body: IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.is_eqv

中文:
定义 Brauer.CSA_Setoid
  签名: : Setoid (CSA K) where
  定义体: IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.is_eqv

Depends on / 依赖: IsBrauerEquivalent
-/
def Brauer.CSA_Setoid : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.is_eqv

/--
Definition of `BrauerGroup` / `BrauerGroup` 的定义

English:
abbreviation BrauerGroup
  body: Quotient (Brauer.CSA_Setoid K)

中文:
缩写 BrauerGroup
  定义体: Quotient (Brauer.CSA_Setoid K)

Depends on / 依赖: Brauer, Brauer.CSA_Setoid, CSA_Setoid, Quotient
-/
abbrev BrauerGroup := Quotient (Brauer.CSA_Setoid K)
