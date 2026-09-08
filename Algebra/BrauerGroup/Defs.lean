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

/-- `CSA` is the set of all finite-dimensional central simple algebras over a field `K`. For the
generalization to a `CommRing`, see `IsAzumaya` in `Mathlib/Algebra/Azumaya/Defs.lean`. -/
/-
**CSA** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u) → [Field K] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CSA` is the set of all finite-dimensional central simple algebras over a field 
`K`. For the
generalization to a `CommRing`, see `IsAzumaya` in `Mathlib/Algebra/Azumaya/Defs
.lean`.
-/
structure CSA (K : Type u) [Field K] extends AlgCat.{v} K where
  /-- Any member of `CSA` is central. -/
  [isCentral : Algebra.IsCentral K carrier]
  /-- Any member of `CSA` is simple. -/
  [isSimple : IsSimpleRing carrier]
  /-- Any member of `CSA` is finite-dimensional. -/
  [fin_dim : FiniteDimensional K carrier]

variable {K : Type u} [Field K]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CSA.{u, v} K) (Type v) := ⟨(·.carrier)⟩

attribute [instance] CSA.isCentral CSA.isSimple CSA.fin_dim

/-- Two finite-dimensional central simple algebras `A` and `B` are Brauer equivalent
  if there exist `n, m ∈ ℕ+` such that `Mₙ(A) ≃ₐ[K] Mₘ(B)`. -/
/-
**IsBrauerEquivalent** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsBrauerEquivalent (A B : CSA K) : Prop
参数：A B : CSA K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two finite-dimensional central simple algebras `A` and `B` are Brauer equivalent
  if there exist `n, m ∈ ℕ+` such that `Mₙ(A) ≃ₐ[K] Mₘ(B)`.
-/
abbrev IsBrauerEquivalent (A B : CSA K) : Prop :=
  ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧ (Nonempty <| Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

namespace IsBrauerEquivalent

@[refl]
/-
**IsBrauerEquivalent.refl** 是 Mathlib 中的一个引理，位于命名空间 `IsBrauerEquivalent`。
形式化陈述：refl (A : CSA K) : IsBrauerEquivalent A A
参数：A : CSA K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma refl (A : CSA K) : IsBrauerEquivalent A A :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.refl⟩⟩

@[symm]
/-
**IsBrauerEquivalent.symm** 是 Mathlib 中的一个引理，位于命名空间 `IsBrauerEquivalent`。
形式化陈述：symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A
参数：h : IsBrauerEquivalent A B。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A :=
  let ⟨n, m, hn, hm, ⟨iso⟩⟩ := h
  ⟨m, n, hm, hn, ⟨iso.symm⟩⟩

open Matrix in
@[trans]
/-
**IsBrauerEquivalent.trans** 是 Mathlib 中的一个引理，位于命名空间 `IsBrauerEquivalent`。
形式化陈述：trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquiva
lent B C) : IsBrauerEquivalent A C
参数：hAB : IsBrauerEquivalent A B；hBC : IsBrauerEquivalent B C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, hn, hm, ⟨iso1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨iso2⟩⟩ := hBC
  exact ⟨p * n, m * q, by simp_all, by simp_all,
    ⟨reindexAlgEquiv _ _ finProdFinEquiv |>.symm.trans <| compAlgEquiv _ _ _ _|>.symm.trans <|
    iso1.mapMatrix (m := Fin p)|>.trans <| compAlgEquiv _ _ _ _|>.trans <|
    reindexAlgEquiv K B (.prodComm (Fin p) (Fin m))|>.trans <| compAlgEquiv _ _ _ _|>.symm.trans <|
    iso2.mapMatrix.trans <| compAlgEquiv _ _ _ _|>.trans <| reindexAlgEquiv _ _ finProdFinEquiv⟩⟩
/-
**IsBrauerEquivalent.is_eqv** 是 Mathlib 中的一个引理，位于命名空间 `IsBrauerEquivalent`。
形式化陈述：is_eqv : Equivalence (IsBrauerEquivalent (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBrauerEquivalent.refl`：refl (A : CSA K) : IsBrauerEquivalent A A
· 使用引理 `IsBrauerEquivalent.symm`：symm {A B : CSA K} (h : IsBrauerEquivalent A B)
 : IsBrauerEquivalent B A
· 使用引理 `IsBrauerEquivalent.trans`：trans {A B C : CSA K} (hAB : IsBrauerEquivalen
t A B) (hBC : IsBrauerEquivalent B C) : IsBrauerEquivalent A C
-/
lemma is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

variable (K)

/-- `CSA` equipped with Brauer Equivalence is indeed a setoid. -/
@[instance_reducible]
/-
**Brauer.CSA_Setoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Brauer.CSA_Setoid : Setoid (CSA K) where r
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsBrauerEquivalent.is_eqv`：is_eqv : Equivalence (IsBrauerEquivalent (K

--- 原说明 ---
`CSA` equipped with Brauer Equivalence is indeed a setoid.
-/
def Brauer.CSA_Setoid : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.is_eqv

/-- `BrauerGroup` is the set of all finite-dimensional central simple algebras quotient
  by Brauer Equivalence. -/
/-
**BrauerGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：BrauerGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BrauerGroup` is the set of all finite-dimensional central simple algebras quoti
ent
  by Brauer Equivalence.
-/
abbrev BrauerGroup := Quotient (Brauer.CSA_Setoid K)
