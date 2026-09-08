/-
Copyright (c) 2026 Niels Voss, Arnav Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss, Arnav Mehta
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Singular values for finite-dimensional linear maps

For a linear map `T` between finite-dimensional inner product spaces `E` and `F`, we define the
singular values, which are the square roots of the eigenvalues of `T.adjoint ∘ₗ T`, arranged in
descending order and repeated according to their multiplicity.

With our definition, there are countably infinitely many singular values, but only the first rank(T)
singular values are nonzero.

The singular values are zero-indexed, so `T.singularValues 0` is the first singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ i ≤ rank(T)`.

## Main definition

- `LinearMap.singularValues`: The infinite but finitely supported sequence of the singular values of
  a linear map.

## Main statements

- `LinearMap.support_singularValues`: The first rank(T) many singular values are positive, and the
  rest are zero.

## Implementation notes

Suppose `T : E →ₗ[𝕜] F` where `dim(E) = n`, `dim(F) = m`.
In mathematical literature, the number of singular values varies, with popular choices including
- `rank(T)` singular values, all of which are positive.
- `min(n,m)` singular values, some of which might be zero.
- `n` singular values, some of which might be zero. This is the approach taken in [axler2024].
- Countably infinitely many singular values, with all but finitely many of them being zero.

We take the last approach for the following reasons:
- It avoid unnecessary dependent typing.
- You can easily convert this definition to the other three by composing with `Fin.val`, but
  converting between any two of the other definitions is more inconvenient because it involves
  multiple `Fin` types.
- If you prefer a definition where there are `k` singular values, you can treat the singular values
  after `k` as junk values.
  Not having to prove that `i < k` when getting the `i`th singular value has similar advantages to
  not having to prove that `y ≠ 0` when calculating `x / y`.
- This API coincides with a potential future API for approximation numbers, which are a
  generalization of singular values to continuous linear maps between possibly-infinite-dimensional
  normed vector spaces.

## TODO

- Generalize singular values to the approximation numbers for maps between
  possibly-infinite-dimensional normed vector spaces.
  This will likely have a similar type signature to the current singular values definition, except
  it will take in a `ContinuousLinearMap` and will not be finitely supported.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

singular values
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/--
If `T : E →ₗ[𝕜] F` is a linear map between finite dimensional inner product spaces, then
`T.singularValues` is the infinite sequence where the first dim(E) elements are the square roots of
eigenvalues of `T.adjoint ∘ₗ T` (which are guaranteed to be nonnegative real numbers), arranged
in descending order and repeated according to their multiplicity, and the rest of the elements in
the infinite sequence are zero. Please see the module docstring of
`Mathlib/Analysis/InnerProductSpace/SingularValues.lean` for an explanation of this design decision.

The singular values are zero-indexed, so `T.singularValues 0` refers to the first singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ i ≤ rank(T)`.
-/
/-
**LinearMap.singularValues** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：singularValues : Nat ->₀ Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric

--- 原说明 ---
If `T : E →ₗ[𝕜] F` is a linear map between finite dimensional inner product spac
es, then
`T.singularValues` is the infinite sequence where the first dim(E) elements are 
the square roots of
eigenvalues of `T.adjoint ∘ₗ T` (which are guaranteed to be nonnegative real num
bers), arranged
in descending order and repeated according to their multiplicity, and the rest o
f the elements in
the infinite sequence are zero. Please see the module docstring of
`Mathlib/Analysis/InnerProductSpace/SingularValues.lean` for an explanation of t
his design decision.

The singular values are zero-indexed, so `T.singularValues 0` refers to the firs
t singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ 
i ≤ rank(T)`.
-/
noncomputable def singularValues : ℕ →₀ ℝ :=
  Finsupp.embDomain Fin.valEmbedding <|
    Finsupp.ofSupportFinite
      (fun i ↦ √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)
/-
**LinearMap.singularValues_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_nonneg (i : Nat) : 0 <= T.singularValues i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.SingularValues.0.LinearMap.s
ingularValues.eq_1`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : 
NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensi
…
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `Finsupp.ofSupportFinite_coe`：ofSupportFinite_coe {f : α -> M} {hf : (Fun
ction.support f).Finite} : (ofSupportFinite f hf : α -> M) = f
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem singularValues_nonneg (i : ℕ) : 0 ≤ T.singularValues i := by
  rw [singularValues, Finsupp.embDomain_apply, Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity
/-
**LinearMap.singularValues_pos_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：singularValues_pos_iff_ne_zero (i : Nat) : 0 < T.singularValues i ↔ T.sing
ularValues i != 0
参数：i : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singularValues_pos_iff_ne_zero (i : ℕ) :
    0 < T.singularValues i ↔ T.singularValues i ≠ 0 := by
  grind [T.singularValues_nonneg i]

/--
Connection between `LinearMap.singularValues` and `LinearMap.IsSymmetric.eigenvalues`.
Together with `LinearMap.singularValues_of_finrank_le`, this characterizes the singular values.

Because of the square root, you probably need to use
`T.isPositive_adjoint_comp_self.nonneg_eigenvalues` to make effective use of this theorem.
-/
/-
**LinearMap.singularValues_fin** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_fin {n : Nat} (hn : finrank 𝕜 E = n) (i : Fin n) : T.singul
arValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i)
参数：hn : finrank 𝕜 E = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a

--- 原说明 ---
Connection between `LinearMap.singularValues` and `LinearMap.IsSymmetric.eigenva
lues`.
Together with `LinearMap.singularValues_of_finrank_le`, this characterizes the s
ingular values.

Because of the square root, you probably need to use
`T.isPositive_adjoint_comp_self.nonneg_eigenvalues` to make effective use of thi
s theorem.
-/
theorem singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i
/-
**LinearMap.singularValues_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_of_lt {n : Nat} (hn : finrank 𝕜 E = n) {i : Nat} (hi : i < 
n) : T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, h
i⟩)
参数：hn : finrank 𝕜 E = n；hi : i < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.singularValues_fin`：singularValues_fin {n : Nat} (hn : finrank
 𝕜 E = n) (i : Fin n) : T.singularValues i = √(T.isSymmetric_adjoint_comp_self.e
igenvalues hn i)
-/
theorem singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩) :=
  T.singularValues_fin hn ⟨i, hi⟩
/-
**LinearMap.singularValues_of_finrank_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_of_finrank_le {i : Nat} (hi : finrank 𝕜 E <= i) : T.singula
rValues i = 0
参数：hi : finrank 𝕜 E <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.valEmbedding_apply`：∀ {n : ℕ}, ⇑Fin.valEmbedding = Fin.val
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem singularValues_of_finrank_le {i : ℕ} (hi : finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  simp [hi]
/-
**LinearMap.sq_singularValues_fin** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sq_singularValues_fin {n : Nat} (hn : finrank 𝕜 E = n) (i : Fin n) : T.sin
gularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i
参数：hn : finrank 𝕜 E = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.singularValues_fin`：singularValues_fin {n : Nat} (hn : finrank
 𝕜 E = n) (i : Fin n) : T.singularValues i = √(T.isSymmetric_adjoint_comp_self.e
igenvalues hn i)
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `LinearMap.IsPositive.nonneg_eigenvalues`：∀ {𝕜 : Type u_1} {E : Type u_2}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜
 E]   [inst_3 : FiniteDimensi…
· 使用定理 `LinearMap.isPositive_adjoint_comp_self`：∀ {𝕜 : Type u_1} {E : Type u_2} 
{F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medAddCommGroup F] [inst_3 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sq_singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]
/-
**LinearMap.sq_singularValues_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sq_singularValues_of_lt {n : Nat} (hn : finrank 𝕜 E = n) {i : Nat} (hi : i
 < n) : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn 
⟨i, hi⟩
参数：hn : finrank 𝕜 E = n；hi : i < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.sq_singularValues_fin`：sq_singularValues_fin {n : Nat} (hn : f
inrank 𝕜 E = n) (i : Fin n) : T.singularValues i ^ 2 = T.isSymmetric_adjoint_com
p_self.eigenvalues hn…
-/
theorem sq_singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ :=
  T.sq_singularValues_fin hn ⟨i, hi⟩
/-
**LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap`。
形式化陈述：hasEigenvalue_adjoint_comp_self_sq_singularValues {n : Nat} (hn : n < finr
ank 𝕜 E) : End.HasEigenvalue (adjoint T ∘ₗ T) (T.singularValues n ^ 2)
参数：hn : n < finrank 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.sq_singularValues_fin`：sq_singularValues_fin {n : Nat} (hn : f
inrank 𝕜 E = n) (i : Fin n) : T.singularValues i ^ 2 = T.isSymmetric_adjoint_com
p_self.eigenvalues hn…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.IsSymmetric.hasEigenvalue_eigenvalues`：hasEigenvalue_eigenvalu
es (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : HasEigenvalu
e T (hT.eigenvalues hn i)
-/
theorem hasEigenvalue_adjoint_comp_self_sq_singularValues {n : ℕ} (hn : n < finrank 𝕜 E) :
    End.HasEigenvalue (adjoint T ∘ₗ T) (T.singularValues n ^ 2) := by
  convert! T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]
/-
**LinearMap.singularValues_antitone** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_antitone : Antitone T.singularValues
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.singularValues_of_finrank_le`：singularValues_of_finrank_le {i 
: Nat} (hi : finrank 𝕜 E <= i) : T.singularValues i = 0
· 使用定理 `LinearMap.singularValues_nonneg`：singularValues_nonneg (i : Nat) : 0 <= 
T.singularValues i
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `LinearMap.sq_singularValues_fin`：sq_singularValues_fin {n : Nat} (hn : f
inrank 𝕜 E = n) (i : Fin n) : T.singularValues i ^ 2 = T.isSymmetric_adjoint_com
p_self.eigenvalues hn…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LinearMap.IsSymmetric.eigenvalues_antitone`：eigenvalues_antitone (hT : T
.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : Antitone (hT.eigenvalues hn)
· 使用定理 `le_of_sq_le_sq`：le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <=
 b
-/
theorem singularValues_antitone : Antitone T.singularValues := by
  intro i j hij
  by_cases! hj : finrank 𝕜 E ≤ j
  · simpa [T.singularValues_of_finrank_le hj] using T.singularValues_nonneg i
  have : (T.singularValues j : ℝ) ^ 2 ≤ (T.singularValues i : ℝ) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j, hj⟩, T.sq_singularValues_fin rfl ⟨i, hij.trans_lt hj⟩]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij
  exact le_of_sq_le_sq this (T.singularValues_nonneg i)

/--
7.68(a) from [axler2024]. Note that we have countably infinitely many singular values whereas there
are only dim(domain(T)) singular values in [axler2024], so we modify the statement to account for
this.
-/
/-
**LinearMap.injective_iff_forall_lt_finrank_singularValues_pos** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap`。
形式化陈述：injective_iff_forall_lt_finrank_singularValues_pos : Function.Injective T 
↔ forall i < finrank 𝕜 E, 0 < T.singularValues i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `LinearMap.not_hasEigenvalue_zero_tfae`：not_hasEigenvalue_zero_tfae (φ : 
Module.End K M) : List.TFAE [ ¬ Module.End.HasEigenvalue φ 0, ¬ IsRoot (minpoly 
K φ) 0, constantCoeff φ.cha…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.adjoint_comp_self_injective_iff`：adjoint_comp_self_injective_i
ff (A : E ->ₗ[𝕜] F) : Function.Injective (A.adjoint ∘ A) ↔ Function.Injective A
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `LinearMap.IsSymmetric.exists_eigenvalues_eq`：exists_eigenvalues_eq (hT :
 T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜} (hμ : HasEigenvalue T μ) :
 exists i : Fin n, hT.eigenvalues…
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.singularValues_fin`：singularValues_fin {n : Nat} (hn : finrank
 𝕜 E = n) (i : Fin n) : T.singularValues i = √(T.isSymmetric_adjoint_comp_self.e
igenvalues hn i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.ofReal_eq_zero`：ofReal_eq_zero {x : Real} : (x : K) = 0 ↔ x = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearMap.sq_singularValues_of_lt`：sq_singularValues_of_lt {n : Nat} (hn
 : finrank 𝕜 E = n) {i : Nat} (hi : i < n) : T.singularValues i ^ 2 = T.isSymmet
ric_adjoint_comp_self.e…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.singularValues_nonneg`：singularValues_nonneg (i : Nat) : 0 <= 
T.singularValues i
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
7.68(a) from [axler2024]. Note that we have countably infinitely many singular v
alues whereas there
are only dim(domain(T)) singular values in [axler2024], so we modify the stateme
nt to account for
this.
-/
theorem injective_iff_forall_lt_finrank_singularValues_pos :
    Function.Injective T ↔ ∀ i < finrank 𝕜 E, 0 < T.singularValues i := by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 4 0
  rw [← adjoint_comp_self_injective_iff, ← coe_comp, ← ker_eq_bot, ← not_iff_not, this.not_left]
  push Not
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl h
    use i, i.isLt
    simp [RCLike.ofReal_eq_zero.mp hi, T.singularValues_fin rfl]
  · intro ⟨i, h, hz⟩
    convert! T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨i, h⟩
    rw [← sq_singularValues_of_lt, le_antisymm hz (T.singularValues_nonneg i)]
    simp

/--
7.68(b) from [axler2024]. See also `LinearMap.support_singularValues` for a stronger statement.
-/
/-
**LinearMap.card_support_singularValues** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.
range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.singularValues_fin`：singularValues_fin {n : Nat} (hn : finrank
 𝕜 E = n) (i : Fin n) : T.singularValues i = √(T.isSymmetric_adjoint_comp_self.e
igenvalues hn i)
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `LinearMap.isPositive_adjoint_comp_self`：∀ {𝕜 : Type u_1} {E : Type u_2} 
{F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medAddCommGroup F] [inst_3 :…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearMap.IsPositive.nonneg_eigenvalues`：∀ {𝕜 : Type u_1} {E : Type u_2}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜
 E]   [inst_3 : FiniteDimensi…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_attachFin`：card_attachFin (s : Finset Nat) (h : forall m in 
s, m < n) : (s.attachFin h).card = s.card
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `LinearMap.IsSymmetric.card_filter_eigenvalues_eq`：card_filter_eigenvalue
s_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) : Finset.card {i
 | hT.eigenvalues hn i = μ} = Module.f…
· 使用定理 `Module.End.eigenspace_zero`：eigenspace_zero (f : End R M) : f.eigenspace
 0 = LinearMap.ker f
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
7.68(b) from [axler2024]. See also `LinearMap.support_singularValues` for a stro
nger statement.
-/
theorem card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.range := by
  have hS : ∀ m ∈ T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  have : T.singularValues.support.attachFin hS = ({i | hT.eigenvalues rfl i = (0 : 𝕜)} : Finset _)ᶜ
    := by ext i; simp [T.singularValues_fin, T.isPositive_adjoint_comp_self.nonneg_eigenvalues]
  rw [← T.singularValues.support.card_attachFin hS, this, Finset.card_compl, Fintype.card_fin,
    hT.card_filter_eigenvalues_eq rfl 0, Module.End.eigenspace_zero,
    ← (T.adjoint ∘ₗ T).finrank_range_add_finrank_ker, add_tsub_cancel_right,
    T.range_adjoint_comp_self, finrank_range_adjoint]
/-
**LinearMap.isLowerSet_support_singularValues** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：isLowerSet_support_singularValues : IsLowerSet (T.singularValues.support :
 Set Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.singularValues_pos_iff_ne_zero`：singularValues_pos_iff_ne_zero
 (i : Nat) : 0 < T.singularValues i ↔ T.singularValues i != 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LinearMap.singularValues_antitone`：singularValues_antitone : Antitone T.
singularValues
-/
theorem isLowerSet_support_singularValues : IsLowerSet (T.singularValues.support : Set ℕ) := by
  intro a b hl ha
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← singularValues_pos_iff_ne_zero] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]
/-
**LinearMap.support_singularValues** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：support_singularValues : T.singularValues.support = Finset.range (finrank 
𝕜 T.range)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsLowerSet.eq_univ_or_Iio`：IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (
h : IsLowerSet s) : s = univ ∨ exists a, s = Iio a
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `LinearMap.isLowerSet_support_singularValues`：isLowerSet_support_singular
Values : IsLowerSet (T.singularValues.support : Set Nat)
· 使用定理 `Set.Infinite.not_finite`：∀ {α : Type u} {s : Set α}, s.Infinite → ¬s.Fin
ite
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Iio_eq_range`：Iio_eq_range : Iio a = range a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_singularValues : T.singularValues.support = Finset.range (finrank 𝕜 T.range) := by
  obtain ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio.resolve_left
    (fun h ↦ Set.infinite_univ.not_finite (h ▸ Finset.finite_toSet _))
  rw [← Finset.coe_Iio, Finset.coe_inj, Nat.Iio_eq_range] at hn
  simp [← card_support_singularValues, hn]
/-
**LinearMap.singularValues_pos_iff_lt_finrank_range** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：singularValues_pos_iff_lt_finrank_range {n : Nat} : 0 < T.singularValues n
 ↔ n < finrank 𝕜 T.range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.singularValues_pos_iff_ne_zero`：singularValues_pos_iff_ne_zero
 (i : Nat) : 0 < T.singularValues i ↔ T.singularValues i != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `LinearMap.support_singularValues`：support_singularValues : T.singularVal
ues.support = Finset.range (finrank 𝕜 T.range)
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem singularValues_pos_iff_lt_finrank_range {n : ℕ} :
    0 < T.singularValues n ↔ n < finrank 𝕜 T.range := by
  rw [singularValues_pos_iff_ne_zero, ← Finsupp.mem_support_iff, support_singularValues,
    Finset.mem_range]
/-
**LinearMap.singularValues_finrank_range_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：singularValues_finrank_range_self : T.singularValues (finrank 𝕜 T.range) =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `LinearMap.support_singularValues`：support_singularValues : T.singularVal
ues.support = Finset.range (finrank 𝕜 T.range)
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
-/
theorem singularValues_finrank_range_self : T.singularValues (finrank 𝕜 T.range) = 0 := by
  rw [← Finsupp.notMem_support_iff, support_singularValues]
  exact Finset.notMem_range_self
/-
**LinearMap.singularValues_eq_zero_iff_le_finrank_range** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap`。
形式化陈述：singularValues_eq_zero_iff_le_finrank_range {n : Nat} : T.singularValues n
 = 0 ↔ finrank 𝕜 T.range <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `LinearMap.support_singularValues`：support_singularValues : T.singularVal
ues.support = Finset.range (finrank 𝕜 T.range)
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem singularValues_eq_zero_iff_le_finrank_range {n : ℕ} :
    T.singularValues n = 0 ↔ finrank 𝕜 T.range ≤ n := by
  rw [← Finsupp.notMem_support_iff, support_singularValues, Finset.mem_range, not_lt]

@[simp]
/-
**LinearMap.singularValues_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_zero : (0 : E ->ₗ[𝕜] F).singularValues = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
· 使用定理 `LinearMap.singularValues_eq_zero_iff_le_finrank_range`：singularValues_eq
_zero_iff_le_finrank_range {n : Nat} : T.singularValues n = 0 ↔ finrank 𝕜 T.rang
e <= n
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem singularValues_zero : (0 : E →ₗ[𝕜] F).singularValues = 0 := by
  ext1 i
  rw [Finsupp.zero_apply, singularValues_eq_zero_iff_le_finrank_range, range_zero]
  simp

@[simp]
/-
**LinearMap.singularValues_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：singularValues_eq_zero_iff : T.singularValues = 0 ↔ T = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_bot`：range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ 
↔ f = 0
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `LinearMap.singularValues_eq_zero_iff_le_finrank_range`：singularValues_eq
_zero_iff_le_finrank_range {n : Nat} : T.singularValues n = 0 ↔ finrank 𝕜 T.rang
e <= n
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
· 使用定理 `LinearMap.singularValues_zero`：singularValues_zero : (0 : E ->ₗ[𝕜] F).si
ngularValues = 0
-/
theorem singularValues_eq_zero_iff : T.singularValues = 0 ↔ T = 0 := by
  constructor <;> intro h
  · rw [← range_eq_bot, ← Submodule.finrank_eq_zero, ← Nat.le_zero,
      ← singularValues_eq_zero_iff_le_finrank_range, h, Finsupp.zero_apply]
  · exact h ▸ singularValues_zero

end LinearMap

