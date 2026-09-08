/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n * f x ^ (n - 1) * f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `deriv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

variable {𝕜 𝔸 : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸]
variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

/-
**HasStrictDerivAt.fun_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.fun_pow' (h : HasStrictDerivAt f f' x) (n : Nat) : HasStr
ictDerivAt (fun x => f x ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * 
f x ^ i) x
参数：h : HasStrictDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.pow'`：HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f 
f' x) (n : Nat) : HasStrictFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pre
d - i) •> f'…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.fun_pow' (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
  simpa using! h.hasStrictFDerivAt.pow' n |>.hasStrictDerivAt
/-
**HasStrictDerivAt.pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.pow' (h : HasStrictDerivAt f f' x) (n : Nat) : HasStrictD
erivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x
参数：h : HasStrictDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.fun_pow'`：HasStrictDerivAt.fun_pow' (h : HasStrictDeriv
At f f' x) (n : Nat) : HasStrictDerivAt (fun x => f x ^ n) (∑ i in Finset.range 
n, f x ^ (n.pre…
-/
theorem HasStrictDerivAt.pow' (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x :=
  h.fun_pow' n
/-
**HasDerivWithinAt.fun_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.fun_pow' (h : HasDerivWithinAt f f' s x) (n : Nat) : HasD
erivWithinAt (fun x => f x ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * f' 
* f x ^ i) s x
参数：h : HasDerivWithinAt f f' s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.pow'`：HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f 
f' s x) (n : Nat) : HasFDerivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.p
red - i) •> …
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.fun_pow' (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x := by
  simpa using! h.hasFDerivWithinAt.pow' n |>.hasDerivWithinAt
/-
**HasDerivWithinAt.pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.pow' (h : HasDerivWithinAt f f' s x) (n : Nat) : HasDeriv
WithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x
参数：h : HasDerivWithinAt f f' s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.fun_pow'`：HasDerivWithinAt.fun_pow' (h : HasDerivWithin
At f f' s x) (n : Nat) : HasDerivWithinAt (fun x => f x ^ n) (∑ i in Finset.rang
e n, f x ^ (n.p…
-/
theorem HasDerivWithinAt.pow' (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x := h.fun_pow' n
/-
**HasDerivAt.fun_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.fun_pow' (h : HasDerivAt f f' x) (n : Nat) : HasDerivAt (fun x 
=> f x ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x
参数：h : HasDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.pow'`：HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : Nat) : 
HasFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i)
 x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.fun_pow' (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
  simpa using! h.hasFDerivAt.pow' n |>.hasDerivAt
/-
**HasDerivAt.pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.pow' (h : HasDerivAt f f' x) (n : Nat) : HasDerivAt (f ^ n) (∑ 
i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x
参数：h : HasDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.fun_pow'`：HasDerivAt.fun_pow' (h : HasDerivAt f f' x) (n : Na
t) : HasDerivAt (fun x => f x ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * 
f' * f x …
-/
theorem HasDerivAt.pow' (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := h.fun_pow' n

@[simp low]
/-
**derivWithin_fun_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_pow' (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat) : deri
vWithin (fun x => f x ^ n) s x = ∑ i in Finset.range n, f x ^ (n.pred - i) * der
ivWithin f s x * f x ^ i
参数：h : DifferentiableWithinAt 𝕜 f s x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.pow'`：HasDerivWithinAt.pow' (h : HasDerivWithinAt f f' 
s x) (n : Nat) : HasDerivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred 
- i) * f' *…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_pow' (h : DifferentiableWithinAt 𝕜 f s x) (n : ℕ) :
    derivWithin (fun x => f x ^ n) s x =
      ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * derivWithin f s x * f x ^ i := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow' n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp low]
/-
**derivWithin_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_pow' (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat) : derivWit
hin (f ^ n) s x = ∑ i in Finset.range n, f x ^ (n.pred - i) * derivWithin f s x 
* f x ^ i
参数：h : DifferentiableWithinAt 𝕜 f s x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_pow'`：derivWithin_fun_pow' (h : DifferentiableWithinAt 𝕜
 f s x) (n : Nat) : derivWithin (fun x => f x ^ n) s x = ∑ i in Finset.range n, 
f x ^ (n.p…
-/
theorem derivWithin_pow' (h : DifferentiableWithinAt 𝕜 f s x) (n : ℕ) :
    derivWithin (f ^ n) s x =
      ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * derivWithin f s x * f x ^ i :=
  derivWithin_fun_pow' h n

@[simp low]
/-
**deriv_fun_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_pow' (h : DifferentiableAt 𝕜 f x) (n : Nat) : deriv (fun x => f 
x ^ n) x = ∑ i in Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i
参数：h : DifferentiableAt 𝕜 f x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.pow'`：HasDerivAt.pow' (h : HasDerivAt f f' x) (n : Nat) : Has
DerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_pow' (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (fun x => f x ^ n) x = ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i :=
  (h.hasDerivAt.pow' n).deriv

@[simp low]
/-
**deriv_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_pow' (h : DifferentiableAt 𝕜 f x) (n : Nat) : deriv (f ^ n) x = ∑ i 
in Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i
参数：h : DifferentiableAt 𝕜 f x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_fun_pow'`：deriv_fun_pow' (h : DifferentiableAt 𝕜 f x) (n : Nat) : 
deriv (fun x => f x ^ n) x = ∑ i in Finset.range n, f x ^ (n.pred - i) * deriv f
 x *…
-/
theorem deriv_pow' (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (f ^ n) x = ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i :=
  deriv_fun_pow' h n

end NormedRing

section NormedCommRing
variable [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸]
variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

open scoped RightActions

/-
**HasStrictDerivAt.fun_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.fun_pow (h : HasStrictDerivAt f f' x) (n : Nat) : HasStri
ctDerivAt (fun x => f x ^ n) (n * f x ^ (n - 1) * f') x
参数：h : HasStrictDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.pow`：HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f'
 x) (n : Nat) : HasStrictFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') 
x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.fun_pow (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (fun x ↦ f x ^ n) (n * f x ^ (n - 1) * f') x := by
  simpa using h.hasStrictFDerivAt.pow n |>.hasStrictDerivAt
/-
**HasStrictDerivAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.pow (h : HasStrictDerivAt f f' x) (n : Nat) : HasStrictDe
rivAt (f ^ n) (n * f x ^ (n - 1) * f') x
参数：h : HasStrictDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.fun_pow`：HasStrictDerivAt.fun_pow (h : HasStrictDerivAt
 f f' x) (n : Nat) : HasStrictDerivAt (fun x => f x ^ n) (n * f x ^ (n - 1) * f'
) x
-/
theorem HasStrictDerivAt.pow (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x := h.fun_pow n
/-
**HasDerivWithinAt.fun_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.fun_pow (h : HasDerivWithinAt f f' s x) (n : Nat) : HasDe
rivWithinAt (fun x => f x ^ n) (n * f x ^ (n - 1) * f') s x
参数：h : HasDerivWithinAt f f' s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.pow`：HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f'
 s x) (n : Nat) : HasFDerivWithinAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f'
) s x
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.fun_pow (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (fun x ↦ f x ^ n) (n * f x ^ (n - 1) * f') s x := by
  simpa using h.hasFDerivWithinAt.pow n |>.hasDerivWithinAt
/-
**HasDerivWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s x) (n : Nat) : HasDerivW
ithinAt (f ^ n) (n * f x ^ (n - 1) * f') s x
参数：h : HasDerivWithinAt f f' s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.fun_pow`：HasDerivWithinAt.fun_pow (h : HasDerivWithinAt
 f f' s x) (n : Nat) : HasDerivWithinAt (fun x => f x ^ n) (n * f x ^ (n - 1) * 
f') s x
-/
theorem HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (f ^ n) (n * f x ^ (n - 1) * f') s x := h.fun_pow n

@[to_fun]
/-
**HasDerivAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.pow (h : HasDerivAt f f' x) (n : Nat) : HasDerivAt (f ^ n) (n *
 f x ^ (n - 1) * f') x
参数：h : HasDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.pow`：HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : Nat) : Ha
sFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.pow (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x := by
  simpa using! h.hasFDerivAt.pow n |>.hasDerivAt

@[to_fun (attr := simp) derivWithin_fun_pow]
/-
**derivWithin_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_pow (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat) : derivWith
in (f ^ n) s x = n * f x ^ (n - 1) * derivWithin f s x
参数：h : DifferentiableWithinAt 𝕜 f s x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.pow`：HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s 
x) (n : Nat) : HasDerivWithinAt (f ^ n) (n * f x ^ (n - 1) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_pow (h : DifferentiableWithinAt 𝕜 f s x) (n : ℕ) :
    derivWithin (f ^ n) s x = n * f x ^ (n - 1) * derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun (attr := simp) deriv_fun_pow]
/-
**deriv_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_pow (h : DifferentiableAt 𝕜 f x) (n : Nat) : deriv (f ^ n) x = n * f
 x ^ (n - 1) * deriv f x
参数：h : DifferentiableAt 𝕜 f x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.pow`：HasDerivAt.pow (h : HasDerivAt f f' x) (n : Nat) : HasDe
rivAt (f ^ n) (n * f x ^ (n - 1) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_pow (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (f ^ n) x = n * f x ^ (n - 1) * deriv f x := (h.hasDerivAt.pow n).deriv

end NormedCommRing

section NontriviallyNormedField
variable [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} {c : 𝕜 → 𝕜}

/-
**hasStrictDerivAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_pow (n : Nat) (x : 𝕜) : HasStrictDerivAt (fun x : 𝕜 => x 
^ n) (n * x ^ (n - 1)) x
参数：n : Nat；x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasStrictDerivAt.pow`：HasStrictDerivAt.pow (h : HasStrictDerivAt f f' x)
 (n : Nat) : HasStrictDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
-/
theorem hasStrictDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasStrictDerivAt (fun x : 𝕜 ↦ x ^ n) (n * x ^ (n - 1)) x := by
  simpa using! (hasStrictDerivAt_id x).pow n
/-
**hasDerivWithinAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_pow (n : Nat) (x : 𝕜) : HasDerivWithinAt (fun x : 𝕜 => x 
^ n) (n * x ^ (n - 1)) s x
参数：n : Nat；x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivWithinAt.pow`：HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s 
x) (n : Nat) : HasDerivWithinAt (f ^ n) (n * f x ^ (n - 1) * f') s x
· 使用定理 `hasDerivWithinAt_id`：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
-/
theorem hasDerivWithinAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivWithinAt (fun x : 𝕜 ↦ x ^ n) (n * x ^ (n - 1)) s x := by
  simpa using! (hasDerivWithinAt_id x s).pow n
/-
**hasDerivAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_pow (n : Nat) (x : 𝕜) : HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜
) * x ^ (n - 1)) x
参数：n : Nat；x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_pow`：hasStrictDerivAt_pow (n : Nat) (x : 𝕜) : HasStrict
DerivAt (fun x : 𝕜 => x ^ n) (n * x ^ (n - 1)) x
-/
theorem hasDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x := by
  simpa using (hasStrictDerivAt_pow n x).hasDerivAt
/-
**derivWithin_pow_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_pow_field (h : UniqueDiffWithinAt 𝕜 s x) (n : Nat) : derivWith
in (fun x => x ^ n) s x = (n : 𝕜) * x ^ (n - 1)
参数：h : UniqueDiffWithinAt 𝕜 s x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : NormedCommRing 𝔸]   [inst_2 : NormedAlgebra 𝕜 𝔸] {f : 
𝕜 → 𝔸} {x…
· 使用定理 `differentiableWithinAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `derivWithin_id'`：derivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) : deri
vWithin (fun x => x) s x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem derivWithin_pow_field (h : UniqueDiffWithinAt 𝕜 s x) (n : ℕ) :
    derivWithin (fun x => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) := by
  rw [derivWithin_fun_pow (differentiableWithinAt_fun_id) n, derivWithin_id' _ _ h, mul_one]
/-
**deriv_pow_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_pow_field (n : Nat) : deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 
1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} [inst : NontriviallyNorme
dField 𝕜] [inst_1 : NormedCommRing 𝔸]   [inst_2 : NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸}
 {x…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_pow_field (n : ℕ) : deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1) := by
  simp

end NontriviallyNormedField

