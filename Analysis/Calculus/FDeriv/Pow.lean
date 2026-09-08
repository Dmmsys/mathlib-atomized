/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Fréchet Derivative of `f x ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n • f x ^ (n - 1)) • f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `fderiv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i`.

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

variable {𝕜 𝔸 E : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} {s : Set E}

open scoped RightActions

/-
**aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux (f : E → 𝔸) (f' : E →L[𝕜] 𝔸) (x : E) (n : ℕ) :
    f x •> ∑ i ∈ Finset.range (n + 1), f x ^ ((n + 1).pred - i) •> f' <• f x ^ i
      + f' <• (f x ^ (n + 1)) =
    ∑ i ∈ Finset.range (n + 1 + 1), f x ^ ((n + 1 + 1).pred - i) •> f' <• f x ^ i := by
  rw [Finset.sum_range_succ _ (n + 1), Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
  rw [tsub_add_eq_add_tsub hx]

@[to_fun]
/-
**HasStrictFDerivAt.pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f f' x) (n : Nat) : HasStric
tFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x
参数：h : HasStrictFDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f f' x) (n : ℕ) :
    HasStrictFDerivAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using! hasStrictFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    refine this.congr_fderiv <| aux _ _ _ _
/-
**hasStrictFDerivAt_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_pow' (n : Nat) {x : 𝔸} : HasStrictFDerivAt (𝕜
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.pow'`：HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f 
f' x) (n : Nat) : HasStrictFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pre
d - i) •> f'…
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
-/
theorem hasStrictFDerivAt_pow' (n : ℕ) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
  hasStrictFDerivAt_id _ |>.pow' n

@[to_fun]
/-
**HasFDerivWithinAt.pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f f' s x) (n : Nat) : HasFDe
rivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i)
 s x
参数：h : HasFDerivWithinAt f f' s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
    HasFDerivWithinAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) s x :=
  match n with
  | 0 => by simpa using! hasFDerivWithinAt_const 1 x s
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    exact this.congr_fderiv <| aux _ _ _ _
/-
**hasFDerivWithinAt_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_pow' (n : Nat) {x : 𝔸} {s : Set 𝔸} : HasFDerivWithinAt (
𝕜
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.pow'`：HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f 
f' s x) (n : Nat) : HasFDerivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.p
red - i) •> …
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
-/
theorem hasFDerivWithinAt_pow' (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) s x :=
  hasFDerivWithinAt_id _ _ |>.pow' n

@[to_fun]
/-
**HasFDerivAt.pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : Nat) : HasFDerivAt (f ^ n) 
(∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x
参数：h : HasFDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : ℕ) :
    HasFDerivAt (f ^ n) (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using! hasFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    exact this.congr_fderiv <| aux _ _ _ _
/-
**hasFDerivAt_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_pow' (n : Nat) {x : 𝔸} : HasFDerivAt (𝕜
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.pow'`：HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : Nat) : 
HasFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i)
 x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
-/
theorem hasFDerivAt_pow' (n : ℕ) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
  hasFDerivAt_id _ |>.pow' n

@[fun_prop]
/-
**DifferentiableWithinAt.fun_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.fun_pow (hf : DifferentiableWithinAt 𝕜 f s x) (n : 
Nat) : DifferentiableWithinAt 𝕜 (fun x => f x ^ n) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasFDerivWithinAt.pow'`：HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f 
f' s x) (n : Nat) : HasFDerivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.p
red - i) •> …
-/
theorem DifferentiableWithinAt.fun_pow (hf : DifferentiableWithinAt 𝕜 f s x) (n : ℕ) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ n) s x :=
  let ⟨_, hf'⟩ := hf; ⟨_, hf'.pow' n⟩

@[fun_prop]
/-
**DifferentiableWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.pow (hf : DifferentiableWithinAt 𝕜 f s x) : forall 
n : Nat, DifferentiableWithinAt 𝕜 (f ^ n) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.fun_pow`：DifferentiableWithinAt.fun_pow (hf : Dif
ferentiableWithinAt 𝕜 f s x) (n : Nat) : DifferentiableWithinAt 𝕜 (fun x => f x 
^ n) s x
-/
theorem DifferentiableWithinAt.pow (hf : DifferentiableWithinAt 𝕜 f s x) :
    ∀ n : ℕ, DifferentiableWithinAt 𝕜 (f ^ n) s x :=
  hf.fun_pow
/-
**differentiableWithinAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_pow (n : Nat) {x : 𝔸} {s : Set 𝔸} : DifferentiableW
ithinAt 𝕜 (fun x : 𝔸 => x ^ n) s x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.pow`：DifferentiableWithinAt.pow (hf : Differentia
bleWithinAt 𝕜 f s x) : forall n : Nat, DifferentiableWithinAt 𝕜 (f ^ n) s x
· 使用定理 `differentiableWithinAt_id`：differentiableWithinAt_id : DifferentiableWit
hinAt 𝕜 id s x
-/
theorem differentiableWithinAt_pow (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    DifferentiableWithinAt 𝕜 (fun x : 𝔸 => x ^ n) s x :=
  differentiableWithinAt_id.pow _

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x) (n : Nat) : Differentia
bleAt 𝕜 (f ^ n) x
参数：hf : DifferentiableAt 𝕜 f x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableWithinAt.pow`：DifferentiableWithinAt.pow (hf : Differentia
bleWithinAt 𝕜 f s x) : forall n : Nat, DifferentiableWithinAt 𝕜 (f ^ n) s x
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    DifferentiableAt 𝕜 (f ^ n) x :=
    differentiableWithinAt_univ.mp <| hf.differentiableWithinAt.pow n
/-
**differentiableAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_pow (n : Nat) {x : 𝔸} : DifferentiableAt 𝕜 (fun x : 𝔸 => 
x ^ n) x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.pow`：DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x)
 (n : Nat) : DifferentiableAt 𝕜 (f ^ n) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
-/
theorem differentiableAt_pow (n : ℕ) {x : 𝔸} : DifferentiableAt 𝕜 (fun x : 𝔸 => x ^ n) x :=
  differentiableAt_id.pow _

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.pow (hf : DifferentiableOn 𝕜 f s) (n : Nat) : Differentia
bleOn 𝕜 (f ^ n) s
参数：hf : DifferentiableOn 𝕜 f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.pow`：DifferentiableWithinAt.pow (hf : Differentia
bleWithinAt 𝕜 f s x) : forall n : Nat, DifferentiableWithinAt 𝕜 (f ^ n) s x
-/
theorem DifferentiableOn.pow (hf : DifferentiableOn 𝕜 f s) (n : ℕ) :
    DifferentiableOn 𝕜 (f ^ n) s := fun x h => (hf x h).pow n
/-
**differentiableOn_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_pow (n : Nat) {s : Set 𝔸} : DifferentiableOn 𝕜 (fun x : 𝔸
 => x ^ n) s
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.pow`：DifferentiableOn.pow (hf : DifferentiableOn 𝕜 f s)
 (n : Nat) : DifferentiableOn 𝕜 (f ^ n) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
-/
theorem differentiableOn_pow (n : ℕ) {s : Set 𝔸} : DifferentiableOn 𝕜 (fun x : 𝔸 => x ^ n) s :=
  differentiableOn_id.pow n

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.pow (hf : Differentiable 𝕜 f) (n : Nat) : Differentiable 𝕜 
(f ^ n)
参数：hf : Differentiable 𝕜 f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.pow`：DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x)
 (n : Nat) : DifferentiableAt 𝕜 (f ^ n) x
-/
theorem Differentiable.pow (hf : Differentiable 𝕜 f) (n : ℕ) : Differentiable 𝕜 (f ^ n) :=
  fun x => (hf x).pow n
/-
**differentiable_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_pow (n : Nat) : Differentiable 𝕜 fun x : 𝔸 => x ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.pow`：Differentiable.pow (hf : Differentiable 𝕜 f) (n : Na
t) : Differentiable 𝕜 (f ^ n)
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
-/
theorem differentiable_pow (n : ℕ) : Differentiable 𝕜 fun x : 𝔸 => x ^ n :=
  differentiable_id.pow _

@[to_fun fderiv_fun_pow']
/-
**fderiv_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_pow' (n : Nat) (hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (f ^ n) x =
 (∑ i in Finset.range n, f x ^ (n.pred - i) •> fderiv 𝕜 f x <• f x ^ i)
参数：n : Nat；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.pow'`：HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : Nat) : 
HasFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i)
 x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_pow' (n : ℕ) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (f ^ n) x
      = (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> fderiv 𝕜 f x <• f x ^ i) :=
  hf.hasFDerivAt.pow' n |>.fderiv
/-
**fderiv_pow_ring'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_pow_ring' {x : 𝔸} (n : Nat) : fderiv 𝕜 (fun x : 𝔸 => x ^ n) x = (∑ 
i in Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_fun_pow'`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAddCommGrou
p E] …
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `fderiv_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : 
Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Top
olo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem fderiv_pow_ring' {x : 𝔸} (n : ℕ) :
    fderiv 𝕜 (fun x : 𝔸 ↦ x ^ n) x
      = (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i) := by
  rw [fderiv_fun_pow' n differentiableAt_fun_id, fderiv_fun_id]

@[to_fun fderivWithin_fun_pow']
/-
**fderivWithin_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_pow' (hxs : UniqueDiffWithinAt 𝕜 s x) (n : Nat) (hf : Differe
ntiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 (f ^ n) s x = (∑ i in Finset.range n, 
f x ^ (n.pred - i) •> fderivWithin 𝕜 f s x <• f x ^ i)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；n : Nat；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.pow'`：HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f 
f' s x) (n : Nat) : HasFDerivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.p
red - i) •> …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_pow' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : ℕ) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (f ^ n) s x
      = (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> fderivWithin 𝕜 f s x <• f x ^ i) :=
  hf.hasFDerivWithinAt.pow' n |>.fderivWithin hxs
/-
**fderivWithin_pow_ring'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_pow_ring' {s : Set 𝔸} {x : 𝔸} (n : Nat) (hxs : UniqueDiffWith
inAt 𝕜 s x) : fderivWithin 𝕜 (fun x : 𝔸 => x ^ n) s x = (∑ i in Finset.range n, 
x ^ (n.pred - i) •> .id _ _ <• x ^ i)
参数：n : Nat；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_fun_pow'`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAddCo
mmGroup E] …
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `fderivWithin_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3
 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem fderivWithin_pow_ring' {s : Set 𝔸} {x : 𝔸} (n : ℕ) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : 𝔸 ↦ x ^ n) s x
      = (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i) := by
  rw [fderivWithin_fun_pow' hxs n differentiableAt_fun_id.differentiableWithinAt,
    fderivWithin_fun_id hxs]

end NormedRing

section NormedCommRing
variable [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} {s : Set E}

/-
**aux_sum_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux_sum_eq_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, MulOpposite.op (f x ^ i) • f x ^ (n.pred - i) • f' =
      (n • f x ^ (n - 1)) • f' := by
  simp_rw [op_smul_eq_smul, smul_smul, ← pow_add, ← Finset.sum_smul]
  rw [Finset.sum_eq_card_nsmul, Finset.card_range, smul_assoc]
  intro a ha
  congr
  exact add_tsub_cancel_of_le (Nat.le_pred_of_lt <| Finset.mem_range.1 ha)
/-
**HasStrictFDerivAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f' x) (n : Nat) : HasStrict
FDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') x
参数：h : HasStrictFDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
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
· 使用定理 `HasStrictFDerivAt.pow'`：HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f 
f' x) (n : Nat) : HasStrictFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pre
d - i) •> f'…
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.Pow.0.aux_sum_eq_pow`：∀ {𝕜 : T
ype u_1} {𝔸 : Type u_2} {E : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NormedCommRing 𝔸]   [inst_2 : NormedAddCommGroup…
-/
theorem HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f' x) (n : ℕ) :
    HasStrictFDerivAt (fun x ↦ f x ^ n) ((n • f x ^ (n - 1)) • f') x :=
  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
/-
**hasStrictFDerivAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_pow (n : Nat) {x : 𝔸} : HasStrictFDerivAt (𝕜
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.pow`：HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f'
 x) (n : Nat) : HasStrictFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') 
x
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
-/
theorem hasStrictFDerivAt_pow (n : ℕ) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜)
      (fun x : 𝔸 ↦ x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) x :=
  hasStrictFDerivAt_id _ |>.pow n
/-
**HasFDerivWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f' s x) (n : Nat) : HasFDer
ivWithinAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') s x
参数：h : HasFDerivWithinAt f f' s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.congr_fderiv`：HasFDerivWithinAt.congr_fderiv (h : HasF
DerivWithinAt f f' s x) (h' : f' = g') : HasFDerivWithinAt f g' s x
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
· 使用定理 `HasFDerivWithinAt.pow'`：HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f 
f' s x) (n : Nat) : HasFDerivWithinAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.p
red - i) •> …
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.Pow.0.aux_sum_eq_pow`：∀ {𝕜 : T
ype u_1} {𝔸 : Type u_2} {E : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NormedCommRing 𝔸]   [inst_2 : NormedAddCommGroup…
-/
theorem HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
    HasFDerivWithinAt (fun x ↦ f x ^ n) ((n • f x ^ (n - 1)) • f') s x :=
  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
/-
**hasFDerivWithinAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_pow (n : Nat) {x : 𝔸} {s : Set 𝔸} : HasFDerivWithinAt (𝕜
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.pow`：HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f'
 s x) (n : Nat) : HasFDerivWithinAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f'
) s x
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
-/
theorem hasFDerivWithinAt_pow (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜)
      (fun x : 𝔸 ↦ x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) s x :=
  hasFDerivWithinAt_id _ _ |>.pow n
/-
**HasFDerivAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : Nat) : HasFDerivAt (fun x =>
 f x ^ n) ((n • f x ^ (n - 1)) • f') x
参数：h : HasFDerivAt f f' x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.congr_fderiv`：HasFDerivAt.congr_fderiv (h : HasFDerivAt f f'
 x) (h' : f' = g') : HasFDerivAt f g' x
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
· 使用定理 `HasFDerivAt.pow'`：HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : Nat) : 
HasFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i)
 x
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.Pow.0.aux_sum_eq_pow`：∀ {𝕜 : T
ype u_1} {𝔸 : Type u_2} {E : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NormedCommRing 𝔸]   [inst_2 : NormedAddCommGroup…
-/
theorem HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : ℕ) :
    HasFDerivAt (fun x ↦ f x ^ n) ((n • f x ^ (n - 1)) • f') x :=
  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
/-
**hasFDerivAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_pow (n : Nat) {x : 𝔸} : HasFDerivAt (𝕜
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.pow`：HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : Nat) : Ha
sFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
-/
theorem hasFDerivAt_pow (n : ℕ) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜)
      (fun x : 𝔸 ↦ x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) x :=
  hasFDerivAt_id _ |>.pow n

@[to_fun fderiv_fun_pow]
/-
**fderiv_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_pow (n : Nat) (hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (f ^ n) x = 
(n • f x ^ (n - 1)) • fderiv 𝕜 f x
参数：n : Nat；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.pow`：HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : Nat) : Ha
sFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_pow (n : ℕ) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (f ^ n) x = (n • f x ^ (n - 1)) • fderiv 𝕜 f x :=
  hf.hasFDerivAt.pow n |>.fderiv
/-
**fderiv_pow_ring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_pow_ring {x : 𝔸} (n : Nat) : fderiv 𝕜 (fun x : 𝔸 => x ^ n) x = (n •
 x ^ (n - 1)) • .id _ _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3} [inst : N
ontriviallyNormedField 𝕜] [inst_1 : NormedCommRing 𝔸]   [inst_2 : NormedAddCommG
roup…
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `fderiv_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : 
Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Top
olo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem fderiv_pow_ring {x : 𝔸} (n : ℕ) :
    fderiv 𝕜 (fun x : 𝔸 ↦ x ^ n) x = (n • x ^ (n - 1)) • .id _ _ := by
  rw [fderiv_fun_pow n differentiableAt_fun_id, fderiv_fun_id]

@[to_fun fderivWithin_fun_pow]
/-
**fderivWithin_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x) (n : Nat) (hf : Differen
tiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 (f ^ n) s x = (n • f x ^ (n - 1)) • fde
rivWithin 𝕜 f s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；n : Nat；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.pow`：HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f'
 s x) (n : Nat) : HasFDerivWithinAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f'
) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : ℕ) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (f ^ n) s x = (n • f x ^ (n - 1)) • fderivWithin 𝕜 f s x :=
  hf.hasFDerivWithinAt.pow n |>.fderivWithin hxs
/-
**fderivWithin_pow_ring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_pow_ring {s : Set 𝔸} {x : 𝔸} (n : Nat) (hxs : UniqueDiffWithi
nAt 𝕜 s x) : fderivWithin 𝕜 (fun x : 𝔸 => x ^ n) s x = (n • x ^ (n - 1)) • .id _
 _
参数：n : Nat；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3} [in
st : NontriviallyNormedField 𝕜] [inst_1 : NormedCommRing 𝔸]   [inst_2 : NormedAd
dCommGroup…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `fderivWithin_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3
 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem fderivWithin_pow_ring {s : Set 𝔸} {x : 𝔸} (n : ℕ) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : 𝔸 ↦ x ^ n) s x = (n • x ^ (n - 1)) • .id _ _ := by
  rw [fderivWithin_fun_pow hxs n differentiableAt_fun_id.differentiableWithinAt,
    fderivWithin_fun_id hxs]

end NormedCommRing

