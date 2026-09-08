/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.VectorField

/-!
# Evaluation of the derivative of differential forms on vector fields

In this file we prove the following formula and its corollaries.
If `ω` is a differentiable `k`-form and `V i` are `k + 1` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_n(x)) = \sum_{i=0}^k (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_k(x)\big)\right)(V_i(x)) +
    \sum_{0 \le i < j\le k} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x), V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big),
$$
where $[V_i, V_j]$ is the commutator of the vector fields $V_i$ and $V_j$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

There is no convenient way to write the second term in Lean for `k = 0`,
so we only state this theorem for `k = n + 1`,
see `extDerivWithin_apply_vectorField` and `extDeriv_apply_vectorField`.

In this case, we write the second term as a sum over `i j : Fin (n + 1)`, `i ≤ j`,
where the indexes `(i, j)` in our sum correspond to `(i, j + 1)`
(formally, `(Fin.castSucc i, Fin.succ j)`) in the formula above.
For this reason, we have `-` before the sum in our formal statement.
-/

public section

open Filter ContinuousAlternatingMap Finset VectorField
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n m k : ℕ} {r : WithTop ℕ∞}
  {s t : Set E} {x : E}

/--
If `ω` is a differentiable `(n + 1)`-form and `V i` are `n + 2` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i \le j\le n} (-1)^{i + j}
        ω\big(x; [V_i, V_{j + 1}](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_{j + 1}(x)}, …, V_k(x)\big),
$$

where $[V_i, V_{j + 1}]$ is the commutator of the vector fields $V_i$ and $V_{j + 1}$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

In informal texts, this formula is usually written as

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i < j\le n + 1} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big).
$$

In the sum from our formalization,
each index `(i, j)` corresponds to the index `(Fin.castSucc i, Fin.succ j)`
in the sum used in informal texts.

For this reason, `i + j` in our sum has the opposite parity compared to informal texts,
which changes the sign before the sum from `+` to `-`.
-/
/-
**extDerivWithin_apply_vectorField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_apply_vectorField {ω : E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V :
 Fin (n + 2) -> E -> E} (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : forall i, Di
fferentiableWithinAt 𝕜 (V i) s x) (hsx : UniqueDiffWithinAt 𝕜 s x) : extDerivWit
hin ω s x (V · x) = (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x => ω x (i.removeN
th (V · x))) s x (V i x)) - ∑ i : Fin (n + 1), ∑ j >= i, (-1) ^ (i + j : Nat) • 
ω x (Matrix.vecCons (lieBracketWithin 𝕜 (V i.castSucc) (V j.succ) s x) (j.remove
Nth <| i.castSucc.removeNt
参数：n + 1；n + 2；hω : DifferentiableWithinAt 𝕜 ω s x；hV : forall i, Differentiable
WithinAt 𝕜 (V i) s x；hsx : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `fderivWithin_continuousAlternatingMap_apply_apply`：fderivWithin_continuo
usAlternatingMap_apply_apply (hf : DifferentiableWithinAt 𝕜 f s x) (hg : forall 
i, DifferentiableWithinAt 𝕜 (g i) s x) …
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `extDerivWithin_apply`：extDerivWithin_apply (h : DifferentiableWithinAt 𝕜
 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x) (v : Fin (n + 1) -> E) : extDerivWithin 
ω s x v = …
· 使用定理 `fderivWithin_continuousAlternatingMap_apply_const_apply`：fderivWithin_co
ntinuousAlternatingMap_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : 
DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Fin.sum_sum_eq_sum_triangle_add`：∀ {M : Type u_2} [inst : AddCommMonoid 
M] {n : ℕ} (f : Fin (n + 1) → Fin n → M),   ∑ i, ∑ j, f i j = ∑ i, ∑ j ≥ i, (f i
.castSucc j + f j.suc…
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用定理 `ContinuousAlternatingMap.map_insertNth`：map_insertNth (f : E [⋀^Fin (n +
 1)]->L[𝕜] F) (p : Fin (n + 1)) (x : E) (v : Fin n -> E) : f (p.insertNth x v) =
 (-1) ^ (p : Nat) • f (Matri…
· 使用定理 `Fin.removeNth_removeNth_eq_swap`：removeNth_removeNth_eq_swap {α : Sort*}
 (m : Fin (n + 2) -> α) (i : Fin (n + 1)) (j : Fin (n + 2)) : i.removeNth (j.rem
oveNth m) = (i.predAb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `ω` is a differentiable `(n + 1)`-form and `V i` are `n + 2` differentiable v
ector fields, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big
)\right)(V_i(x)) -
      \sum_{0 \le i \le j\le n} (-1)^{i + j}
        ω\big(x; [V_i, V_{j + 1}](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_{j + 1}(x)}, …, V_k(x)\big)
,
$$

where $[V_i, V_{j + 1}]$ is the commutator of the vector fields $V_i$ and $V_{j 
+ 1}$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

In informal texts, this formula is usually written as

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big
)\right)(V_i(x)) -
      \sum_{0 \le i < j\le n + 1} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big).
$$

In the sum from our formalization,
each index `(i, j)` corresponds to the index `(Fin.castSucc i, Fin.succ j)`
in the sum used in informal texts.

For this reason, `i + j` in our sum has the opposite parity compared to informal
 texts,
which changes the sign before the sum from `+` to `-`.
-/
theorem extDerivWithin_apply_vectorField
    {ω : E → E [⋀^Fin (n + 1)]→L[𝕜] F} {V : Fin (n + 2) → E → E}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : ∀ i, DifferentiableWithinAt 𝕜 (V i) s x)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin ω s x (V · x) =
      (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) s x (V i x)) -
        ∑ i : Fin (n + 1), ∑ j ≥ i,
          (-1) ^ (i + j : ℕ) •
            ω x (Matrix.vecCons (lieBracketWithin 𝕜 (V i.castSucc) (V j.succ) s x)
              (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  have H₀ (i : Fin (n + 2)) (j : Fin (n + 1)) :
      DifferentiableWithinAt 𝕜 (fun y ↦ i.removeNth (V · y) j) s x := hV ..
  symm
  simp only [extDerivWithin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply,
    fderivWithin_continuousAlternatingMap_apply_apply hω (H₀ _) hsx, *,
    smul_add, sum_add_distrib, add_sub_assoc, add_eq_left, sub_eq_zero, smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Fintype.sum_congr _ _ fun i ↦ sum_congr rfl fun j hj ↦ ?_
  rw [mem_Ici] at hj
  simp only [← Fin.insertNth_removeNth, map_insertNth]
  rw [Fin.removeNth_removeNth_eq_swap]
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  simp +unfoldPartialApp [pow_add, lieBracketWithin, mul_smul, smul_comm ((-1) ^ (j : ℕ)), smul_sub,
      ← sub_eq_add_neg, H₁, H₂, H₃, Fin.removeNth]

/--
If `ω` is a differentiable `(n + 1)`-form and `V i` are `n + 2` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i \le j\le n} (-1)^{i + j}
        ω\big(x; [V_i, V_{j + 1}](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_{j + 1}(x)}, …, V_k(x)\big),
$$

where $[V_i, V_{j + 1}]$ is the commutator of the vector fields $V_i$ and $V_{j + 1}$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

In informal texts, this formula is usually written as

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i < j\le n + 1} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big).
$$

In the sum from our formalization,
each index `(i, j)` corresponds to the index `(Fin.castSucc i, Fin.succ j)`
in the sum used in informal texts.

For this reason, `i + j` in our sum has the opposite parity compared to informal texts,
which changes the sign before the sum from `+` to `-`.
-/
/-
**extDeriv_apply_vectorField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_apply_vectorField {ω : E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V : Fin (
n + 2) -> E -> E} (hω : DifferentiableAt 𝕜 ω x) (hV : forall i, DifferentiableAt
 𝕜 (V i) x) : extDeriv ω x (V · x) = (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x => ω x
 (i.removeNth (V · x))) x (V i x)) - ∑ i : Fin (n + 1), ∑ j >= i, (-1) ^ (i + j 
: Nat) • ω x (Matrix.vecCons (lieBracket 𝕜 (V i.castSucc) (V j.succ) x) (j.remov
eNth <| i.castSucc.removeNth (V · x)))
参数：n + 1；n + 2；hω : DifferentiableAt 𝕜 ω x；hV : forall i, DifferentiableAt 𝕜 (V 
i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `extDerivWithin_apply_vectorField`：extDerivWithin_apply_vectorField {ω : 
E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V : Fin (n + 2) -> E -> E} (hω : Differentiable
WithinAt 𝕜 ω s x) (hV …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
If `ω` is a differentiable `(n + 1)`-form and `V i` are `n + 2` differentiable v
ector fields, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big
)\right)(V_i(x)) -
      \sum_{0 \le i \le j\le n} (-1)^{i + j}
        ω\big(x; [V_i, V_{j + 1}](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_{j + 1}(x)}, …, V_k(x)\big)
,
$$

where $[V_i, V_{j + 1}]$ is the commutator of the vector fields $V_i$ and $V_{j 
+ 1}$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

In informal texts, this formula is usually written as

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big
)\right)(V_i(x)) -
      \sum_{0 \le i < j\le n + 1} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big).
$$

In the sum from our formalization,
each index `(i, j)` corresponds to the index `(Fin.castSucc i, Fin.succ j)`
in the sum used in informal texts.

For this reason, `i + j` in our sum has the opposite parity compared to informal
 texts,
which changes the sign before the sum from `+` to `-`.
-/
theorem extDeriv_apply_vectorField {ω : E → E [⋀^Fin (n + 1)]→L[𝕜] F} {V : Fin (n + 2) → E → E}
    (hω : DifferentiableAt 𝕜 ω x) (hV : ∀ i, DifferentiableAt 𝕜 (V i) x) :
    extDeriv ω x (V · x) =
      (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) x (V i x)) -
        ∑ i : Fin (n + 1), ∑ j ≥ i,
          (-1) ^ (i + j : ℕ) •
            ω x (Matrix.vecCons (lieBracket 𝕜 (V i.castSucc) (V j.succ) x)
              (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← fderivWithin_univ,
    ← lieBracketWithin_univ] at *
  exact extDerivWithin_apply_vectorField hω hV (by simp)

/-- Let `ω` be a differentiable `n`-form and `V i` be `n + 1` differentiable vector fields.
If `V i` pairwise commute at `x`, i.e., $[V_i, V_j](x) = 0$ for all `i ≠ j`, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) = \sum_{i=0}^{n + 1} (-1)^i •
    D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)).
$$
-/
/-
**extDerivWithin_apply_vectorField_of_pairwise_commute** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：extDerivWithin_apply_vectorField_of_pairwise_commute {ω : E -> E [⋀^Fin n]
->L[𝕜] F} {V : Fin (n + 1) -> E -> E} (hω : DifferentiableWithinAt 𝕜 ω s x) (hV 
: forall i, DifferentiableWithinAt 𝕜 (V i) s x) (hsx : UniqueDiffWithinAt 𝕜 s x)
 (hcomm : Pairwise fun i j => lieBracketWithin 𝕜 (V i) (V j) s x = 0) : extDeriv
Within ω s x (V · x) = (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x => ω x (i.remo
veNth (V · x))) s x (V i x))
参数：n + 1；hω : DifferentiableWithinAt 𝕜 ω s x；hV : forall i, DifferentiableWithin
At 𝕜 (V i) s x；hsx : UniqueDiffWithinAt 𝕜 s x；hcomm : Pairwise fun i j => lieBra
cketWithin 𝕜 (V i) (V j) s x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extDerivWithin_apply`：extDerivWithin_apply (h : DifferentiableWithinAt 𝕜
 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x) (v : Fin (n + 1) -> E) : extDerivWithin 
ω s x v = …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `fderivWithin_continuousAlternatingMap_apply_const_apply`：fderivWithin_co
ntinuousAlternatingMap_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : 
DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Fin.removeNth_zero`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (f : (i : Fin
 (n + 1)) → α i), Fin.removeNth 0 f = Fin.tail f
· 使用定理 `fderivWithin_continuousAlternatingMap_apply_apply`：fderivWithin_continuo
usAlternatingMap_apply_apply (hf : DifferentiableWithinAt 𝕜 f s x) (hg : forall 
i, DifferentiableWithinAt 𝕜 (g i) s x) …
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extDerivWithin_apply_vectorField`：extDerivWithin_apply_vectorField {ω : 
E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V : Fin (n + 2) -> E -> E} (hω : Differentiable
WithinAt 𝕜 ω s x) (hV …
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `Fintype.sum_eq_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] 
[inst_1 : AddCommMonoid M] (f : α → M),   (∀ (a : α), f a = 0) → ∑ a, f a = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Let `ω` be a differentiable `n`-form and `V i` be `n + 1` differentiable vector 
fields.
If `V i` pairwise commute at `x`, i.e., $[V_i, V_j](x) = 0$ for all `i ≠ j`, the
n

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) = \sum_{i=0}^{n + 1} (-1)^i •
    D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\
right)(V_i(x)).
$$
-/
theorem extDerivWithin_apply_vectorField_of_pairwise_commute
    {ω : E → E [⋀^Fin n]→L[𝕜] F} {V : Fin (n + 1) → E → E}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : ∀ i, DifferentiableWithinAt 𝕜 (V i) s x)
    (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hcomm : Pairwise fun i j ↦ lieBracketWithin 𝕜 (V i) (V j) s x = 0) :
    extDerivWithin ω s x (V · x) =
      (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) s x (V i x)) := by
  cases n with
  | zero =>
    simp [extDerivWithin_apply, fderivWithin_continuousAlternatingMap_apply_const_apply,
      fderivWithin_continuousAlternatingMap_apply_apply, *]
  | succ n =>
    rw [extDerivWithin_apply_vectorField hω hV hsx, sub_eq_self]
    refine Fintype.sum_eq_zero _ fun i ↦ sum_eq_zero fun j hj ↦ ?_
    rw [hcomm (ne_of_lt <| by simpa using hj), (ω x).map_coord_zero 0] <;>
      simp

/-- Let `ω` be a differentiable `n`-form and `V i` be `n + 1` differentiable vector fields.
If `V i` pairwise commute at `x`, i.e., $[V_i, V_j](x) = 0$ for all `i ≠ j`, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) = \sum_{i=0}^{n + 1} (-1)^i •
    D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)).
$$
-/
/-
**extDeriv_apply_vectorField_of_pairwise_commute** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_apply_vectorField_of_pairwise_commute {ω : E -> E [⋀^Fin n]->L[𝕜]
 F} {V : Fin (n + 1) -> E -> E} (hω : DifferentiableAt 𝕜 ω x) (hV : forall i, Di
fferentiableAt 𝕜 (V i) x) (hcomm : Pairwise fun i j => lieBracket 𝕜 (V i) (V j) 
x = 0) : extDeriv ω x (V · x) = (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x => ω x (i.r
emoveNth (V · x))) x (V i x))
参数：n + 1；hω : DifferentiableAt 𝕜 ω x；hV : forall i, DifferentiableAt 𝕜 (V i) x；h
comm : Pairwise fun i j => lieBracket 𝕜 (V i) (V j) x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `extDerivWithin_apply_vectorField_of_pairwise_commute`：extDerivWithin_app
ly_vectorField_of_pairwise_commute {ω : E -> E [⋀^Fin n]->L[𝕜] F} {V : Fin (n + 
1) -> E -> E} (hω : DifferentiableWithinAt…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Let `ω` be a differentiable `n`-form and `V i` be `n + 1` differentiable vector 
fields.
If `V i` pairwise commute at `x`, i.e., $[V_i, V_j](x) = 0$ for all `i ≠ j`, the
n

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) = \sum_{i=0}^{n + 1} (-1)^i •
    D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\
right)(V_i(x)).
$$
-/
theorem extDeriv_apply_vectorField_of_pairwise_commute
    {ω : E → E [⋀^Fin n]→L[𝕜] F} {V : Fin (n + 1) → E → E}
    (hω : DifferentiableAt 𝕜 ω x) (hV : ∀ i, DifferentiableAt 𝕜 (V i) x)
    (hcomm : Pairwise fun i j ↦ lieBracket 𝕜 (V i) (V j) x = 0) :
    extDeriv ω x (V · x) =
      (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) x (V i x)) := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ, ← extDerivWithin_univ,
    ← fderivWithin_univ] at *
  exact extDerivWithin_apply_vectorField_of_pairwise_commute hω hV (by simp) hcomm
