/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Basic

/-!
# Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `Fin n` of cardinality `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this file, we implement this. The new power series is called `p.changeOrigin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open. All these arguments
require the target space to be complete, as otherwise the series might not converge.

### Main results

In a complete space, if a function admits a power series in a ball, then it is analytic at any
point `y` of this ball, and the power series there can be expressed in terms of the initial power
series `p` as `p.changeOrigin y`. See `HasFPowerSeriesOnBall.changeOrigin`. It follows in particular
that the set of points at which a given function is analytic is open, see `isOpen_analyticAt`.
-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal Topology
open Filter Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

section

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r : ℝ≥0}

/-- A term of `FormalMultilinearSeries.changeOriginSeries`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.changeOrigin x` is a formal multilinear series such that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense. Each term of `p.changeOrigin x`
is itself an analytic function of `x` given by the series `p.changeOriginSeries`. Each term in
`changeOriginSeries` is the sum of `changeOriginSeriesTerm`'s over all `s` of cardinality `l`.
The definition is such that `p.changeOriginSeriesTerm k l s hs (fun _ ↦ x) (fun _ ↦ y) =
p (k + l) (s.piecewise (fun _ ↦ x) (fun _ ↦ y))`
-/
/-
**FormalMultilinearSeries.changeOriginSeriesTerm** 是 Mathlib 中的一个定义，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：changeOriginSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card
 = l) : E [×l]->L[𝕜] E [×k]->L[𝕜] F
参数：k l : Nat；s : Finset (Fin (k + l))；hs : s.card = l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term of `FormalMultilinearSeries.changeOriginSeries`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence
,
`p.changeOrigin x` is a formal multilinear series such that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense. Each term of `p.
changeOrigin x`
is itself an analytic function of `x` given by the series `p.changeOriginSeries`
. Each term in
`changeOriginSeries` is the sum of `changeOriginSeriesTerm`'s over all `s` of ca
rdinality `l`.
The definition is such that `p.changeOriginSeriesTerm k l s hs (fun _ ↦ x) (fun 
_ ↦ y) =
p (k + l) (s.piecewise (fun _ ↦ x) (fun _ ↦ y))`
-/
def changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    E [×l]→L[𝕜] E [×k]→L[𝕜] F :=
  let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  a (p (k + l))
/-
**FormalMultilinearSeries.changeOriginSeriesTerm_apply** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：changeOriginSeriesTerm_apply (k l : Nat) (s : Finset (Fin (k + l))) (hs : 
s.card = l) (x y : E) : (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ =>
 y) = p (k + l) (s.piecewise (fun _ => x) fun _ => y)
参数：k l : Nat；s : Finset (Fin (k + l))；hs : s.card = l；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.curryFinFinset_apply_const`：curryFinFinset_appl
y_const (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G') (x y : G) : (curryFin
Finset 𝕜 G G' hk hl f (fun _ => x) fun _ …
-/
theorem changeOriginSeriesTerm_apply (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l)
    (x y : E) :
    (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y) =
      p (k + l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _

@[simp]
/-
**FormalMultilinearSeries.norm_changeOriginSeriesTerm** 是 Mathlib 中的一个定理，位于命名空间 
`FormalMultilinearSeries`。
形式化陈述：norm_changeOriginSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s
.card = l) : ‖p.changeOriginSeriesTerm k l s hs‖ = ‖p (k + l)‖
参数：k l : Nat；s : Finset (Fin (k + l))；hs : s.card = l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖ = ‖p (k + l)‖ := by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.norm_map]

@[simp]
/-
**FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm** 是 Mathlib 中的一个定理，位于命名空
间 `FormalMultilinearSeries`。
形式化陈述：nnnorm_changeOriginSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs :
 s.card = l) : ‖p.changeOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊
参数：k l : Nat；s : Finset (Fin (k + l))；hs : s.card = l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.nnnorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊ := by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.nnnorm_map]
/-
**FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm_apply_le** 是 Mathlib 中的一
个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：nnnorm_changeOriginSeriesTerm_apply_le (k l : Nat) (s : Finset (Fin (k + l
))) (hs : s.card = l) (x y : E) : ‖p.changeOriginSeriesTerm k l s hs (fun _ => x
) fun _ => y‖₊ <= ‖p (k + l)‖₊ * ‖x‖₊ ^ l * ‖y‖₊ ^ k
参数：k l : Nat；s : Finset (Fin (k + l))；hs : s.card = l；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm`：nnnorm_changeOrig
inSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) : ‖p.chang
eOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊
· 使用定理 `Fin.prod_const`：prod_const (n : Nat) (x : M) : ∏ _i : Fin n, x = x ^ n
· 使用定理 `ContinuousMultilinearMap.le_of_opNNNorm_le`：le_of_opNNNorm_le (f : Conti
nuousMultilinearMap 𝕜 E G) {C : Real>=0} (h : ‖f‖₊ <= C) (m : forall i, E i) : ‖
f m‖₊ <= C * ∏ i, ‖m i‖₊
· 使用定理 `ContinuousMultilinearMap.le_opNNNorm`：le_opNNNorm (f : ContinuousMultili
nearMap 𝕜 E G) (m : forall i, E i) : ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊
-/
theorem nnnorm_changeOriginSeriesTerm_apply_le (k l : ℕ) (s : Finset (Fin (k + l)))
    (hs : s.card = l) (x y : E) :
    ‖p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y‖₊ ≤
      ‖p (k + l)‖₊ * ‖x‖₊ ^ l * ‖y‖₊ ^ k := by
  rw [← p.nnnorm_changeOriginSeriesTerm k l s hs, ← Fin.prod_const, ← Fin.prod_const]
  apply ContinuousMultilinearMap.le_of_opNNNorm_le
  apply ContinuousMultilinearMap.le_opNNNorm

/-- The power series for `f.changeOrigin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.changeOrigin x` is a formal multilinear series such that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense. Its `k`-th term is the sum of
the series `p.changeOriginSeries k`. -/
/-
**FormalMultilinearSeries.changeOriginSeries** 是 Mathlib 中的一个定义，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：changeOriginSeries (k : Nat) : FormalMultilinearSeries 𝕜 E (E [×k]->L[𝕜] F
)
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series for `f.changeOrigin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence
,
`p.changeOrigin x` is a formal multilinear series such that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense. Its `k`-th term 
is the sum of
the series `p.changeOriginSeries k`.
-/
def changeOriginSeries (k : ℕ) : FormalMultilinearSeries 𝕜 E (E [×k]→L[𝕜] F) := fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2
/-
**FormalMultilinearSeries.nnnorm_changeOriginSeries_le_tsum** 是 Mathlib 中的一个定理，位
于命名空间 `FormalMultilinearSeries`。
形式化陈述：nnnorm_changeOriginSeries_le_tsum (k l : Nat) : ‖p.changeOriginSeries k l‖
₊ <= ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊
参数：k l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `nnnorm_sum_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAddComm
Group E] (s : Finset ι) (f : ι → E),   ‖∑ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm`：nnnorm_changeOrig
inSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) : ‖p.chang
eOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_changeOriginSeries_le_tsum (k l : ℕ) :
    ‖p.changeOriginSeries k l‖₊ ≤
      ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ :=
  (nnnorm_sum_le _ (fun t => changeOriginSeriesTerm p k l (Subtype.val t) t.prop)).trans_eq <| by
    simp_rw [tsum_fintype, nnnorm_changeOriginSeriesTerm (p := p) (k := k) (l := l)]
/-
**FormalMultilinearSeries.nnnorm_changeOriginSeries_apply_le_tsum** 是 Mathlib 中的
一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：nnnorm_changeOriginSeries_apply_le_tsum (k l : Nat) (x : E) : ‖p.changeOri
ginSeries k l fun _ => x‖₊ <= ∑' _ : { s : Finset (Fin (k + l)) // s.card = l },
 ‖p (k + l)‖₊ * ‖x‖₊ ^ l
参数：k l : Nat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.tsum_mul_right`：∀ {α : Type u_2} {L : SummationFilter α} (f : α →
 NNReal) (a : NNReal),   ∑'[L] (x : α), f x * a = (∑'[L] (x : α), f x) * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.prod_const`：prod_const (n : Nat) (x : M) : ∏ _i : Fin n, x = x ^ n
· 使用定理 `ContinuousMultilinearMap.le_of_opNNNorm_le`：le_of_opNNNorm_le (f : Conti
nuousMultilinearMap 𝕜 E G) {C : Real>=0} (h : ‖f‖₊ <= C) (m : forall i, E i) : ‖
f m‖₊ <= C * ∏ i, ‖m i‖₊
· 使用定理 `FormalMultilinearSeries.nnnorm_changeOriginSeries_le_tsum`：nnnorm_change
OriginSeries_le_tsum (k l : Nat) : ‖p.changeOriginSeries k l‖₊ <= ∑' _ : { s : F
inset (Fin (k + l)) // s.card = l }, ‖p (k + l)…
-/
theorem nnnorm_changeOriginSeries_apply_le_tsum (k l : ℕ) (x : E) :
    ‖p.changeOriginSeries k l fun _ => x‖₊ ≤
      ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ * ‖x‖₊ ^ l := by
  rw [NNReal.tsum_mul_right, ← Fin.prod_const]
  exact (p.changeOriginSeries k l).le_of_opNNNorm_le (p.nnnorm_changeOriginSeries_le_tsum _ _) _

/-- Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense.
-/
/-
**FormalMultilinearSeries.changeOrigin** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense.
-/
def changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun k => (p.changeOriginSeries k).sum x

/-- An auxiliary equivalence useful in the proofs about
`FormalMultilinearSeries.changeOriginSeries`: the set of triples `(k, l, s)`, where `s` is a
`Finset (Fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`Finset (Fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - Finset.card s, Finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps]
/-
**FormalMultilinearSeries.changeOriginIndexEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：changeOriginIndexEquiv : (Σ k l : Nat, { s : Finset (Fin (k + l)) // s.car
d = l }) ≃ Σ n : Nat, Finset (Fin n) where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary equivalence useful in the proofs about
`FormalMultilinearSeries.changeOriginSeries`: the set of triples `(k, l, s)`, wh
ere `s` is a
`Finset (Fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n,
 s)`, where `s` is a
`Finset (Fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n,
 s)` to
`(n - Finset.card s, Finset.card s, s)`. The actual definition is less readable 
because of problems
with non-definitional equalities.
-/
def changeOriginIndexEquiv :
    (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) ≃ Σ n : ℕ, Finset (Fin n) where
  toFun s := ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
        (finCongr <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subtype.coe_mk]
    -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
    -- formulate the generalized goal
    suffices ∀ k' l', k' = k → l' = l → ∀ (hkl : k + l = k' + l') (hs'),
        (⟨k', l', ⟨s.map (finCongr hkl).toEmbedding, hs'⟩⟩ :
          Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) = ⟨k, l, ⟨s, hs⟩⟩ by
      apply this <;> simp only [hs, add_tsub_cancel_right]
    simp
  right_inv := by
    rintro ⟨n, s⟩
    simp [tsub_add_cancel_of_le (card_finset_fin_le s), finCongr_eq_equivCast]
/-
**FormalMultilinearSeries.changeOriginSeriesTerm_changeOriginIndexEquiv_symm** 是
 Mathlib 中的一个引理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：changeOriginSeriesTerm_changeOriginIndexEquiv_symm (n t) : let s
参数：n t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finCongr_refl`：∀ {n : ℕ} (h : optParam (n = n) ⋯), finCongr h = Equiv.re
fl (Fin n)
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `FormalMultilinearSeries.changeOriginSeriesTerm_apply`：changeOriginSeries
Term_apply (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) (x y : E) : 
(p.changeOriginSeriesTerm k l s hs (fun _ …
-/
lemma changeOriginSeriesTerm_changeOriginIndexEquiv_symm (n t) :
    let s := changeOriginIndexEquiv.symm ⟨n, t⟩
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ ↦ x) (fun _ ↦ y) =
    p n (t.piecewise (fun _ ↦ x) fun _ ↦ y) := by
  have : ∀ (m) (hm : n = m), p n (t.piecewise (fun _ ↦ x) fun _ ↦ y) =
      p m ((t.map (finCongr hm).toEmbedding).piecewise (fun _ ↦ x) fun _ ↦ y) := by
    rintro m rfl
    simp +unfoldPartialApp [Finset.piecewise]
  simp_rw [changeOriginSeriesTerm_apply, eq_comm]; apply this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**FormalMultilinearSeries.changeOriginSeries_summable_aux** 是 Mathlib 中的一个定理，位于命
名空间 `FormalMultilinearSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem changeOriginSeries_summable_aux₁ {r r' : ℝ≥0} (hr : (r + r' : ℝ≥0∞) < p.radius) :
    Summable fun s : Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (s.1 + s.2.1)‖₊ * r ^ s.2.1 * r' ^ s.1 := by
  rw [← changeOriginIndexEquiv.symm.summable_iff]
  dsimp only [Function.comp_def, changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst]
  have : ∀ n : ℕ,
      HasSum (fun s : Finset (Fin n) => ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
        (‖p n‖₊ * (r + r') ^ n) := by
    intro n
    -- TODO: why `simp only [tsub_add_cancel_of_le (card_finset_fin_le _)]` fails?
    convert_to HasSum (fun s : Finset (Fin n) => ‖p n‖₊ * (r ^ s.card * r' ^ (n - s.card))) _
    · ext1 s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  refine NNReal.summable_sigma.2 ⟨fun n => (this n).summable, ?_⟩
  simp only [(this _).tsum_eq]
  exact p.summable_nnnorm_mul_pow hr
/-
**FormalMultilinearSeries.changeOriginSeries_summable_aux** 是 Mathlib 中的一个定理，位于命
名空间 `FormalMultilinearSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem changeOriginSeries_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
    Summable fun s : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (k + s.1)‖₊ * r ^ s.1 := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹
/-
**FormalMultilinearSeries.changeOriginSeries_summable_aux** 是 Mathlib 中的一个定理，位于命
名空间 `FormalMultilinearSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem changeOriginSeries_summable_aux₃ {r : ℝ≥0} (hr : ↑r < p.radius) (k : ℕ) :
    Summable fun l : ℕ => ‖p.changeOriginSeries k l‖₊ * r ^ l := by
  refine NNReal.summable_of_le
    (fun n => ?_) (NNReal.summable_sigma.1 <| p.changeOriginSeries_summable_aux₂ hr k).2
  simp only [NNReal.tsum_mul_right]
  gcongr
  apply p.nnnorm_changeOriginSeries_le_tsum
/-
**FormalMultilinearSeries.le_changeOriginSeries_radius** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：le_changeOriginSeries_radius (k : Nat) : p.radius <= (p.changeOriginSeries
 k).radius
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable_nnnorm`：le_radius_of_summa
ble_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r <= p.radius
· 使用定理 `FormalMultilinearSeries.changeOriginSeries_summable_aux₃`：changeOriginSe
ries_summable_aux₃ {r : Real>=0} (hr : ↑r < p.radius) (k : Nat) : Summable fun l
 : Nat => ‖p.changeOriginSeries k l‖₊ * r ^ l
-/
theorem le_changeOriginSeries_radius (k : ℕ) : p.radius ≤ (p.changeOriginSeries k).radius :=
  ENNReal.le_of_forall_nnreal_lt fun _r hr =>
    le_radius_of_summable_nnnorm _ (p.changeOriginSeries_summable_aux₃ hr k)
/-
**FormalMultilinearSeries.nnnorm_changeOrigin_le** 是 Mathlib 中的一个定理，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：nnnorm_changeOrigin_le (k : Nat) (h : (‖x‖₊ : Real>=0∞) < p.radius) : ‖p.c
hangeOrigin x k‖₊ <= ∑' s : Σ l : Nat, { s : Finset (Fin (k + l)) // s.card = l 
}, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1
参数：k : Nat；h : (‖x‖₊ : Real>=0∞) < p.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `tsum_of_nnnorm_bounded`：tsum_of_nnnorm_bounded {f : ι -> E} {g : ι -> Re
al>=0} {a : Real>=0} (hg : HasSum g a) (h : forall i, ‖f i‖₊ <= g i) : ‖∑' i : ι
, f i‖₊ <= a
· 使用定理 `FormalMultilinearSeries.changeOriginSeries_summable_aux₂`：changeOriginSe
ries_summable_aux₂ (hr : (r : Real>=0∞) < p.radius) (k : Nat) : Summable fun s :
 Σ l : Nat, { s : Finset (Fin (k + l)) // s.ca…
· 使用定理 `HasSum.sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] [ContinuousAdd α]   [RegularSpace α] {γ : β → Type 
u_…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.summable_sigma`：summable_sigma {β : α -> Type*} {f : (Σ x, β x) -
> Real>=0} : Summable f ↔ (forall x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun 
x => ∑' y, …
· 使用定理 `FormalMultilinearSeries.nnnorm_changeOriginSeries_apply_le_tsum`：nnnorm_
changeOriginSeries_apply_le_tsum (k l : Nat) (x : E) : ‖p.changeOriginSeries k l
 fun _ => x‖₊ <= ∑' _ : { s : Finset (Fin (k + l)) //…
-/
theorem nnnorm_changeOrigin_le (k : ℕ) (h : (‖x‖₊ : ℝ≥0∞) < p.radius) :
    ‖p.changeOrigin x k‖₊ ≤
      ∑' s : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1 := by
  refine tsum_of_nnnorm_bounded ?_ fun l => p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  have := p.changeOriginSeries_summable_aux₂ h k
  refine HasSum.sigma this.hasSum fun l => ?_
  exact ((NNReal.summable_sigma.1 this).1 l).hasSum

/-- The radius of convergence of `p.changeOrigin x` is at least `p.radius - ‖x‖`. In other words,
`p.changeOrigin x` is well defined on the largest ball contained in the original ball of
convergence. -/
/-
**FormalMultilinearSeries.changeOrigin_radius** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：changeOrigin_radius : p.radius - ‖x‖₊ <= (p.changeOrigin x).radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ENNReal.le_of_forall_pos_nnreal_lt`：le_of_forall_pos_nnreal_lt {x y : Re
al>=0∞} (h : forall r : Real>=0, 0 < r -> ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable_nnnorm`：le_radius_of_summa
ble_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r <= p.radius
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `FormalMultilinearSeries.nnnorm_changeOrigin_le`：nnnorm_changeOrigin_le (
k : Nat) (h : (‖x‖₊ : Real>=0∞) < p.radius) : ‖p.changeOrigin x k‖₊ <= ∑' s : Σ 
l : Nat, { s : Finset (Fin (k + l)) …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NNReal.summable_of_le`：summable_of_le {f g : β -> Real>=0} (hgf : forall
 b, g b <= f b) : Summable f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.summable_sigma`：summable_sigma {β : α -> Type*} {f : (Σ x, β x) -
> Real>=0} : Summable f ↔ (forall x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun 
x => ∑' y, …
· 使用定理 `FormalMultilinearSeries.changeOriginSeries_summable_aux₁`：changeOriginSe
ries_summable_aux₁ {r r' : Real>=0} (hr : (r + r' : Real>=0∞) < p.radius) : Summ
able fun s : Σ k l : Nat, { s : Finset (Fin (k…

--- 原说明 ---
The radius of convergence of `p.changeOrigin x` is at least `p.radius - ‖x‖`. In
 other words,
`p.changeOrigin x` is well defined on the largest ball contained in the original
 ball of
convergence.
-/
theorem changeOrigin_radius : p.radius - ‖x‖₊ ≤ (p.changeOrigin x).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _h0 hr => ?_
  rw [lt_tsub_iff_right, add_comm] at hr
  have hr' : (‖x‖₊ : ℝ≥0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have (k : ℕ) :
      ‖p.changeOrigin x k‖₊ * r ^ k ≤
        (∑' s : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1) *
          r ^ k := by
    gcongr; exact p.nnnorm_changeOrigin_le k hr'
  refine NNReal.summable_of_le this ?_
  simpa only [← NNReal.tsum_mul_right] using
    (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr)).2

/-- `derivSeries p` is a power series for `fderiv 𝕜 f` if `p` is a power series for `f`,
see `HasFPowerSeriesOnBall.fderiv`. -/
/-
**FormalMultilinearSeries.derivSeries** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultiline
arSeries`。
形式化陈述：derivSeries : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`derivSeries p` is a power series for `fderiv 𝕜 f` if `p` is a power series for 
`f`,
see `HasFPowerSeriesOnBall.fderiv`.
-/
def derivSeries : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) :=
  (continuousMultilinearCurryFin1 𝕜 E F : (E [×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
    |>.compFormalMultilinearSeries (p.changeOriginSeries 1)
/-
**FormalMultilinearSeries.radius_le_radius_derivSeries** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：radius_le_radius_derivSeries : p.radius <= p.derivSeries.radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FormalMultilinearSeries.le_changeOriginSeries_radius`：le_changeOriginSer
ies_radius (k : Nat) : p.radius <= (p.changeOriginSeries k).radius
· 使用引理 `FormalMultilinearSeries.radius_le_of_le`：radius_le_of_le {𝕜' E' F' : Typ
e*} [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E'] [No
rmedAddCommGroup F'] [NormedS…
· 使用定理 `ContinuousLinearMap.norm_compContinuousMultilinearMap_le`：norm_compConti
nuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) : 
‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f…
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem radius_le_radius_derivSeries : p.radius ≤ p.derivSeries.radius := by
  apply (p.le_changeOriginSeries_radius 1).trans (radius_le_of_le (fun n ↦ ?_))
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)
/-
**FormalMultilinearSeries.derivSeries_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：derivSeries_eq_zero {n : Nat} (hp : p (n + 1) = 0) : p.derivSeries n = 0
参数：hp : p (n + 1) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `FormalMultilinearSeries.congr_zero`：congr_zero (p : FormalMultilinearSer
ies 𝕜 E F) {k l : Nat} (h : k = l) (h' : p k = 0) : p l = 0
· 使用定理 `_private.Mathlib.Analysis.Analytic.ChangeOrigin.0.FormalMultilinearSerie
s.derivSeries_eq_zero._abel_1_2`：∀ {n : ℕ}, n + 1 = 1 + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem derivSeries_eq_zero {n : ℕ} (hp : p (n + 1) = 0) : p.derivSeries n = 0 := by
  suffices p.changeOriginSeries 1 n = 0 by ext v; simp [derivSeries, this]
  apply Finset.sum_eq_zero (fun s hs ↦ ?_)
  have : p (1 + n) = 0 := p.congr_zero (by abel) hp
  simp [changeOriginSeriesTerm, this]

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E}

/-
**FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin** 是 Mathlib 中的一个定理，
位于命名空间 `FormalMultilinearSeries`。
形式化陈述：hasFPowerSeriesOnBall_changeOrigin (k : Nat) (hr : 0 < p.radius) : HasFPow
erSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius
参数：k : Nat；hr : 0 < p.radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.le_changeOriginSeries_radius`：le_changeOriginSer
ies_radius (k : Nat) : p.radius <= (p.changeOriginSeries k).radius
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.instFirstCountableTopologyForallOfCountable`：∀ {ι : Typ
e u_1} {X : ι → Type u_2} [Countable ι] [inst : (i : ι) → TopologicalSpace (X i)
]   [∀ (i : ι), FirstCountableTopology (X i)], Fir…
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem hasFPowerSeriesOnBall_changeOrigin (k : ℕ) (hr : 0 < p.radius) :
    HasFPowerSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius :=
  have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFPowerSeriesOnBall (hr.trans_le this)).mono hr this

/-- Summing the series `p.changeOrigin x` at a point `y` gives back `p (x + y)`. -/
/-
**FormalMultilinearSeries.changeOrigin_eval** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：changeOrigin_eval (h : (‖x‖₊ + ‖y‖₊ : Real>=0∞) < p.radius) : (p.changeOri
gin x).sum y = p.sum (x + y)
参数：h : (‖x‖₊ + ‖y‖₊ : Real>=0∞) < p.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `FormalMultilinearSeries.changeOrigin_radius`：changeOrigin_radius : p.rad
ius - ‖x‖₊ <= (p.changeOrigin x).radius
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nnnorm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E),
 ‖a + b‖₊ ≤ ‖a‖₊ + ‖b‖₊
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Summable.of_nnnorm_bounded`：Summable.of_nnnorm_bounded {f : ι -> E} {g :
 ι -> Real>=0} (hg : Summable g) (h : forall i, ‖f i‖₊ <= g i) : Summable f
· 使用定理 `FormalMultilinearSeries.changeOriginSeries_summable_aux₁`：changeOriginSe
ries_summable_aux₁ {r r' : Real>=0} (hr : (r + r' : Real>=0∞) < p.radius) : Summ
able fun s : Σ k l : Nat, { s : Finset (Fin (k…
· 使用定理 `FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm_apply_le`：nnnorm_c
hangeOriginSeriesTerm_apply_le (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.ca
rd = l) (x y : E) : ‖p.changeOriginSeriesTerm k l s …
· 使用定理 `HasSum.sigma_of_hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommM
onoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α] [T3Space α]   {γ : β → 
Type u_4} {f…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
Summing the series `p.changeOrigin x` at a point `y` gives back `p (x + y)`.
-/
theorem changeOrigin_eval (h : (‖x‖₊ + ‖y‖₊ : ℝ≥0∞) < p.radius) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  have x_mem_ball : x ∈ Metric.eball (0 : E) p.radius :=
    mem_eball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y ∈ Metric.eball (0 : E) (p.changeOrigin x).radius := by
    refine mem_eball_zero_iff.2 (lt_of_lt_of_le ?_ p.changeOrigin_radius)
    rwa [lt_tsub_iff_right, add_comm]
  have x_add_y_mem_ball : x + y ∈ Metric.eball (0 : E) p.radius := by
    refine mem_eball_zero_iff.2 (lt_of_le_of_lt ?_ h)
    exact mod_cast nnnorm_add_le x y
  set f : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) → F := fun s =>
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have hsf : Summable f := by
    refine .of_nnnorm_bounded (p.changeOriginSeries_summable_aux₁ h) ?_
    rintro ⟨k, l, s, hs⟩
    dsimp only [Subtype.coe_mk]
    exact p.nnnorm_changeOriginSeriesTerm_apply_le _ _ _ _ _ _
  have hf : HasSum f ((p.changeOrigin x).sum y) := by
    refine HasSum.sigma_of_hasSum ((p.changeOrigin x).summable y_mem_ball).hasSum (fun k => ?_) hsf
    · dsimp +instances only [f]
      refine ContinuousMultilinearMap.hasSum_eval ?_ _
      have := (p.hasFPowerSeriesOnBall_changeOrigin k h.pos).hasSum x_mem_ball
      rw [zero_add] at this
      refine HasSum.sigma_of_hasSum this (fun l => ?_) ?_
      · simp only [changeOriginSeries, sum_apply]
        apply hasSum_fintype
      · refine .of_nnnorm_bounded
          (p.changeOriginSeries_summable_aux₂ (mem_eball_zero_iff.1 x_mem_ball) k)
            fun s => ?_
        refine (ContinuousMultilinearMap.le_opNNNorm _ _).trans_eq ?_
        simp
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine HasSum.sigma_of_hasSum
    (p.hasSum x_add_y_mem_ball) (fun n => ?_) (changeOriginIndexEquiv.symm.summable_iff.2 hsf)
  rw [← Pi.add_def, (p n).map_add_univ (fun _ => x) fun _ => y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype (fun c => f (changeOriginIndexEquiv.symm ⟨n, c⟩))

/-- Power series terms are analytic as we vary the origin -/
/-
**FormalMultilinearSeries.analyticAt_changeOrigin** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：analyticAt_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius
 > 0) (n : Nat) : AnalyticAt 𝕜 (fun x => p.changeOrigin x n) 0
参数：p : FormalMultilinearSeries 𝕜 E F；rp : p.radius > 0；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesOnBall.analyticAt`：HasFPowerSeriesOnBall.analyticAt (hf :
 HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin`：hasFPowerSer
iesOnBall_changeOrigin (k : Nat) (hr : 0 < p.radius) : HasFPowerSeriesOnBall (fu
n x => p.changeOrigin x k) (p.changeOriginSeries…

--- 原说明 ---
Power series terms are analytic as we vary the origin
-/
theorem analyticAt_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius > 0) (n : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ p.changeOrigin x n) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p n rp).analyticAt

end FormalMultilinearSeries


section

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
  {x y : E} {r : ℝ≥0∞}

/-- If a function admits a power series expansion `p` within a set `s` on a ball `B (x, r)`, then
it also admits a power series on any subball of this ball (even with a different center provided
it belongs to `s`), given by `p.changeOrigin`. -/
/-
**HasFPowerSeriesWithinOnBall.changeOrigin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.changeOrigin (hf : HasFPowerSeriesWithinOnBall
 f p s x r) (h : ‖y‖ₑ < r) (hy : x + y in insert x s) : HasFPowerSeriesWithinOnB
all f (p.changeOrigin y) s (x + y) (r - ‖y‖ₑ) where r_le
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : ‖y‖ₑ < r；hy : x + y in insert 
x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `FormalMultilinearSeries.changeOrigin_radius`：changeOrigin_radius : p.rad
ius - ‖x‖₊ <= (p.changeOrigin x).radius
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.changeOrigin_eval`：changeOrigin_eval (h : (‖x‖₊ 
+ ‖y‖₊ : Real>=0∞) < p.radius) : (p.changeOrigin x).sum y = p.sum (x + y)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `HasFPowerSeriesWithinOnBall.sum`：HasFPowerSeriesWithinOnBall.sum (h : Ha
sFPowerSeriesWithinOnBall f p s x r) {y : E} (h'y : x + y in insert x s) (hy : y
 in Metric.eball (0 :…
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If a function admits a power series expansion `p` within a set `s` on a ball `B 
(x, r)`, then
it also admits a power series on any subball of this ball (even with a different
 center provided
it belongs to `s`), given by `p.changeOrigin`.
-/
theorem HasFPowerSeriesWithinOnBall.changeOrigin (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (h : ‖y‖ₑ < r) (hy : x + y ∈ insert x s) :
    HasFPowerSeriesWithinOnBall f (p.changeOrigin y) s (x + y) (r - ‖y‖ₑ) where
  r_le := by
    apply le_trans _ p.changeOrigin_radius
    exact tsub_le_tsub hf.r_le le_rfl
  r_pos := by simp [h]
  hasSum {z} h'z hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff, lt_tsub_iff_right, add_comm] at hz
      rw [p.changeOrigin_eval (hz.trans_le hf.r_le), add_assoc, hf.sum]
      · have : insert (x + y) s ⊆ insert (x + y) (insert x s) := by
          apply insert_subset_insert (subset_insert _ _)
        rw [insert_eq_of_mem hy] at this
        apply this
        simpa [add_assoc] using h'z
      exact mem_eball_zero_iff.2 (lt_of_le_of_lt (enorm_add_le _ _) hz)
    rw [this]
    apply (p.changeOrigin y).hasSum
    refine Metric.eball_subset_eball (le_trans ?_ p.changeOrigin_radius) hz
    exact tsub_le_tsub hf.r_le le_rfl

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.changeOrigin`.
-/
/-
**HasFPowerSeriesOnBall.changeOrigin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.changeOrigin (hf : HasFPowerSeriesOnBall f p x r) (h
 : (‖y‖₊ : Real>=0∞) < r) : HasFPowerSeriesOnBall f (p.changeOrigin y) (x + y) (
r - ‖y‖₊)
参数：hf : HasFPowerSeriesOnBall f p x r；h : (‖y‖₊ : Real>=0∞) < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.changeOrigin`：HasFPowerSeriesWithinOnBall.ch
angeOrigin (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : ‖y‖ₑ < r) (hy : x +
 y in insert x s) : HasFPowerS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s

--- 原说明 ---
If a function admits a power series expansion `p` on a ball `B (x, r)`, then it 
also admits a
power series on any subball of this ball (even with a different center), given b
y `p.changeOrigin`.
-/
theorem HasFPowerSeriesOnBall.changeOrigin (hf : HasFPowerSeriesOnBall f p x r)
    (h : (‖y‖₊ : ℝ≥0∞) < r) : HasFPowerSeriesOnBall f (p.changeOrigin y) (x + y) (r - ‖y‖₊) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.changeOrigin h (by simp)

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
/-
**HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem (hf : HasFPowerSeriesW
ithinOnBall f p s x r) (h : y in insert x s inter Metric.eball x r) : AnalyticWi
thinAt 𝕜 f s y
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : y in insert x s inter Metric.e
ball x r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HasFPowerSeriesWithinOnBall.changeOrigin`：HasFPowerSeriesWithinOnBall.ch
angeOrigin (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : ‖y‖ₑ < r) (hy : x +
 y in insert x s) : HasFPowerS…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt`：HasFPowerSeriesWithinOnBal
l.analyticWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : AnalyticWithin
At 𝕜 f s x

--- 原说明 ---
If a function admits a power series expansion `p` on an open ball `B (x, r)`, th
en
it is analytic at every point of this ball.
-/
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem
    (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (h : y ∈ insert x s ∩ Metric.eball x r) : AnalyticWithinAt 𝕜 f s y := by
  have : (‖y - x‖₊ : ℝ≥0∞) < r := by simpa [edist_eq_enorm_sub] using! h.2
  have := hf.changeOrigin this (by simpa using! h.1)
  rw [add_sub_cancel] at this
  exact this.analyticWithinAt

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
/-
**HasFPowerSeriesOnBall.analyticAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.analyticAt_of_mem (hf : HasFPowerSeriesOnBall f p x 
r) (h : y in Metric.eball x r) : AnalyticAt 𝕜 f y
参数：hf : HasFPowerSeriesOnBall f p x r；h : y in Metric.eball x r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem`：HasFPowerSeriesWith
inOnBall.analyticWithinAt_of_mem (hf : HasFPowerSeriesWithinOnBall f p s x r) (h
 : y in insert x s inter Metric.eball x r…
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a

--- 原说明 ---
If a function admits a power series expansion `p` on an open ball `B (x, r)`, th
en
it is analytic at every point of this ball.
-/
theorem HasFPowerSeriesOnBall.analyticAt_of_mem (hf : HasFPowerSeriesOnBall f p x r)
    (h : y ∈ Metric.eball x r) : AnalyticAt 𝕜 f y := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  rw [← analyticWithinAt_univ]
  exact hf.analyticWithinAt_of_mem (by simpa using h)
/-
**HasFPowerSeriesWithinOnBall.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.analyticOn (hf : HasFPowerSeriesWithinOnBall f
 p s x r) : AnalyticOn 𝕜 f (insert x s inter Metric.eball x r)
参数：hf : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticWithinAt.mono`：AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f 
s x) (h : t subseteq s) : AnalyticWithinAt 𝕜 f t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `analyticWithinAt_insert`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem`：HasFPowerSeriesWith
inOnBall.analyticWithinAt_of_mem (hf : HasFPowerSeriesWithinOnBall f p s x r) (h
 : y in insert x s inter Metric.eball x r…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem HasFPowerSeriesWithinOnBall.analyticOn (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    AnalyticOn 𝕜 f (insert x s ∩ Metric.eball x r) :=
  fun _ hy ↦ ((analyticWithinAt_insert (y := x)).2 (hf.analyticWithinAt_of_mem hy)).mono
    inter_subset_left
/-
**HasFPowerSeriesOnBall.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.analyticOnNhd (hf : HasFPowerSeriesOnBall f p x r) :
 AnalyticOnNhd 𝕜 f (Metric.eball x r)
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesOnBall.analyticAt_of_mem`：HasFPowerSeriesOnBall.analyticA
t_of_mem (hf : HasFPowerSeriesOnBall f p x r) (h : y in Metric.eball x r) : Anal
yticAt 𝕜 f y
-/
theorem HasFPowerSeriesOnBall.analyticOnNhd (hf : HasFPowerSeriesOnBall f p x r) :
    AnalyticOnNhd 𝕜 f (Metric.eball x r) :=
  fun _y hy => hf.analyticAt_of_mem hy

variable (𝕜 f) in
/-- For any function `f` from a normed vector space to a Banach space, the set of points `x` such
that `f` is analytic at `x` is open. -/
/-
**isOpen_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.analyticAt_of_mem`：HasFPowerSeriesOnBall.analyticA
t_of_mem (hf : HasFPowerSeriesOnBall f p x r) (h : y in Metric.eball x r) : Anal
yticAt 𝕜 f y

--- 原说明 ---
For any function `f` from a normed vector space to a Banach space, the set of po
ints `x` such
that `f` is analytic at `x` is open.
-/
theorem isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.analyticAt_of_mem hy
/-
**AnalyticAt.eventually_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.eventually_analyticAt (h : AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x
, AnalyticAt 𝕜 f y
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_analyticAt`：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }
-/
theorem AnalyticAt.eventually_analyticAt (h : AnalyticAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, AnalyticAt 𝕜 f y :=
  (isOpen_analyticAt 𝕜 f).mem_nhds h
/-
**AnalyticAt.exists_mem_nhds_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.exists_mem_nhds_analyticOnNhd (h : AnalyticAt 𝕜 f x) : exists s
 in 𝓝 x, AnalyticOnNhd 𝕜 f s
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
· 使用定理 `AnalyticAt.eventually_analyticAt`：AnalyticAt.eventually_analyticAt (h : 
AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y
-/
theorem AnalyticAt.exists_mem_nhds_analyticOnNhd (h : AnalyticAt 𝕜 f x) :
    ∃ s ∈ 𝓝 x, AnalyticOnNhd 𝕜 f s :=
  h.eventually_analyticAt.exists_mem

/-- If we're analytic at a point, we're analytic in a nonempty ball -/
/-
**AnalyticAt.exists_ball_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.exists_ball_analyticOnNhd (h : AnalyticAt 𝕜 f x) : exists r : R
eal, 0 < r ∧ AnalyticOnNhd 𝕜 f (Metric.ball x r)
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `isOpen_analyticAt`：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }

--- 原说明 ---
If we're analytic at a point, we're analytic in a nonempty ball
-/
theorem AnalyticAt.exists_ball_analyticOnNhd (h : AnalyticAt 𝕜 f x) :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd 𝕜 f (Metric.ball x r) :=
  Metric.isOpen_iff.mp (isOpen_analyticAt _ _) _ h

/-- Sum of series is analytic on its ball of convergence. -/
/-
**FormalMultilinearSeries.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [CompleteSpace F]   {p : FormalM
ultilinearSeries 𝕜 E F}, AnalyticOnNhd 𝕜 p.sum (Metric.eball 0 p.radius)
参数：Metric.eball 0 p.radius。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_zero`：eball_zero : eball x 0 = ∅
· 使用定理 `HasFPowerSeriesOnBall.analyticOnNhd`：HasFPowerSeriesOnBall.analyticOnNhd
 (hf : HasFPowerSeriesOnBall f p x r) : AnalyticOnNhd 𝕜 f (Metric.eball x r)
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
Sum of series is analytic on its ball of convergence.
-/
protected theorem FormalMultilinearSeries.analyticOnNhd :
    AnalyticOnNhd 𝕜 p.sum (Metric.eball 0 p.radius) := by
  by_cases hr : p.radius = 0
  · simp [hr]
  exact (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (pos_of_ne_zero hr)).analyticOnNhd

end

