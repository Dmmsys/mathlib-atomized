/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Smoothness of series

We show that series of functions are differentiable, or smooth, when each individual
function in the series is and additionally suitable uniform summable bounds are satisfied.

More specifically,
* `differentiable_tsum` ensures that a series of differentiable functions is differentiable.
* `contDiff_tsum` ensures that a series of `C^n` functions is `C^n`.

We also give versions of these statements which are localized to a set.
-/

public section


open Set Metric TopologicalSpace Function Asymptotics Filter

open scoped Topology NNReal

variable {α β 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

/-! ### Differentiability -/

variable [NormedSpace 𝕜 F]
variable {f : α → E → F} {f' : α → E → E →L[𝕜] F} {g : α → 𝕜 → F} {g' : α → 𝕜 → F} {v : ℕ → α → ℝ}
  {s : Set E} {t : Set 𝕜} {x₀ x : E} {y₀ y : 𝕜} {N : ℕ∞}

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series converges everywhere on the set. -/
/-
**summable_of_summable_hasFDerivAt_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：summable_of_summable_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs :
 IsOpen s) (h's : IsPreconnected s) (hf : forall n x, x in s -> HasFDerivAt (f n
) (f' n x) x) (hf' : forall n x, x in s -> ‖f' n x‖ <= u n) (hx₀ : x₀ in s) (hf0
 : Summable (f · x₀)) (hx : x in s) : Summable fun n => f n x
参数：hu : Summable u；hs : IsOpen s；h's : IsPreconnected s；hf : forall n x, x in s 
-> HasFDerivAt (f n) (f' n x) x；hf' : forall n x, x in s -> ‖f' n x‖ <= u n；hx₀ 
: x₀ in s；hf0 : Summable (f · x₀)；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `summable_iff_cauchySeq_finset`：∀ {α : Type u_1} {β : Type u_2} [inst : U
niformSpace α] [inst_1 : AddCommMonoid α] [CompleteSpace α] {f : β → α},   Summa
ble f ↔ CauchySeq f…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TendstoUniformlyOn.uniformCauchySeqOn`：TendstoUniformlyOn.uniformCauchyS
eqOn (hF : TendstoUniformlyOn F f p s) : UniformCauchySeqOn F p s
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `cauchy_map_of_uniformCauchySeqOn_fderiv`：cauchy_map_of_uniformCauchySeqO
n_fderiv {s : Set E} (hs : IsOpen s) (h's : IsPreconnected s) (hf' : UniformCauc
hySeqOn f' l s) (hf : forall …
· 使用定理 `HasFDerivAt.fun_sum`：HasFDerivAt.fun_sum (h : forall i in u, HasFDerivAt
 (A i) (A' i) x) : HasFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x

--- 原说明 ---
Consider a series of functions `∑' n, f n x` on a preconnected open set. If the 
series converges
at a point, and all functions in the series are differentiable with a summable b
ound on the
derivatives, then the series converges everywhere on the set.
-/
theorem summable_of_summable_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n) (hx₀ : x₀ ∈ s) (hf0 : Summable (f · x₀))
    (hx : x ∈ s) : Summable fun n => f n x := by
  have := Classical.decEq α
  rw [summable_iff_cauchySeq_finset] at hf0 ⊢
  have A : UniformCauchySeqOn (fun t : Finset α => fun x => ∑ i ∈ t, f' i x) atTop s :=
    (tendstoUniformlyOn_tsum hu hf').uniformCauchySeqOn
  refine cauchy_map_of_uniformCauchySeqOn_fderiv (f := fun t x ↦ ∑ i ∈ t, f i x)
    hs h's A (fun t y hy => ?_) hx₀ hx hf0
  exact HasFDerivAt.fun_sum fun i _ => hf i y hy

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series converges everywhere on the set. -/
/-
**summable_of_summable_hasDerivAt_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：summable_of_summable_hasDerivAt_of_isPreconnected (hu : Summable u) (ht : 
IsOpen t) (h't : IsPreconnected t) (hg : forall n y, y in t -> HasDerivAt (g n) 
(g' n y) y) (hg' : forall n y, y in t -> ‖g' n y‖ <= u n) (hy₀ : y₀ in t) (hg0 :
 Summable (g · y₀)) (hy : y in t) : Summable fun n => g n y
参数：hu : Summable u；ht : IsOpen t；h't : IsPreconnected t；hg : forall n y, y in t 
-> HasDerivAt (g n) (g' n y) y；hg' : forall n y, y in t -> ‖g' n y‖ <= u n；hy₀ :
 y₀ in t；hg0 : Summable (g · y₀)；hy : y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `summable_of_summable_hasFDerivAt_of_isPreconnected`：summable_of_summable
_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s) (h's : IsPrecon
nected s) (hf : forall n x, x in s -> Ha…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…

--- 原说明 ---
Consider a series of functions `∑' n, f n x` on a preconnected open set. If the 
series converges
at a point, and all functions in the series are differentiable with a summable b
ound on the
derivatives, then the series converges everywhere on the set.
-/
theorem summable_of_summable_hasDerivAt_of_isPreconnected (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n) (hy₀ : y₀ ∈ t) (hg0 : Summable (g · y₀))
    (hy : y ∈ t) : Summable fun n => g n y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine summable_of_summable_hasFDerivAt_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  simpa

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series is differentiable on the set and its derivative is the sum of the
derivatives. -/
/-
**hasFDerivAt_tsum_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_tsum_of_isPreconnected (hu : Summable u) (hs : IsOpen s) (h's 
: IsPreconnected s) (hf : forall n x, x in s -> HasFDerivAt (f n) (f' n x) x) (h
f' : forall n x, x in s -> ‖f' n x‖ <= u n) (hx₀ : x₀ in s) (hf0 : Summable fun 
n => f n x₀) (hx : x in s) : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x
参数：hu : Summable u；hs : IsOpen s；h's : IsPreconnected s；hf : forall n x, x in s 
-> HasFDerivAt (f n) (f' n x) x；hf' : forall n x, x in s -> ‖f' n x‖ <= u n；hx₀ 
: x₀ in s；hf0 : Summable fun n => f n x₀；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `summable_of_summable_hasFDerivAt_of_isPreconnected`：summable_of_summable
_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s) (h's : IsPrecon
nected s) (hf : forall n x, x in s -> Ha…
· 使用定理 `hasFDerivAt_of_tendstoUniformlyOn`：hasFDerivAt_of_tendstoUniformlyOn [Ne
Bot l] {s : Set E} (hs : IsOpen s) (hf' : TendstoUniformlyOn f' g' l s) (hf : fo
rall n : ι, forall x : …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `HasFDerivAt.fun_sum`：HasFDerivAt.fun_sum (h : forall i in u, HasFDerivAt
 (A i) (A' i) x) : HasFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x

--- 原说明 ---
Consider a series of functions `∑' n, f n x` on a preconnected open set. If the 
series converges
at a point, and all functions in the series are differentiable with a summable b
ound on the
derivatives, then the series is differentiable on the set and its derivative is 
the sum of the
derivatives.
-/
theorem hasFDerivAt_tsum_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n) (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    (hx : x ∈ s) : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  have A :
    ∀ x : E, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, f n x) atTop (𝓝 (∑' n, f n x)) := by
    intro y hy
    apply Summable.hasSum
    exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  refine hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hf')
    (fun t y hy => ?_) A hx
  exact HasFDerivAt.fun_sum fun n _ => hf n y hy

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series is differentiable on the set and its derivative is the sum of the
derivatives. -/
/-
**hasDerivAt_tsum_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_tsum_of_isPreconnected (hu : Summable u) (ht : IsOpen t) (h't :
 IsPreconnected t) (hg : forall n y, y in t -> HasDerivAt (g n) (g' n y) y) (hg'
 : forall n y, y in t -> ‖g' n y‖ <= u n) (hy₀ : y₀ in t) (hg0 : Summable fun n 
=> g n y₀) (hy : y in t) : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y
参数：hu : Summable u；ht : IsOpen t；h't : IsPreconnected t；hg : forall n y, y in t 
-> HasDerivAt (g n) (g' n y) y；hg' : forall n y, y in t -> ‖g' n y‖ <= u n；hy₀ :
 y₀ in t；hg0 : Summable fun n => g n y₀；hy : y in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.map_tsum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `hasFDerivAt_tsum_of_isPreconnected`：hasFDerivAt_tsum_of_isPreconnected (
hu : Summable u) (hs : IsOpen s) (h's : IsPreconnected s) (hf : forall n x, x in
 s -> HasFDerivAt (f n) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…

--- 原说明 ---
Consider a series of functions `∑' n, f n x` on a preconnected open set. If the 
series converges
at a point, and all functions in the series are differentiable with a summable b
ound on the
derivatives, then the series is differentiable on the set and its derivative is 
the sum of the
derivatives.
-/
theorem hasDerivAt_tsum_of_isPreconnected (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n) (hy₀ : y₀ ∈ t) (hg0 : Summable fun n => g n y₀)
    (hy : y ∈ t) : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg ⊢
  convert! hasFDerivAt_tsum_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  · exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1).map_tsum <|
      .of_norm_bounded hu fun n ↦ hg' n y hy
  · simpa

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
/-
**summable_of_summable_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_summable_hasFDerivAt (hu : Summable u) (hf : forall n x, HasFD
erivAt (f n) (f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) (hf0 : Summable fun
 n => f n x₀) (x : E) : Summable fun n => f n x
参数：hu : Summable u；hf : forall n x, HasFDerivAt (f n) (f' n x) x；hf' : forall n 
x, ‖f' n x‖ <= u n；hf0 : Summable fun n => f n x₀；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_summable_hasFDerivAt_of_isPreconnected`：summable_of_summable
_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s) (h's : IsPrecon
nected s) (hf : forall n x, x in s -> Ha…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound 
on the derivatives,
then the series converges everywhere.
-/
theorem summable_of_summable_hasFDerivAt (hu : Summable u)
    (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x) (hf' : ∀ n x, ‖f' n x‖ ≤ u n)
    (hf0 : Summable fun n => f n x₀) (x : E) : Summable fun n => f n x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  exact summable_of_summable_hasFDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
/-
**summable_of_summable_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_summable_hasDerivAt (hu : Summable u) (hg : forall n y, HasDer
ivAt (g n) (g' n y) y) (hg' : forall n y, ‖g' n y‖ <= u n) (hg0 : Summable fun n
 => g n y₀) (y : 𝕜) : Summable fun n => g n y
参数：hu : Summable u；hg : forall n y, HasDerivAt (g n) (g' n y) y；hg' : forall n y
, ‖g' n y‖ <= u n；hg0 : Summable fun n => g n y₀；y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `summable_of_summable_hasDerivAt_of_isPreconnected`：summable_of_summable_
hasDerivAt_of_isPreconnected (hu : Summable u) (ht : IsOpen t) (h't : IsPreconne
cted t) (hg : forall n y, y in t -> Has…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `Convex.instPathConnectedSpace`：∀ {𝕜 : Type u_3} [inst : NontriviallyNorm
edField 𝕜] [IsRCLikeNormedField 𝕜], PathConnectedSpace 𝕜
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound 
on the derivatives,
then the series converges everywhere.
-/
theorem summable_of_summable_hasDerivAt (hu : Summable u)
    (hg : ∀ n y, HasDerivAt (g n) (g' n y) y) (hg' : ∀ n y, ‖g' n y‖ ≤ u n)
    (hg0 : Summable fun n => g n y₀) (y : 𝕜) : Summable fun n => g n y := by
  exact summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hg n x) (fun n x _ => hg' n x) (mem_univ _) hg0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
/-
**hasFDerivAt_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_tsum (hu : Summable u) (hf : forall n x, HasFDerivAt (f n) (f'
 n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) (hf0 : Summable fun n => f n x₀) (x
 : E) : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x
参数：hu : Summable u；hf : forall n x, HasFDerivAt (f n) (f' n x) x；hf' : forall n 
x, ‖f' n x‖ <= u n；hf0 : Summable fun n => f n x₀；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_tsum_of_isPreconnected`：hasFDerivAt_tsum_of_isPreconnected (
hu : Summable u) (hs : IsOpen s) (h's : IsPreconnected s) (hf : forall n x, x in
 s -> HasFDerivAt (f n) …
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound 
on the derivatives,
then the series is differentiable and its derivative is the sum of the derivativ
es.
-/
theorem hasFDerivAt_tsum (hu : Summable u) (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, ‖f' n x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
/-
**hasDerivAt_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_tsum (hu : Summable u) (hg : forall n y, HasDerivAt (g n) (g' n
 y) y) (hg' : forall n y, ‖g' n y‖ <= u n) (hg0 : Summable fun n => g n y₀) (y :
 𝕜) : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y
参数：hu : Summable u；hg : forall n y, HasDerivAt (g n) (g' n y) y；hg' : forall n y
, ‖g' n y‖ <= u n；hg0 : Summable fun n => g n y₀；y : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_tsum_of_isPreconnected`：hasDerivAt_tsum_of_isPreconnected (hu
 : Summable u) (ht : IsOpen t) (h't : IsPreconnected t) (hg : forall n y, y in t
 -> HasDerivAt (g n) (g…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `Convex.instPathConnectedSpace`：∀ {𝕜 : Type u_3} [inst : NontriviallyNorm
edField 𝕜] [IsRCLikeNormedField 𝕜], PathConnectedSpace 𝕜
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound 
on the derivatives,
then the series is differentiable and its derivative is the sum of the derivativ
es.
-/
theorem hasDerivAt_tsum (hu : Summable u) (hg : ∀ n y, HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, ‖g' n y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n y _ => hg n y) (fun n y _ => hg' n y) (mem_univ _) hg0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If all functions in the series are differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there is no pointwise
convergence then the series is zero everywhere so the result still holds. -/
/-
**differentiable_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_tsum (hu : Summable u) (hf : forall n x, HasFDerivAt (f n) 
(f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) : Differentiable 𝕜 fun y => ∑' n
, f n y
参数：hu : Summable u；hf : forall n x, HasFDerivAt (f n) (f' n x) x；hf' : forall n 
x, ‖f' n x‖ <= u n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFDerivAt_tsum`：hasFDerivAt_tsum (hu : Summable u) (hf : forall n x, H
asFDerivAt (f n) (f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) (hf0 : Summable
 fun n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c

--- 原说明 ---
Consider a series of functions `∑' n, f n x`. If all functions in the series are
 differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there 
is no pointwise
convergence then the series is zero everywhere so the result still holds.
-/
theorem differentiable_tsum (hu : Summable u) (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, ‖f' n x‖ ≤ u n) : Differentiable 𝕜 fun y => ∑' n, f n y := by
  by_cases! h : ∃ x₀, Summable fun n => f n x₀
  · rcases h with ⟨x₀, hf0⟩
    intro x
    exact (hasFDerivAt_tsum hu hf hf' hf0 x).differentiableAt
  · have : (fun x => ∑' n, f n x) = 0 := by ext1 x; exact tsum_eq_zero_of_not_summable (h x)
    rw [this]
    exact differentiable_const 0

/-- Consider a series of functions `∑' n, f n x`. If all functions in the series are differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there is no pointwise
convergence then the series is zero everywhere so the result still holds. -/
/-
**differentiable_tsum'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_tsum' (hu : Summable u) (hg : forall n y, HasDerivAt (g n) 
(g' n y) y) (hg' : forall n y, ‖g' n y‖ <= u n) : Differentiable 𝕜 fun z => ∑' n
, g n z
参数：hu : Summable u；hg : forall n y, HasDerivAt (g n) (g' n y) y；hg' : forall n y
, ‖g' n y‖ <= u n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `differentiable_tsum`：differentiable_tsum (hu : Summable u) (hf : forall 
n x, HasFDerivAt (f n) (f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) : Differe
ntiable 𝕜…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…

--- 原说明 ---
Consider a series of functions `∑' n, f n x`. If all functions in the series are
 differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there 
is no pointwise
convergence then the series is zero everywhere so the result still holds.
-/
theorem differentiable_tsum' (hu : Summable u) (hg : ∀ n y, HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, ‖g' n y‖ ≤ u n) : Differentiable 𝕜 fun z => ∑' n, g n z := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine differentiable_tsum hu hg ?_
  simpa
/-
**fderiv_tsum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_tsum_apply (hu : Summable u) (hf : forall n, Differentiable 𝕜 (f n)
) (hf' : forall n x, ‖fderiv 𝕜 (f n) x‖ <= u n) (hf0 : Summable fun n => f n x₀)
 (x : E) : fderiv 𝕜 (fun y => ∑' n, f n y) x = ∑' n, fderiv 𝕜 (f n) x
参数：hu : Summable u；hf : forall n, Differentiable 𝕜 (f n)；hf' : forall n x, ‖fder
iv 𝕜 (f n) x‖ <= u n；hf0 : Summable fun n => f n x₀；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `hasFDerivAt_tsum`：hasFDerivAt_tsum (hu : Summable u) (hf : forall n x, H
asFDerivAt (f n) (f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) (hf0 : Summable
 fun n…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_tsum_apply (hu : Summable u) (hf : ∀ n, Differentiable 𝕜 (f n))
    (hf' : ∀ n x, ‖fderiv 𝕜 (f n) x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    fderiv 𝕜 (fun y => ∑' n, f n y) x = ∑' n, fderiv 𝕜 (f n) x :=
  (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv
/-
**deriv_tsum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_tsum_apply (hu : Summable u) (hg : forall n, Differentiable 𝕜 (g n))
 (hg' : forall n y, ‖deriv (g n) y‖ <= u n) (hg0 : Summable fun n => g n y₀) (y 
: 𝕜) : deriv (fun z => ∑' n, g n z) y = ∑' n, deriv (g n) y
参数：hu : Summable u；hg : forall n, Differentiable 𝕜 (g n)；hg' : forall n y, ‖deri
v (g n) y‖ <= u n；hg0 : Summable fun n => g n y₀；y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_tsum`：hasDerivAt_tsum (hu : Summable u) (hg : forall n y, Has
DerivAt (g n) (g' n y) y) (hg' : forall n y, ‖g' n y‖ <= u n) (hg0 : Summable fu
n n =…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_tsum_apply (hu : Summable u) (hg : ∀ n, Differentiable 𝕜 (g n))
    (hg' : ∀ n y, ‖deriv (g n) y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    deriv (fun z => ∑' n, g n z) y = ∑' n, deriv (g n) y :=
  (hasDerivAt_tsum hu (fun n y => (hg n y).hasDerivAt) hg' hg0 _).deriv
/-
**fderiv_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_tsum (hu : Summable u) (hf : forall n, Differentiable 𝕜 (f n)) (hf'
 : forall n x, ‖fderiv 𝕜 (f n) x‖ <= u n) (hf0 : Summable fun n => f n x₀) : (fd
eriv 𝕜 fun y => ∑' n, f n y) = fun x => ∑' n, fderiv 𝕜 (f n) x
参数：hu : Summable u；hf : forall n, Differentiable 𝕜 (f n)；hf' : forall n x, ‖fder
iv 𝕜 (f n) x‖ <= u n；hf0 : Summable fun n => f n x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderiv_tsum_apply`：fderiv_tsum_apply (hu : Summable u) (hf : forall n, D
ifferentiable 𝕜 (f n)) (hf' : forall n x, ‖fderiv 𝕜 (f n) x‖ <= u n) (hf0 : Summ
able fu…
-/
theorem fderiv_tsum (hu : Summable u) (hf : ∀ n, Differentiable 𝕜 (f n))
    (hf' : ∀ n x, ‖fderiv 𝕜 (f n) x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) :
    (fderiv 𝕜 fun y => ∑' n, f n y) = fun x => ∑' n, fderiv 𝕜 (f n) x := by
  ext1 x
  exact fderiv_tsum_apply hu hf hf' hf0 x
/-
**deriv_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_tsum (hu : Summable u) (hg : forall n, Differentiable 𝕜 (g n)) (hg' 
: forall n y, ‖deriv (g n) y‖ <= u n) (hg0 : Summable fun n => g n y₀) : (deriv 
fun y => ∑' n, g n y) = fun y => ∑' n, deriv (g n) y
参数：hu : Summable u；hg : forall n, Differentiable 𝕜 (g n)；hg' : forall n y, ‖deri
v (g n) y‖ <= u n；hg0 : Summable fun n => g n y₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_tsum_apply`：deriv_tsum_apply (hu : Summable u) (hg : forall n, Dif
ferentiable 𝕜 (g n)) (hg' : forall n y, ‖deriv (g n) y‖ <= u n) (hg0 : Summable 
fun n …
-/
theorem deriv_tsum (hu : Summable u) (hg : ∀ n, Differentiable 𝕜 (g n))
    (hg' : ∀ n y, ‖deriv (g n) y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) :
    (deriv fun y => ∑' n, g n y) = fun y => ∑' n, deriv (g n) y := by
  ext1 x
  exact deriv_tsum_apply hu hg hg' hg0 x

/-! ### Higher smoothness -/

/-- Consider a series of `C^n` functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
/-
**iteratedFDeriv_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_tsum (hf : forall i, ContDiff 𝕜 N (f i)) (hv : forall k : N
at, (k : Nat∞) <= N -> Summable (v k)) (h'f : forall (k : Nat) (i : α) (x : E), 
(k : Nat∞) <= N -> ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) {k : Nat} (hk : (k : N
at∞) <= N) : (iteratedFDeriv 𝕜 k fun y => ∑' n, f n y) = fun x => ∑' n, iterated
FDeriv 𝕜 k (f n) x
参数：hf : forall i, ContDiff 𝕜 N (f i)；hv : forall k : Nat, (k : Nat∞) <= N -> Sum
mable (v k)；h'f : forall (k : Nat) (i : α) (x : E), (k : Nat∞) <= N -> ‖iterated
FDeriv 𝕜 k (f i) x‖ <= v k i；hk : (k : Nat∞) <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.map_tsum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Ty
pe u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring
 R₂] [inst_2 : AddCo…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
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
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_tsum`：fderiv_tsum (hu : Summable u) (hf : forall n, Differentiabl
e 𝕜 (f n)) (hf' : forall n x, ‖fderiv 𝕜 (f n) x‖ <= u n) (hf0 : Summable fun n =
>…
· 使用定理 `ContDiff.differentiable_iteratedFDeriv`：ContDiff.differentiable_iterated
FDeriv {m : Nat} (hm : m < n) (hf : ContDiff 𝕜 n f) : Differentiable 𝕜 fun x => 
iteratedFDeriv 𝕜 m f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …

--- 原说明 ---
Consider a series of `C^n` functions, with summable uniform bounds on the succes
sive
derivatives. Then the iterated derivative of the sum is the sum of the iterated 
derivative.
-/
theorem iteratedFDeriv_tsum (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) :
    (iteratedFDeriv 𝕜 k fun y => ∑' n, f n y) = fun x => ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  induction k with
  | zero =>
    ext1 x
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
    have A : Summable fun n => iteratedFDeriv 𝕜 k (f n) 0 :=
      .of_norm_bounded (hv k h'k.le) fun n ↦ h'f k n 0 h'k.le
    simp_rw [iteratedFDeriv_succ_eq_comp_left, IH h'k.le]
    rw [fderiv_tsum (hv _ hk) (fun n => (hf n).differentiable_iteratedFDeriv
        (mod_cast h'k)) _ A]
    · ext1 x
      exact (continuousMultilinearCurryLeftEquiv 𝕜
        (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv.map_tsum
    · intro n x
      simpa only [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_map, comp_apply]
        using h'f k.succ n x hk

/-- Consider a series of smooth functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
/-
**iteratedFDeriv_tsum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_tsum_apply (hf : forall i, ContDiff 𝕜 N (f i)) (hv : forall
 k : Nat, (k : Nat∞) <= N -> Summable (v k)) (h'f : forall (k : Nat) (i : α) (x 
: E), (k : Nat∞) <= N -> ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) {k : Nat} (hk : 
(k : Nat∞) <= N) (x : E) : iteratedFDeriv 𝕜 k (fun y => ∑' n, f n y) x = ∑' n, i
teratedFDeriv 𝕜 k (f n) x
参数：hf : forall i, ContDiff 𝕜 N (f i)；hv : forall k : Nat, (k : Nat∞) <= N -> Sum
mable (v k)；h'f : forall (k : Nat) (i : α) (x : E), (k : Nat∞) <= N -> ‖iterated
FDeriv 𝕜 k (f i) x‖ <= v k i；hk : (k : Nat∞) <= N；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDeriv_tsum`：iteratedFDeriv_tsum (hf : forall i, ContDiff 𝕜 N (f
 i)) (hv : forall k : Nat, (k : Nat∞) <= N -> Summable (v k)) (h'f : forall (k :
 Nat) (i …

--- 原说明 ---
Consider a series of smooth functions, with summable uniform bounds on the succe
ssive
derivatives. Then the iterated derivative of the sum is the sum of the iterated 
derivative.
-/
theorem iteratedFDeriv_tsum_apply (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) (x : E) :
    iteratedFDeriv 𝕜 k (fun y => ∑' n, f n y) x = ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  rw [iteratedFDeriv_tsum hf hv h'f hk]

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N`. Then the series is also `C^N`. -/
/-
**contDiff_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_tsum (hf : forall i, ContDiff 𝕜 N (f i)) (hv : forall k : Nat, (k
 : Nat∞) <= N -> Summable (v k)) (h'f : forall (k : Nat) (i : α) (x : E), k <= N
 -> ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) : ContDiff 𝕜 N fun x => ∑' i, f i x
参数：hf : forall i, ContDiff 𝕜 N (f i)；hv : forall k : Nat, (k : Nat∞) <= N -> Sum
mable (v k)；h'f : forall (k : Nat) (i : α) (x : E), k <= N -> ‖iteratedFDeriv 𝕜 
k (f i) x‖ <= v k i。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_iff_continuous_differentiable`：contDiff_iff_continuous_differen
tiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, m <= n -> Continuous fun x
 => iteratedFDeriv 𝕜 m f x) …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `iteratedFDeriv_tsum`：iteratedFDeriv_tsum (hf : forall i, ContDiff 𝕜 N (f
 i)) (hv : forall k : Nat, (k : Nat∞) <= N -> Summable (v k)) (h'f : forall (k :
 Nat) (i …
· 使用定理 `continuous_tsum`：continuous_tsum [TopologicalSpace β] {f : α -> β -> F} 
(hf : forall i, Continuous (f i)) (hu : Summable u) (hfu : forall n x, ‖f n x‖ <
= u n…
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
· 使用定理 `ContDiff.continuous_iteratedFDeriv`：ContDiff.continuous_iteratedFDeriv {
m : Nat} (hm : m <= n) (hf : ContDiff 𝕜 n f) : Continuous fun x => iteratedFDeri
v 𝕜 m f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiff.differentiable_iteratedFDeriv`：ContDiff.differentiable_iterated
FDeriv {m : Nat} (hm : m < n) (hf : ContDiff 𝕜 n f) : Differentiable 𝕜 fun x => 
iteratedFDeriv 𝕜 m f x
· 使用定理 `differentiable_tsum`：differentiable_tsum (hu : Summable u) (hf : forall 
n x, HasFDerivAt (f n) (f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n) : Differe
ntiable 𝕜…
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `fderiv_iteratedFDeriv`：fderiv_iteratedFDeriv {n : Nat} : fderiv 𝕜 (itera
tedFDeriv 𝕜 n f) = continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) =>
 E) F ∘ ite…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …

--- 原说明 ---
Consider a series of functions `∑' i, f i x`. Assume that each individual functi
on `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th 
derivative
for each `k ≤ N`. Then the series is also `C^N`.
-/
theorem contDiff_tsum (hf : ∀ i, ContDiff 𝕜 N (f i)) (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), k ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [iteratedFDeriv_tsum hf hv h'f hm]
    refine continuous_tsum ?_ (hv m hm) ?_
    · intro i
      exact ContDiff.continuous_iteratedFDeriv (mod_cast hm) (hf i)
    · intro n x
      exact h'f _ _ _ hm
  · intro m hm
    have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using Order.add_one_le_of_lt hm
    rw [iteratedFDeriv_tsum hf hv h'f hm.le]
    have A n x : HasFDerivAt (iteratedFDeriv 𝕜 m (f n)) (fderiv 𝕜 (iteratedFDeriv 𝕜 m (f n)) x) x :=
      (ContDiff.differentiable_iteratedFDeriv (mod_cast hm)
        (hf n)).differentiableAt.hasFDerivAt
    refine differentiable_tsum (hv _ h'm) A fun n x => ?_
    rw [fderiv_iteratedFDeriv, comp_apply, LinearIsometryEquiv.norm_map]
    exact h'f _ _ _ h'm

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N` (except maybe for finitely many `i`s). Then the series is also `C^N`. -/
/-
**contDiff_tsum_of_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_tsum_of_eventually (hf : forall i, ContDiff 𝕜 N (f i)) (hv : fora
ll k : Nat, k <= N -> Summable (v k)) (h'f : forall k : Nat, k <= N -> forallᶠ i
 in (Filter.cofinite : Filter α), forall x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= 
v k i) : ContDiff 𝕜 N fun x => ∑' i, f i x
参数：hf : forall i, ContDiff 𝕜 N (f i)；hv : forall k : Nat, k <= N -> Summable (v 
k)；h'f : forall k : Nat, k <= N -> forallᶠ i in (Filter.cofinite : Filter α), fo
rall x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_forall_nat_le`：contDiff_iff_forall_nat_le {n : Nat∞} : Cont
Diff 𝕜 n f ↔ forall m : Nat, ↑m <= n -> ContDiff 𝕜 m f
· 使用定理 `Filter.eventually_cofinite`：eventually_cofinite {p : α -> Prop} : (foral
lᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_subtype_compl`：∀ {α : Type u_1} {β : Type u_2} [in
st : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   [Complete
Space α] [T2Space α] {f :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.sum`：ContDiff.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} 
(h : forall i in s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i in 
s,…
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `contDiff_tsum`：contDiff_tsum (hf : forall i, ContDiff 𝕜 N (f i)) (hv : f
orall k : Nat, (k : Nat∞) <= N -> Summable (v k)) (h'f : forall (k : Nat) (i : α
) (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a series of functions `∑' i, f i x`. Assume that each individual functi
on `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th 
derivative
for each `k ≤ N` (except maybe for finitely many `i`s). Then the series is also 
`C^N`.
-/
theorem contDiff_tsum_of_eventually (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, k ≤ N → Summable (v k))
    (h'f : ∀ k : ℕ, k ≤ N →
      ∀ᶠ i in (Filter.cofinite : Filter α), ∀ x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  refine contDiff_iff_forall_nat_le.2 fun m hm => ?_
  let t : Set α :=
    { i : α | ¬∀ k : ℕ, k ∈ Finset.range (m + 1) → ∀ x, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i }
  have ht : Set.Finite t :=
    haveI A :
      ∀ᶠ i in (Filter.cofinite : Filter α),
        ∀ k : ℕ, k ∈ Finset.range (m + 1) → ∀ x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i := by
      rw [eventually_all_finset]
      intro i hi
      apply h'f
      simp only [Finset.mem_range_succ_iff] at hi
      exact (WithTop.coe_le_coe.2 hi).trans hm
    eventually_cofinite.2 A
  let T : Finset α := ht.toFinset
  have : (fun x => ∑' i, f i x) = (fun x => ∑ i ∈ T, f i x) +
      fun x => ∑' i : { i // i ∉ T }, f i x := by
    ext1 x
    refine (Summable.sum_add_tsum_subtype_compl ?_ T).symm
    refine .of_norm_bounded_eventually (hv 0 zero_le) ?_
    filter_upwards [h'f 0 zero_le] with i hi
    simpa only [norm_iteratedFDeriv_zero] using hi x
  rw [this]
  apply (ContDiff.sum fun i _ => (hf i).of_le (mod_cast hm)).add
  have h'u : ∀ k : ℕ, (k : ℕ∞) ≤ m → Summable (v k ∘ ((↑) : { i // i ∉ T } → α)) := fun k hk =>
    (hv k (hk.trans hm)).subtype _
  refine contDiff_tsum (fun i => (hf i).of_le (mod_cast hm)) h'u ?_
  rintro k ⟨i, hi⟩ x hk
  simp only [t, T, Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_range, not_forall, not_le,
    exists_prop, not_exists, not_and, not_lt] at hi
  exact hi k (Nat.lt_succ_iff.2 (WithTop.coe_le_coe.1 hk)) x
