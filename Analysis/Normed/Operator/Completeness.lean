/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Operators on complete normed spaces

This file contains statements about norms of operators on complete normed spaces, such as a
version of the Banach-Alaoglu theorem (`ContinuousLinearMap.isCompact_image_coe_closedBall`).
-/

@[expose] public section

suppress_compilation

open Bornology Metric Set Real
open Filter hiding map_smul
open scoped NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ E F Fₗ : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F)

namespace ContinuousLinearMap

section Completeness

variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [RingHomIsometric σ₁₂]

/-- Construct a bundled continuous (semi)linear map from a map `f : E → F` and a proof of the fact
that it belongs to the closure of the image of a bounded set `s : Set (E →SL[σ₁₂] F)` under coercion
to function. Coercion to function of the result is definitionally equal to `f`. -/
@[simps! -fullyApplied apply]
/-
**ContinuousLinearMap.ofMemClosureImageCoeBounded** 是 Mathlib 中的一个定义，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：ofMemClosureImageCoeBounded (f : E' -> F) {s : Set (E' ->SL[σ₁₂] F)} (hs :
 IsBounded s) (hf : f in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s)) : E
' ->SL[σ₁₂] F
参数：f : E' -> F；E' ->SL[σ₁₂] F；hs : IsBounded s；hf : f in closure (((↑) : (E' ->S
L[σ₁₂] F) -> E' -> F) '' s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled continuous (semi)linear map from a map `f : E → F` and a pro
of of the fact
that it belongs to the closure of the image of a bounded set `s : Set (E →SL[σ₁₂
] F)` under coercion
to function. Coercion to function of the result is definitionally equal to `f`.
-/
def ofMemClosureImageCoeBounded (f : E' → F) {s : Set (E' →SL[σ₁₂] F)} (hs : IsBounded s)
    (hf : f ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) : E' →SL[σ₁₂] F := by
  -- `f` is a linear map due to `linearMapOfMemClosureRangeCoe`
  refine (linearMapOfMemClosureRangeCoe f ?_).mkContinuousOfExistsBound ?_
  · refine closure_mono (image_subset_iff.2 fun g _ => ?_) hf
    exact ⟨g, rfl⟩
  · -- We need to show that `f` has bounded norm. Choose `C` such that `‖g‖ ≤ C` for all `g ∈ s`.
    rcases isBounded_iff_forall_norm_le.1 hs with ⟨C, hC⟩
    -- Then `‖g x‖ ≤ C * ‖x‖` for all `g ∈ s`, `x : E`, hence `‖f x‖ ≤ C * ‖x‖` for all `x`.
    have : ∀ x, IsClosed { g : E' → F | ‖g x‖ ≤ C * ‖x‖ } := fun x =>
      isClosed_Iic.preimage (@continuous_apply E' (fun _ => F) _ x).norm
    refine ⟨C, fun x => (this x).closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf⟩
    exact g.le_of_opNorm_le (hC _ hg) _

/-- Let `f : E → F` be a map, let `g : α → E →SL[σ₁₂] F` be a family of continuous (semi)linear maps
that takes values in a bounded set and converges to `f` pointwise along a nontrivial filter. Then
`f` is a continuous (semi)linear map. -/
@[simps! -fullyApplied apply]
/-
**ContinuousLinearMap.ofTendstoOfBoundedRange** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：ofTendstoOfBoundedRange {α : Type*} {l : Filter α} [l.NeBot] (f : E' -> F)
 (g : α -> E' ->SL[σ₁₂] F) (hf : Tendsto (fun a x => g a x) l (𝓝 f)) (hg : IsBou
nded (Set.range g)) : E' ->SL[σ₁₂] F
参数：f : E' -> F；g : α -> E' ->SL[σ₁₂] F；hf : Tendsto (fun a x => g a x) l (𝓝 f)；h
g : IsBounded (Set.range g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : E → F` be a map, let `g : α → E →SL[σ₁₂] F` be a family of continuous (
semi)linear maps
that takes values in a bounded set and converges to `f` pointwise along a nontri
vial filter. Then
`f` is a continuous (semi)linear map.
-/
def ofTendstoOfBoundedRange {α : Type*} {l : Filter α} [l.NeBot] (f : E' → F)
    (g : α → E' →SL[σ₁₂] F) (hf : Tendsto (fun a x => g a x) l (𝓝 f))
    (hg : IsBounded (Set.range g)) : E' →SL[σ₁₂] F :=
  ofMemClosureImageCoeBounded f hg <| mem_closure_of_tendsto hf <|
    Eventually.of_forall fun _ => mem_image_of_mem _ <| Set.mem_range_self _

/-- If a Cauchy sequence of continuous linear map converges to a continuous linear map pointwise,
then it converges to the same map in norm. This lemma is used to prove that the space of continuous
linear maps is complete provided that the codomain is a complete space. -/
/-
**ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：tendsto_of_tendsto_pointwise_of_cauchySeq {f : Nat -> E' ->SL[σ₁₂] F} {g :
 E' ->SL[σ₁₂] F} (hg : Tendsto (fun n x => f n x) atTop (𝓝 g)) (hf : CauchySeq f
) : Tendsto f atTop (𝓝 g)
参数：hg : Tendsto (fun n x => f n x) atTop (𝓝 g)；hf : CauchySeq f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_iff_le_tendsto_0`：cauchySeq_iff_le_tendsto_0 {s : Nat -> α} : 
CauchySeq s ↔ exists b : Nat -> Real, (forall n, 0 <= b n) ∧ (forall n m N : Nat
, N <= n -> N <=…
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M

--- 原说明 ---
If a Cauchy sequence of continuous linear map converges to a continuous linear m
ap pointwise,
then it converges to the same map in norm. This lemma is used to prove that the 
space of continuous
linear maps is complete provided that the codomain is a complete space.
-/
theorem tendsto_of_tendsto_pointwise_of_cauchySeq {f : ℕ → E' →SL[σ₁₂] F} {g : E' →SL[σ₁₂] F}
    (hg : Tendsto (fun n x => f n x) atTop (𝓝 g)) (hf : CauchySeq f) : Tendsto f atTop (𝓝 g) := by
  /- Since `f` is a Cauchy sequence, there exists `b → 0` such that `‖f n - f m‖ ≤ b N` for any
    `m, n ≥ N`. -/
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  simp_rw [dist_eq_norm] at hfb
  -- Since `b → 0`, it suffices to show that `‖f n x - g x‖ ≤ b n * ‖x‖` for all `n` and `x`.
  suffices ∀ n x, ‖f n x - g x‖ ≤ b n * ‖x‖ from
    tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_le_bound _ (hb₀ n) (this n)) hb_lim)
  intro n x
  -- Note that `f m x → g x`, hence `‖f n x - f m x‖ → ‖f n x - g x‖` as `m → ∞`
  have : Tendsto (fun m => ‖f n x - f m x‖) atTop (𝓝 ‖f n x - g x‖) :=
    (tendsto_const_nhds.sub <| tendsto_pi_nhds.1 hg _).norm
  -- Thus it suffices to verify `‖f n x - f m x‖ ≤ b n * ‖x‖` for `m ≥ n`.
  refine le_of_tendsto this (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
  -- This inequality follows from `‖f n - f m‖ ≤ b n`.
  exact (f n - f m).le_of_opNorm_le (hfb _ _ _ le_rfl hm) _

/-- Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] F` taking values
in a proper space. Then `s` interpreted as a set in the space of maps `E → F` with topology of
pointwise convergence is precompact: its closure is a compact set. -/
/-
**ContinuousLinearMap.isCompact_closure_image_coe_of_bounded** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousLinearMap`。
形式化陈述：isCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' ->SL[σ
₁₂] F)} (hb : IsBounded s) : IsCompact (closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -
> F) '' s))
参数：E' ->SL[σ₁₂] F；hb : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Bornology.IsBounded.isCompact_closure`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α] [ProperSpace α], Bornology.IsBounded s → IsCompact (closu
re s)
· 使用定理 `LipschitzWith.isBounded_image`：isBounded_image (hf : LipschitzWith K f) 
{s : Set α} (hs : IsBounded s) : IsBounded (f '' s)
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `instR1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), R1Space (X i)],   R1Space ((i : ι) → X i)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `isCompact_pi_infinite`：isCompact_pi_infinite {s : forall i, Set (X i)} :
 (forall i, IsCompact (s i)) -> IsCompact { x : forall i, X i | forall i, x i in
 s i }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] 
F` taking values
in a proper space. Then `s` interpreted as a set in the space of maps `E → F` wi
th topology of
pointwise convergence is precompact: its closure is a compact set.
-/
theorem isCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) : IsCompact (closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :=
  have : ∀ x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (image_subset_iff.2 fun _ hg _ => subset_closure <| mem_image_of_mem _ hg)

/-- Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] F` taking values
in a proper space. If `s` interpreted as a set in the space of maps `E → F` with topology of
pointwise convergence is closed, then it is compact.

TODO: reformulate this in terms of a type synonym with the right topology. -/
/-
**ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E
' ->SL[σ₁₂] F)} (hb : IsBounded s) (hc : IsClosed (((↑) : (E' ->SL[σ₁₂] F) -> E'
 -> F) '' s)) : IsCompact (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s)
参数：E' ->SL[σ₁₂] F；hb : IsBounded s；hc : IsClosed (((↑) : (E' ->SL[σ₁₂] F) -> E' 
-> F) '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isCompact_closure_image_coe_of_bounded`：isCompact_cl
osure_image_coe_of_bounded [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBo
unded s) : IsCompact (closure (((↑) : (E' ->SL[σ…
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] 
F` taking values
in a proper space. If `s` interpreted as a set in the space of maps `E → F` with
 topology of
pointwise convergence is closed, then it is compact.

TODO: reformulate this in terms of a type synonym with the right topology.
-/
theorem isCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :
    IsCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb

/-- If a set `s` of semilinear functions is bounded and is closed in the weak-\* topology, then its
image under coercion to functions `E → F` is a closed set. We don't have a name for `E →SL[σ] F`
with weak-\* topology in `mathlib`, so we use an equivalent condition (see `isClosed_induced_iff'`).

TODO: reformulate this in terms of a type synonym with the right topology. -/
/-
**ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isClosed_image_coe_of_bounded_of_weak_closed {s : Set (E' ->SL[σ₁₂] F)} (h
b : IsBounded s) (hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F) in closure (((↑
) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) -> f in s) : IsClosed (((↑) : (E' ->SL[σ₁
₂] F) -> E' -> F) '' s)
参数：E' ->SL[σ₁₂] F；hb : IsBounded s；hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F
) in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) -> f in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s

--- 原说明 ---
If a set `s` of semilinear functions is bounded and is closed in the weak-\* top
ology, then its
image under coercion to functions `E → F` is a closed set. We don't have a name 
for `E →SL[σ] F`
with weak-\* topology in `mathlib`, so we use an equivalent condition (see `isCl
osed_induced_iff'`).

TODO: reformulate this in terms of a type synonym with the right topology.
-/
theorem isClosed_image_coe_of_bounded_of_weak_closed {s : Set (E' →SL[σ₁₂] F)} (hb : IsBounded s)
    (hc : ∀ f : E' →SL[σ₁₂] F,
      (⇑f : E' → F) ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩

/-- If a set `s` of semilinear functions is bounded and is closed in the weak-\* topology, then its
image under coercion to functions `E → F` is a compact set. We don't have a name for `E →SL[σ] F`
with weak-\* topology in `mathlib`, so we use an equivalent condition (see `isClosed_induced_iff'`).
-/
/-
**ContinuousLinearMap.isCompact_image_coe_of_bounded_of_weak_closed** 是 Mathlib 
中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isCompact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E'
 ->SL[σ₁₂] F)} (hb : IsBounded s) (hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F
) in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) -> f in s) : IsCompact (
((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s)
参数：E' ->SL[σ₁₂] F；hb : IsBounded s；hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F
) in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) -> f in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image`：isCo
mpact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' ->SL[σ₁₂
] F)} (hb : IsBounded s) (hc : IsClosed (((↑) : (E' ->SL…
· 使用定理 `ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed`：isClos
ed_image_coe_of_bounded_of_weak_closed {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBounde
d s) (hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F) i…

--- 原说明 ---
If a set `s` of semilinear functions is bounded and is closed in the weak-\* top
ology, then its
image under coercion to functions `E → F` is a compact set. We don't have a name
 for `E →SL[σ] F`
with weak-\* topology in `mathlib`, so we use an equivalent condition (see `isCl
osed_induced_iff'`).
-/
theorem isCompact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : ∀ f : E' →SL[σ₁₂] F,
      (⇑f : E' → F) ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isCompact_image_coe_of_bounded_of_closed_image hb <|
    isClosed_image_coe_of_bounded_of_weak_closed hb hc

/-- A closed ball is closed in the weak-\* topology. We don't have a name for `E →SL[σ] F` with
weak-\* topology in `mathlib`, so we use an equivalent condition (see `isClosed_induced_iff'`). -/
/-
**ContinuousLinearMap.is_weak_closed_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：is_weak_closed_closedBall (f₀ : E' ->SL[σ₁₂] F) (r : Real) ⦃f : E' ->SL[σ₁
₂] F⦄ (hf : ⇑f in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' closedBall f₀ 
r)) : f in closedBall f₀ r
参数：f₀ : E' ->SL[σ₁₂] F；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `Set.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : 
Set α}, (f '' s).Nonempty → s.Nonempty
· 使用定理 `closure_nonempty_iff`：closure_nonempty_iff : (closure s).Nonempty ↔ s.No
nempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closedBall_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup
 E] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r ↔ ‖b - a‖ ≤ r
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖

--- 原说明 ---
A closed ball is closed in the weak-\* topology. We don't have a name for `E →SL
[σ] F` with
weak-\* topology in `mathlib`, so we use an equivalent condition (see `isClosed_
induced_iff'`).
-/
theorem is_weak_closed_closedBall (f₀ : E' →SL[σ₁₂] F) (r : ℝ) ⦃f : E' →SL[σ₁₂] F⦄
    (hf : ⇑f ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' closedBall f₀ r)) :
    f ∈ closedBall f₀ r := by
  have hr : 0 ≤ r := nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨_, hf⟩).of_image
  refine mem_closedBall_iff_norm.2 (opNorm_le_bound _ hr fun x => ?_)
  have : IsClosed { g : E' → F | ‖g x - f₀ x‖ ≤ r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continuous_const).norm
  refine this.closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf
  exact (g - f₀).le_of_opNorm_le (mem_closedBall_iff_norm.1 hg) _

/-- The set of functions `f : E → F` that represent continuous linear maps `f : E →SL[σ₁₂] F`
at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is closed in the topology of pointwise convergence.
This is one of the key steps in the proof of the **Banach-Alaoglu** theorem. -/
/-
**ContinuousLinearMap.isClosed_image_coe_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：isClosed_image_coe_closedBall (f₀ : E ->SL[σ₁₂] F) (r : Real) : IsClosed (
((↑) : (E ->SL[σ₁₂] F) -> E -> F) '' closedBall f₀ r)
参数：f₀ : E ->SL[σ₁₂] F；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed`：isClos
ed_image_coe_of_bounded_of_weak_closed {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBounde
d s) (hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F) i…
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `ContinuousLinearMap.is_weak_closed_closedBall`：is_weak_closed_closedBall
 (f₀ : E' ->SL[σ₁₂] F) (r : Real) ⦃f : E' ->SL[σ₁₂] F⦄ (hf : ⇑f in closure (((↑)
 : (E' ->SL[σ₁₂] F) -> E' -> F) '' …

--- 原说明 ---
The set of functions `f : E → F` that represent continuous linear maps `f : E →S
L[σ₁₂] F`
at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is closed in the topology of pointwis
e convergence.
This is one of the key steps in the proof of the **Banach-Alaoglu** theorem.
-/
theorem isClosed_image_coe_closedBall (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsClosed (((↑) : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)

/-- **Banach-Alaoglu** theorem. The set of functions `f : E → F` that represent continuous linear
maps `f : E →SL[σ₁₂] F` at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is compact in the topology of
pointwise convergence. Other versions of this theorem can be found in
`Analysis.Normed.Module.WeakDual`. -/
/-
**ContinuousLinearMap.isCompact_image_coe_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：isCompact_image_coe_closedBall [ProperSpace F] (f₀ : E ->SL[σ₁₂] F) (r : R
eal) : IsCompact (((↑) : (E ->SL[σ₁₂] F) -> E -> F) '' closedBall f₀ r)
参数：f₀ : E ->SL[σ₁₂] F；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isCompact_image_coe_of_bounded_of_weak_closed`：isCom
pact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E' ->SL[σ₁₂] 
F)} (hb : IsBounded s) (hc : forall f : E' ->SL[σ₁₂] F,…
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `ContinuousLinearMap.is_weak_closed_closedBall`：is_weak_closed_closedBall
 (f₀ : E' ->SL[σ₁₂] F) (r : Real) ⦃f : E' ->SL[σ₁₂] F⦄ (hf : ⇑f in closure (((↑)
 : (E' ->SL[σ₁₂] F) -> E' -> F) '' …

--- 原说明 ---
**Banach-Alaoglu** theorem. The set of functions `f : E → F` that represent cont
inuous linear
maps `f : E →SL[σ₁₂] F` at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is compact in
 the topology of
pointwise convergence. Other versions of this theorem can be found in
`Analysis.Normed.Module.WeakDual`.
-/
theorem isCompact_image_coe_closedBall [ProperSpace F] (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsCompact (((↑) : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall <|
    is_weak_closed_closedBall f₀ r

end Completeness

end ContinuousLinearMap

