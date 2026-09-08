/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Convex.PartitionOfUnity

/-!
# Lemmas about (e)metric spaces that need partition of unity

The main lemma in this file (see `Metric.exists_continuous_real_forall_closedBall_subset`) says the
following. Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of closed sets,
let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`Metric.closedBall x (δ x) ⊆ U i`. We also formulate versions of this lemma for extended metric
spaces and for different codomains (`ℝ`, `ℝ≥0`, and `ℝ≥0∞`).

We also prove a few auxiliary lemmas to be used later in a proof of the smooth version of this
lemma.

## Tags

metric space, partition of unity, locally finite
-/

public section

open Topology ENNReal NNReal Filter Set Function TopologicalSpace Metric

variable {ι X : Type*}

namespace Metric

variable [EMetricSpace X] {K : ι → Set X} {U : ι → Set X}

/-- Let `K : ι → Set X` be a locally finite family of closed sets in an emetric space. Let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then for any point
`x : X`, for sufficiently small `r : ℝ≥0∞` and for `y` sufficiently close to `x`, for all `i`, if
`y ∈ K i`, then `Metric.closedEBall y r ⊆ U i`. -/
/-
**Metric.eventually_nhds_zero_forall_closedEBall_subset** 是 Mathlib 中的一个定理，位于命名空
间 `Metric`。
形式化陈述：eventually_nhds_zero_forall_closedEBall_subset (hK : forall i, IsClosed (K
 i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i) (hfin : Lo
callyFinite K) (x : X) : forallᶠ p : Real>=0∞ × X in 𝓝 0 ×ˢ 𝓝 x, forall i, p.2 i
n K i -> closedEBall p.2 p.1 subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedEBall`：nhds_basis_closedEBall : (𝓝 x).HasBasis (
fun ε : Real>=0∞ => 0 < ε) (closedEBall x)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Metric.closedEBall_mem_nhds`：closedEBall_mem_nhds (x : α) {ε : Real>=0∞}
 (ε0 : 0 < ε) : closedEBall x ε in 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K : ι → Set X` be a locally finite family of closed sets in an emetric spac
e. Let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then
 for any point
`x : X`, for sufficiently small `r : ℝ≥0∞` and for `y` sufficiently close to `x`
, for all `i`, if
`y ∈ K i`, then `Metric.closedEBall y r ⊆ U i`.
-/
theorem eventually_nhds_zero_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ˢ 𝓝 x, ∀ i, p.2 ∈ K i → closedEBall p.2 p.1 ⊆ U i := by
  suffices ∀ i, x ∈ K i → ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ˢ 𝓝 x, closedEBall p.2 p.1 ⊆ U i by
    apply mp_mem ((eventually_all_finite (hfin.point_finite x)).2 this)
      (mp_mem (@tendsto_snd ℝ≥0∞ _ (𝓝 0) _ _ (hfin.iInter_compl_mem_nhds hK x)) _)
    apply univ_mem'
    rintro ⟨r, y⟩ hxy hyU i hi
    simp only [mem_iInter, mem_compl_iff, not_imp_not, mem_preimage] at hxy
    exact hyU _ (hxy _ hi)
  intro i hi
  rcases nhds_basis_closedEBall.mem_iff.1 ((hU i).mem_nhds <| hKU i hi) with ⟨R, hR₀, hR⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hR₀ with ⟨r, hr₀, hrR⟩
  filter_upwards [prod_mem_prod (eventually_lt_nhds hr₀)
      (closedEBall_mem_nhds x (tsub_pos_iff_lt.2 hrR))] with p hp z hz
  apply hR
  calc
    edist z x ≤ edist z p.2 + edist p.2 x := edist_triangle _ _ _
    _ ≤ p.1 + (R - p.1) := add_le_add hz <| le_trans hp.2 <| tsub_le_tsub_left hp.1.out.le _
    _ = R := add_tsub_cancel_of_le (lt_trans (by exact hp.1) hrR).le

/-- Auxiliary lemma for `exists_continuous_real_forall_closedEBall_subset`
and its smooth counterpart. -/
/-
**Metric.exists_forall_closedEBall_subset_aux** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `exists_continuous_real_forall_closedEBall_subset`
and its smooth counterpart.
-/
theorem exists_forall_closedEBall_subset_aux₁ (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∃ r : ℝ, ∀ᶠ y in 𝓝 x,
      r ∈ Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (_ : y ∈ K i), { r | closedEBall y r ⊆ U i } := by
  have := (ENNReal.continuous_ofReal.tendsto' 0 0 ENNReal.ofReal_zero).eventually
    (eventually_nhds_zero_forall_closedEBall_subset hK hU hKU hfin x).curry
  rcases this.exists_gt with ⟨r, hr0, hr⟩
  refine ⟨r, hr.mono fun y hy => ⟨hr0, ?_⟩⟩
  rwa [mem_preimage, mem_iInter₂]

/-- Auxiliary lemma for `exists_continuous_real_forall_closedEBall_subset`
and its smooth counterpart. -/
/-
**Metric.exists_forall_closedEBall_subset_aux** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `exists_continuous_real_forall_closedEBall_subset`
and its smooth counterpart.
-/
theorem exists_forall_closedEBall_subset_aux₂ (y : X) :
    Convex ℝ
      (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (_ : y ∈ K i), { r | closedEBall y r ⊆ U i }) :=
  (convex_Ioi _).inter <| OrdConnected.convex <| OrdConnected.preimage_ennreal_ofReal <|
    ordConnected_iInter fun i => ordConnected_iInter fun (_ : y ∈ K i) =>
      ordConnected_setOfPred_closedEBall_subset y (U i)

/-- Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite family of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`,
we have `Metric.closedEBall x (ENNReal.ofReal (δ x)) ⊆ U i`. -/
/-
**Metric.exists_continuous_real_forall_closedEBall_subset** 是 Mathlib 中的一个定理，位于命
名空间 `Metric`。
形式化陈述：exists_continuous_real_forall_closedEBall_subset (hK : forall i, IsClosed 
(K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i) (hfin : 
LocallyFinite K) : exists δ : C(X, Real), (forall x, 0 < δ x) ∧ forall (i), fora
ll x in K i, closedEBall x (ENNReal.ofReal <| δ x) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_continuous_forall_mem_convex_of_local_const`：exists_continuous_fo
rall_mem_convex_of_local_const (ht : forall x, Convex Real (t x)) (H : forall x 
: X, exists c : E, forallᶠ y in 𝓝 x, c i…
· 使用定理 `NormalSpace.of_paracompactSpace_r1Space`：∀ {X : Type v} [inst : Topologi
calSpace X] [R1Space X] [ParacompactSpace X], NormalSpace X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Metric.instParacompactSpace`：∀ {α : Type u_1} [inst : PseudoEMetricSpace
 α], ParacompactSpace α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Metric.exists_forall_closedEBall_subset_aux₂`：exists_forall_closedEBall_
subset_aux₂ (y : X) : Convex Real (Ioi (0 : Real) inter ENNReal.ofReal ⁻¹' ⋂ (i)
 (_ : y in K i), { r | closedEBall…
· 使用定理 `Metric.exists_forall_closedEBall_subset_aux₁`：exists_forall_closedEBall_
subset_aux₁ (hK : forall i, IsClosed (K i)) (hU : forall i, IsOpen (U i)) (hKU :
 forall i, K i subseteq U i) (hfin…

--- 原说明 ---
Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite fam
ily of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all
 `i`. Then there
exists a positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x
 ∈ K i`,
we have `Metric.closedEBall x (ENNReal.ofReal (δ x)) ⊆ U i`.
-/
theorem exists_continuous_real_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧
      ∀ (i), ∀ x ∈ K i, closedEBall x (ENNReal.ofReal <| δ x) ⊆ U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_comm ι X] using!
    exists_continuous_forall_mem_convex_of_local_const exists_forall_closedEBall_subset_aux₂
      (exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

/-- Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite family of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`,
we have `Metric.closedEBall x (δ x) ⊆ U i`. -/
/-
**Metric.exists_continuous_nnreal_forall_closedEBall_subset** 是 Mathlib 中的一个定理，位
于命名空间 `Metric`。
形式化陈述：exists_continuous_nnreal_forall_closedEBall_subset (hK : forall i, IsClose
d (K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i) (hfin 
: LocallyFinite K) : exists δ : C(X, Real>=0), (forall x, 0 < δ x) ∧ forall (i),
 forall x in K i, closedEBall x (δ x) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_continuous_real_forall_closedEBall_subset`：exists_continuo
us_real_forall_closedEBall_subset (hK : forall i, IsClosed (K i)) (hU : forall i
, IsOpen (U i)) (hKU : forall i, K i subseteq…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `NNReal.ContinuousMap.canLift`：∀ {X : Type u_1} [inst : TopologicalSpace 
X],   CanLift C(X, ℝ) C(X, NNReal) ContinuousMap.coeNNRealReal.comp fun f => ∀ (
x : X), 0 ≤ f x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite fam
ily of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all
 `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and 
`x ∈ K i`,
we have `Metric.closedEBall x (δ x) ⊆ U i`.
-/
theorem exists_continuous_nnreal_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedEBall x (δ x) ⊆ U i := by
  rcases exists_continuous_real_forall_closedEBall_subset hK hU hKU hfin with ⟨δ, hδ₀, hδ⟩
  lift δ to C(X, ℝ≥0) using fun x => (hδ₀ x).le
  refine ⟨δ, hδ₀, fun i x hi => ?_⟩
  simpa only [← ENNReal.ofReal_coe_nnreal] using! hδ i x hi

/-- Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite family of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0∞)` such that for any `i` and `x ∈ K i`,
we have `Metric.closedEBall x (δ x) ⊆ U i`. -/
/-
**Metric.exists_continuous_ennreal_forall_closedEBall_subset** 是 Mathlib 中的一个定理，
位于命名空间 `Metric`。
形式化陈述：exists_continuous_ennreal_forall_closedEBall_subset (hK : forall i, IsClos
ed (K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i) (hfin
 : LocallyFinite K) : exists δ : C(X, Real>=0∞), (forall x, 0 < δ x) ∧ forall (i
), forall x in K i, closedEBall x (δ x) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_continuous_nnreal_forall_closedEBall_subset`：exists_contin
uous_nnreal_forall_closedEBall_subset (hK : forall i, IsClosed (K i)) (hU : fora
ll i, IsOpen (U i)) (hKU : forall i, K i subset…
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r

--- 原说明 ---
Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite fam
ily of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all
 `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0∞)` such that for any `i` and
 `x ∈ K i`,
we have `Metric.closedEBall x (δ x) ⊆ U i`.
-/
theorem exists_continuous_ennreal_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0∞), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedEBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nnreal_forall_closedEBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨Coe.coe, ENNReal.continuous_coe⟩ δ, fun x => ENNReal.coe_pos.2 (hδ₀ x), hδ⟩

end Metric

namespace EMetric
open Metric

@[deprecated (since := "2026-01-24")]
alias eventually_nhds_zero_forall_closedBall_subset :=
  eventually_nhds_zero_forall_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias exists_forall_closedBall_subset_aux₁ := exists_forall_closedEBall_subset_aux₁

@[deprecated (since := "2026-01-24")]
alias exists_forall_closedBall_subset_aux₂ := exists_forall_closedEBall_subset_aux₂

@[deprecated (since := "2026-01-24")]
alias exists_continuous_real_forall_closedBall_subset :=
  exists_continuous_real_forall_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias exists_continuous_nnreal_forall_closedBall_subset :=
  exists_continuous_nnreal_forall_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias exists_continuous_eNNReal_forall_closedBall_subset :=
  exists_continuous_ennreal_forall_closedEBall_subset

end EMetric

namespace Metric

variable [MetricSpace X] {K : ι → Set X} {U : ι → Set X}

/-- Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of closed sets, let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`, we have
`Metric.closedBall x (δ x) ⊆ U i`. -/
/-
**Metric.exists_continuous_nnreal_forall_closedBall_subset** 是 Mathlib 中的一个定理，位于
命名空间 `Metric`。
形式化陈述：exists_continuous_nnreal_forall_closedBall_subset (hK : forall i, IsClosed
 (K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i) (hfin :
 LocallyFinite K) : exists δ : C(X, Real>=0), (forall x, 0 < δ x) ∧ forall (i), 
forall x in K i, closedBall x (δ x) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_continuous_nnreal_forall_closedEBall_subset`：exists_contin
uous_nnreal_forall_closedEBall_subset (hK : forall i, IsClosed (K i)) (hU : fora
ll i, IsOpen (U i)) (hKU : forall i, K i subset…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedEBall_coe`：Metric.closedEBall_coe {x : α} {ε : Real>=0} : c
losedEBall x ε = closedBall x ε

--- 原说明 ---
Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of clo
sed sets, let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then
 there exists a
positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`
, we have
`Metric.closedBall x (δ x) ⊆ U i`.
-/
theorem exists_continuous_nnreal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i := by
  rcases Metric.exists_continuous_nnreal_forall_closedEBall_subset hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_coe]
  exact hδ i x hx

/-- Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of closed sets, let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`Metric.closedBall x (δ x) ⊆ U i`. -/
/-
**Metric.exists_continuous_real_forall_closedBall_subset** 是 Mathlib 中的一个定理，位于命名
空间 `Metric`。
形式化陈述：exists_continuous_real_forall_closedBall_subset (hK : forall i, IsClosed (
K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i) (hfin : L
ocallyFinite K) : exists δ : C(X, Real), (forall x, 0 < δ x) ∧ forall (i), foral
l x in K i, closedBall x (δ x) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_continuous_nnreal_forall_closedBall_subset`：exists_continu
ous_nnreal_forall_closedBall_subset (hK : forall i, IsClosed (K i)) (hU : forall
 i, IsOpen (U i)) (hKU : forall i, K i subsete…
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)

--- 原说明 ---
Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of clo
sed sets, let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then
 there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, 
we have
`Metric.closedBall x (δ x) ⊆ U i`.
-/
theorem exists_continuous_real_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nnreal_forall_closedBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨Coe.coe, NNReal.continuous_coe⟩ δ, hδ₀, hδ⟩

end Metric

