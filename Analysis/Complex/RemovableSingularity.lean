/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Removable singularity theorem

In this file we prove Riemann's removable singularity theorem: if `f : ℂ → E` is complex
differentiable in a punctured neighborhood of a point `c` and is bounded in a punctured neighborhood
of `c` (or, more generally, $f(z) - f(c)=o((z-c)^{-1})$), then it has a limit at `c` and the
function `update f c (limUnder (𝓝[≠] c) f)` is complex differentiable in a neighborhood of `c`.
-/

public section


open TopologicalSpace Metric Set Filter Asymptotics Function

open scoped Topology Filter NNReal Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace Complex

/-- **Removable singularity** theorem, weak version. If `f : ℂ → E` is differentiable in a punctured
neighborhood of a point and is continuous at this point, then it is analytic at this point. -/
/-
**Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt** 是 Mat
hlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt {f : Comple
x -> E} {c : Complex} (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z) 
(hc : ContinuousAt f c) : AnalyticAt Complex f c
参数：hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z；hc : ContinuousAt f c
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesOnBall.analyticAt`：HasFPowerSeriesOnBall.analyticAt (hf :
 HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x
· 使用定理 `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`：hasFPower
SeriesOnBall_of_differentiable_off_countable {R : Real>=0} {c : Complex} {f : Co
mplex -> E} {s : Set Complex} (hs : s.Countable) (h…
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
**Removable singularity** theorem, weak version. If `f : ℂ → E` is differentiabl
e in a punctured
neighborhood of a point and is continuous at this point, then it is analytic at 
this point.
-/
theorem analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) : AnalyticAt ℂ f c := by
  rcases (nhdsWithin_hasBasis nhds_basis_closedBall _).mem_iff.1 hd with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  replace hc : ContinuousOn f (closedBall c R) := by
    refine fun z hz => ContinuousAt.continuousWithinAt ?_
    rcases eq_or_ne z c with (rfl | hne)
    exacts [hc, (hRs ⟨hz, hne⟩).continuousAt]
  exact (hasFPowerSeriesOnBall_of_differentiable_off_countable (countable_singleton c) hc
    (fun z hz => hRs (sdiff_subset_sdiff_left ball_subset_closedBall hz)) hR0).analyticAt
/-
**Complex.differentiableOn_compl_singleton_and_continuousAt_iff** 是 Mathlib 中的一个
定理，位于命名空间 `Complex`。
形式化陈述：differentiableOn_compl_singleton_and_continuousAt_iff {f : Complex -> E} {
s : Set Complex} {c : Complex} (hs : s in 𝓝 c) : DifferentiableOn Complex f (s \
 {c}) ∧ ContinuousAt f c ↔ DifferentiableOn Complex f s
参数：hs : s in 𝓝 c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用定理 `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`：
analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt {f : Complex -> E
} {c : Complex} (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhds_iff`：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s
 in 𝓝 x') ↔ s in 𝓝 x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ne.nhdsWithin_sdiff_singleton`：Ne.nhdsWithin_sdiff_singleton [T1Space X]
 {x y : X} (h : x != y) (s : Set X) : 𝓝[s \ {y}] x = 𝓝[s] x
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 33 条，此处仅展示前 30 条）
-/
theorem differentiableOn_compl_singleton_and_continuousAt_iff {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hs : s ∈ 𝓝 c) :
    DifferentiableOn ℂ f (s \ {c}) ∧ ContinuousAt f c ↔ DifferentiableOn ℂ f s := by
  refine ⟨?_, fun hd => ⟨hd.mono sdiff_subset, (hd.differentiableAt hs).continuousAt⟩⟩
  rintro ⟨hd, hc⟩ x hx
  rcases eq_or_ne x c with (rfl | hne)
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc).differentiableAt.differentiableWithinAt
    refine eventually_nhdsWithin_iff.2 ((eventually_mem_nhds_iff.2 hs).mono fun z hz hzx => ?_)
    exact hd.differentiableAt (inter_mem hz (isOpen_ne.mem_nhds hzx))
  · simpa only [DifferentiableWithinAt, HasFDerivWithinAt, hne.nhdsWithin_sdiff_singleton] using
      hd x ⟨hx, hne⟩
/-
**Complex.differentiableOn_dslope** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableOn_dslope {f : Complex -> E} {s : Set Complex} {c : Complex}
 (hc : s in 𝓝 c) : DifferentiableOn Complex (dslope f c) s ↔ DifferentiableOn Co
mplex f s
参数：hc : s in 𝓝 c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.of_dslope`：DifferentiableOn.of_dslope (h : Differentiab
leOn 𝕜 (dslope f a) s) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.differentiableOn_compl_singleton_and_continuousAt_iff`：different
iableOn_compl_singleton_and_continuousAt_iff {f : Complex -> E} {s : Set Complex
} {c : Complex} (hs : s in 𝓝 c) : DifferentiableOn …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableOn_dslope_of_notMem`：differentiableOn_dslope_of_notMem (h 
: a ∉ s) : DifferentiableOn 𝕜 (dslope f a) s ↔ DifferentiableOn 𝕜 f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `continuousAt_dslope_same`：continuousAt_dslope_same : ContinuousAt (dslop
e f a) a ↔ DifferentiableAt 𝕜 f a
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
-/
theorem differentiableOn_dslope {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c) :
    DifferentiableOn ℂ (dslope f c) s ↔ DifferentiableOn ℂ f s :=
  ⟨fun h => h.of_dslope, fun h =>
    (differentiableOn_compl_singleton_and_continuousAt_iff hc).mp <|
      ⟨Iff.mpr (differentiableOn_dslope_of_notMem fun h => h.2 rfl) (h.mono sdiff_subset),
        continuousAt_dslope_same.2 <| h.differentiableAt hc⟩⟩

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable on `s \ {c}`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to be
equal to `limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
/-
**Complex.differentiableOn_update_limUnder_of_isLittleO** 是 Mathlib 中的一个定理，位于命名空
间 `Complex`。
形式化陈述：differentiableOn_update_limUnder_of_isLittleO {f : Complex -> E} {s : Set 
Complex} {c : Complex} (hc : s in 𝓝 c) (hd : DifferentiableOn Complex f (s \ {c}
)) (ho : (fun z => f z - f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹) : DifferentiableOn
 Complex (update f c (limUnder (𝓝[!=] c) f)) s
参数：hc : s in 𝓝 c；hd : DifferentiableOn Complex f (s \ {c})；ho : (fun z => f z - 
f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.smul`：DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c 
s) (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (c • f) s
· 使用定理 `DifferentiableOn.sub_const`：DifferentiableOn.sub_const (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_compl_self`：continuousWithinAt_compl_self : Continuou
sWithinAt f {x}ᶜ x ↔ ContinuousAt f x
· 使用定理 `Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero`：∀ {α : Type u_1} {E' :
 Type u_6} {𝕜 : Type u_15} [inst : SeminormedAddCommGroup E'] [inst_1 : NormedDi
visionRing 𝕜]   [inst_2 : _root_.Modul…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousAt_update_same`：continuousAt_update_same [DecidableEq α] {y : 
β} : ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[!=] x) (𝓝 y)
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
**Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a functi
on `f : ℂ → E`
is complex differentiable on `s \ {c}`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f
` redefined to be
equal to `limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `s`.
-/
theorem differentiableOn_update_limUnder_of_isLittleO {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c}))
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s := by
  set F : ℂ → E := fun z => (z - c) • f z
  suffices DifferentiableOn ℂ F (s \ {c}) ∧ ContinuousAt F c by
    rw [differentiableOn_compl_singleton_and_continuousAt_iff hc, ← differentiableOn_dslope hc,
      dslope_sub_smul] at this
    have hc : Tendsto f (𝓝[≠] c) (𝓝 (deriv F c)) :=
      continuousAt_update_same.mp (this.continuousOn.continuousAt hc)
    rwa [hc.limUnder_eq]
  refine ⟨(differentiableOn_id.sub_const _).smul hd, ?_⟩
  rw [← continuousWithinAt_compl_self]
  have H := ho.tendsto_inv_smul_nhds_zero
  have H' : Tendsto (fun z => (z - c) • f c) (𝓝[≠] c) (𝓝 (F c)) :=
    (continuousWithinAt_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds
  simpa [← smul_add, ContinuousWithinAt] using H.add H'

/-- **Removable singularity** theorem: if `s` is a punctured neighborhood of `c : ℂ`, a function
`f : ℂ → E` is complex differentiable on `s`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to
be equal to `limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `{c} ∪ s`. -/
/-
**Complex.differentiableOn_update_limUnder_insert_of_isLittleO** 是 Mathlib 中的一个定
理，位于命名空间 `Complex`。
形式化陈述：differentiableOn_update_limUnder_insert_of_isLittleO {f : Complex -> E} {s
 : Set Complex} {c : Complex} (hc : s in 𝓝[!=] c) (hd : DifferentiableOn Complex
 f s) (ho : (fun z => f z - f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹) : Differentiabl
eOn Complex (update f c (limUnder (𝓝[!=] c) f)) (insert c s)
参数：hc : s in 𝓝[!=] c；hd : DifferentiableOn Complex f s；ho : (fun z => f z - f c)
 =o[𝓝[!=] c] fun z => (z - c)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiableOn_update_limUnder_of_isLittleO`：differentiableOn_
update_limUnder_of_isLittleO {f : Complex -> E} {s : Set Complex} {c : Complex} 
(hc : s in 𝓝 c) (hd : DifferentiableOn Comp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `insert_mem_nhds_iff`：insert_mem_nhds_iff {a : α} {s : Set α} : insert a 
s in 𝓝 a ↔ s in 𝓝[!=] a
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Removable singularity** theorem: if `s` is a punctured neighborhood of `c : ℂ`
, a function
`f : ℂ → E` is complex differentiable on `s`, and $f(z) - f(c)=o((z-c)^{-1})$, t
hen `f` redefined to
be equal to `limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `{c} ∪ s`.
-/
theorem differentiableOn_update_limUnder_insert_of_isLittleO {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hc : s ∈ 𝓝[≠] c) (hd : DifferentiableOn ℂ f s)
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) (insert c s) :=
  differentiableOn_update_limUnder_of_isLittleO (insert_mem_nhds_iff.2 hc)
    (hd.mono fun _ hz => hz.1.resolve_left hz.2) ho

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable and is bounded on `s \ {c}`, then `f` redefined to be equal to
`limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
/-
**Complex.differentiableOn_update_limUnder_of_bddAbove** 是 Mathlib 中的一个定理，位于命名空间
 `Complex`。
形式化陈述：differentiableOn_update_limUnder_of_bddAbove {f : Complex -> E} {s : Set C
omplex} {c : Complex} (hc : s in 𝓝 c) (hd : DifferentiableOn Complex f (s \ {c})
) (hb : BddAbove (norm ∘ f '' (s \ {c}))) : DifferentiableOn Complex (update f c
 (limUnder (𝓝[!=] c) f)) s
参数：hc : s in 𝓝 c；hd : DifferentiableOn Complex f (s \ {c})；hb : BddAbove (norm ∘
 f '' (s \ {c}))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiableOn_update_limUnder_of_isLittleO`：differentiableOn_
update_limUnder_of_isLittleO {f : Complex -> E} {s : Set Complex} {c : Complex} 
(hc : s in 𝓝 c) (hd : DifferentiableOn Comp…
· 使用定理 `Filter.IsBoundedUnder.isLittleO_sub_self_inv`：Filter.IsBoundedUnder.isLi
ttleO_sub_self_inv {𝕜 E : Type*} [NormedField 𝕜] [Norm E] {a : 𝕜} {f : 𝕜 -> E} (
h : IsBoundedUnder (· <= ·) (𝓝[!=]…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `norm_sub_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ - a₂‖ ≤ r₁ + r₂
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
**Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a functi
on `f : ℂ → E`
is complex differentiable and is bounded on `s \ {c}`, then `f` redefined to be 
equal to
`limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `s`.
-/
theorem differentiableOn_update_limUnder_of_bddAbove {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s :=
  differentiableOn_update_limUnder_of_isLittleO hc hd <| IsBoundedUnder.isLittleO_sub_self_inv <|
    let ⟨C, hC⟩ := hb
    ⟨C + ‖f c‖, eventually_map.2 <| mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨s, hc, fun _ hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rfl⟩⟩

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable on a
punctured neighborhood of `c` and $f(z) - f(c)=o((z-c)^{-1})$, then `f` has a limit at `c`. -/
/-
**Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO** 是 
Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO {f : Com
plex -> E} {c : Complex} (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f 
z) (ho : (fun z => f z - f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹) : Tendsto f (𝓝[!=]
 c) (𝓝 <| limUnder (𝓝[!=] c) f)
参数：hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z；ho : (fun z => f z - 
f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Complex.differentiableOn_update_limUnder_of_isLittleO`：differentiableOn_
update_limUnder_of_isLittleO {f : Complex -> E} {s : Set Complex} {c : Complex} 
(hc : s in 𝓝 c) (hd : DifferentiableOn Comp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousAt_update_same`：continuousAt_update_same [DecidableEq α] {y : 
β} : ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[!=] x) (𝓝 y)
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x

--- 原说明 ---
**Removable singularity** theorem: if a function `f : ℂ → E` is complex differen
tiable on a
punctured neighborhood of `c` and $f(z) - f(c)=o((z-c)^{-1})$, then `f` has a li
mit at `c`.
-/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f) := by
  rw [eventually_nhdsWithin_iff] at hd
  have : DifferentiableOn ℂ f ({z | z ≠ c → DifferentiableAt ℂ f z} \ {c}) := fun z hz =>
    (hz.1 hz.2).differentiableWithinAt
  have H := differentiableOn_update_limUnder_of_isLittleO hd this ho
  exact continuousAt_update_same.1 (H.differentiableAt hd).continuousAt

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable and
bounded on a punctured neighborhood of `c`, then `f` has a limit at `c`. -/
/-
**Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under*
* 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under {f :
 Complex -> E} {c : Complex} (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Comple
x f z) (hb : IsBoundedUnder (· <= ·) (𝓝[!=] c) fun z => ‖f z - f c‖) : Tendsto f
 (𝓝[!=] c) (𝓝 <| limUnder (𝓝[!=] c) f)
参数：hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z；hb : IsBoundedUnder (
· <= ·) (𝓝[!=] c) fun z => ‖f z - f c‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittle
O`：tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO {f : Comple
x -> E} {c : Complex} (hd : forallᶠ z in 𝓝[!=] c, Differentiabl…
· 使用定理 `Filter.IsBoundedUnder.isLittleO_sub_self_inv`：Filter.IsBoundedUnder.isLi
ttleO_sub_self_inv {𝕜 E : Type*} [NormedField 𝕜] [Norm E] {a : 𝕜} {f : 𝕜 -> E} (
h : IsBoundedUnder (· <= ·) (𝓝[!=]…

--- 原说明 ---
**Removable singularity** theorem: if a function `f : ℂ → E` is complex differen
tiable and
bounded on a punctured neighborhood of `c`, then `f` has a limit at `c`.
-/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f) :=
  tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd hb.isLittleO_sub_self_inv

/-- The Cauchy formula for the derivative of a holomorphic function. -/
/-
**Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable** 是
 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable {U : Se
t Complex} (hU : IsOpen U) {c w₀ : Complex} {R : Real} {f : Complex -> E} (hc : 
closedBall c R subseteq U) (hf : DifferentiableOn Complex f U) (hw₀ : w₀ in ball
 c R) : ((2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • f z) = der
iv f w₀
参数：hU : IsOpen U；hc : closedBall c R subseteq U；hf : DifferentiableOn Complex f 
U；hw₀ : w₀ in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.differentiableOn_dslope`：differentiableOn_dslope {f : Complex ->
 E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c) : DifferentiableOn Complex (
dslope f c) s ↔ Diffe…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`：∀ {E : Type 
u} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {R
 : ℝ} {c w : ℂ} {f : ℂ → E},   DiffContOnCl ℂ f …
· 使用定理 `DifferentiableOn.diffContOnCl_ball`：DifferentiableOn.diffContOnCl_ball {
U : Set E} {c : E} {R : Real} (hf : DifferentiableOn 𝕜 f U) (hc : closedBall c R
 subseteq U) : DiffContO…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dslope_same`：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.pow`：Continuous.pow {f : X -> M} (h : Continuous f) (n : Nat)
 : Continuous (f ^ n)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `Metric.sphere_disjoint_ball`：sphere_disjoint_ball : Disjoint (sphere x ε
) (ball x ε)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
The Cauchy formula for the derivative of a holomorphic function.
-/
theorem two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable {U : Set ℂ}
    (hU : IsOpen U) {c w₀ : ℂ} {R : ℝ} {f : ℂ → E} (hc : closedBall c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hw₀ : w₀ ∈ ball c R) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • f z) = deriv f w₀ := by
  -- We apply the removable singularity theorem and the Cauchy formula to `dslope f w₀`
  have hf' : DifferentiableOn ℂ (dslope f w₀) U :=
    (differentiableOn_dslope (hU.mem_nhds ((ball_subset_closedBall.trans hc) hw₀))).mpr hf
  have h0 := (hf'.diffContOnCl_ball hc).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw₀
  rw [← dslope_same, ← h0]
  congr 1
  trans ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • (f z - f w₀)
  · have h1 : ContinuousOn (fun z : ℂ => ((z - w₀) ^ 2)⁻¹) (sphere c R) := by
      refine ((continuous_id'.sub continuous_const).pow 2).continuousOn.inv₀ fun w hw h => ?_
      exact sphere_disjoint_ball.ne_of_mem hw hw₀ (sub_eq_zero.mp (sq_eq_zero_iff.mp h))
    have h2 : CircleIntegrable (fun z : ℂ => ((z - w₀) ^ 2)⁻¹ • f z) c R := by
      refine ContinuousOn.circleIntegrable (pos_of_mem_ball hw₀).le ?_
      exact h1.smul (hf.continuousOn.mono (sphere_subset_closedBall.trans hc))
    have h3 : CircleIntegrable (fun z : ℂ => ((z - w₀) ^ 2)⁻¹ • f w₀) c R :=
      ContinuousOn.circleIntegrable (pos_of_mem_ball hw₀).le (h1.smul continuousOn_const)
    have h4 : (∮ z : ℂ in C(c, R), ((z - w₀) ^ 2)⁻¹) = 0 := by
      simpa using! circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) c w₀ R
    simp only [smul_sub, circleIntegral.integral_sub h2 h3, h4, circleIntegral.integral_smul_const,
      zero_smul, sub_zero]
  · refine circleIntegral.integral_congr (pos_of_mem_ball hw₀).le fun z hz => ?_
    simp only [dslope_of_ne, Metric.sphere_disjoint_ball.ne_of_mem hz hw₀, slope, ← smul_assoc, sq,
      mul_inv, Ne, not_false_iff, vsub_eq_sub, smul_eq_mul]

end Complex

