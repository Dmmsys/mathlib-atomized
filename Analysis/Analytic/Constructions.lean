/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Geoffrey Irving, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Various ways to combine analytic functions

We show that the following are analytic:

1. Cartesian products of analytic functions
2. Arithmetic on analytic functions: `mul`, `smul`, `inv`, `div`
3. Finite sums and products: `Finset.sum`, `Finset.prod`
-/

@[expose] public section

noncomputable section

open scoped Topology Ring
open Filter Asymptotics ENNReal NNReal

variable {α : Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
variable {𝕝 : Type*} [NormedDivisionRing 𝕝] [NormedAlgebra 𝕜 𝕝]

/-!
### Constants are analytic
-/

/-
**hasFPowerSeriesOnBall_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOnBall_const {c : F} {e : E} : HasFPowerSeriesOnBall (fun _
 => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.constFormalMultilinearSeries_radius`：constFormal
MultilinearSeries_radius {v : F} : (constFormalMultilinearSeries 𝕜 E v).radius =
 ⊤
· 使用定理 `WithTop.top_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α], 0 < ⊤
· 使用定理 `hasSum_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {f : β → α} (b : β),   (∀ (b' : β), b' ≠ b → f b' 
= 0…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `constFormalMultilinearSeries_apply_of_nonzero`：constFormalMultilinearSer
ies_apply_of_nonzero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedA
ddCommGroup F] [NormedSpace 𝕜 E] [N…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop

--- 原说明 ---
### Constants are analytic
-/
theorem hasFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤ := by
  refine ⟨by simp, WithTop.top_pos, fun _ => hasSum_single 0 fun n hn => ?_⟩
  simp [constFormalMultilinearSeries_apply_of_nonzero hn]
/-
**hasFPowerSeriesAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_const {c : F} {e : E} : HasFPowerSeriesAt (fun _ => c) (
constFormalMultilinearSeries 𝕜 E c) e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFPowerSeriesOnBall_const`：hasFPowerSeriesOnBall_const {c : F} {e : E}
 : HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤
-/
theorem hasFPowerSeriesAt_const {c : F} {e : E} :
    HasFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e :=
  ⟨⊤, hasFPowerSeriesOnBall_const⟩

@[fun_prop]
/-
**analyticAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _ => v) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFPowerSeriesAt_const`：hasFPowerSeriesAt_const {c : F} {e : E} : HasFP
owerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e
-/
theorem analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, hasFPowerSeriesAt_const⟩
/-
**analyticOnNhd_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_const {v : F} {s : Set E} : AnalyticOnNhd 𝕜 (fun _ => v) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
-/
theorem analyticOnNhd_const {v : F} {s : Set E} : AnalyticOnNhd 𝕜 (fun _ => v) s :=
  fun _ _ => analyticAt_const
/-
**analyticWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticWithinAt_const {v : F} {s : Set E} {x : E} : AnalyticWithinAt 𝕜 (f
un _ => v) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
-/
theorem analyticWithinAt_const {v : F} {s : Set E} {x : E} : AnalyticWithinAt 𝕜 (fun _ => v) s x :=
  analyticAt_const.analyticWithinAt
/-
**analyticOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_const {v : F} {s : Set E} : AnalyticOn 𝕜 (fun _ => v) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s
-/
theorem analyticOn_const {v : F} {s : Set E} : AnalyticOn 𝕜 (fun _ => v) s :=
  analyticOnNhd_const.analyticOn

/-!
### Addition, negation, subtraction, scalar multiplication
-/

section

variable {f g : E → F} {pf pg : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}
  {R : Type*} [NormedRing R] [Module R F] [IsBoundedSMul R F] [SMulCommClass 𝕜 R F] {c : R}

/-
**HasFPowerSeriesWithinOnBall.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.add (hf : HasFPowerSeriesWithinOnBall f pf s x
 r) (hg : HasFPowerSeriesWithinOnBall g pg s x r) : HasFPowerSeriesWithinOnBall 
(f + g) (pf + pg) s x r
参数：hf : HasFPowerSeriesWithinOnBall f pf s x r；hg : HasFPowerSeriesWithinOnBall 
g pg s x r。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_min_iff`：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.min_radius_le_radius_add`：min_radius_le_radius_a
dd (p q : FormalMultilinearSeries 𝕜 E F) : min p.radius q.radius <= (p + q).radi
us
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesWithinOnBall.add (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (hg : HasFPowerSeriesWithinOnBall g pg s x r) :
    HasFPowerSeriesWithinOnBall (f + g) (pf + pg) s x r :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).add (hg.hasSum hy h'y) }
/-
**HasFPowerSeriesOnBall.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.add (hf : HasFPowerSeriesOnBall f pf x r) (hg : HasF
PowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall (f + g) (pf + pg) x r
参数：hf : HasFPowerSeriesOnBall f pf x r；hg : HasFPowerSeriesOnBall g pg x r。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_min_iff`：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.min_radius_le_radius_add`：min_radius_le_radius_a
dd (p q : FormalMultilinearSeries 𝕜 E F) : min p.radius q.radius <= (p + q).radi
us
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.add (hf : HasFPowerSeriesOnBall f pf x r)
    (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall (f + g) (pf + pg) x r :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).add (hg.hasSum hy) }
/-
**HasFPowerSeriesWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.add (hf : HasFPowerSeriesWithinAt f pf s x) (hg : 
HasFPowerSeriesWithinAt g pg s x) : HasFPowerSeriesWithinAt (f + g) (pf + pg) s 
x
参数：hf : HasFPowerSeriesWithinAt f pf s x；hg : HasFPowerSeriesWithinAt g pg s x。
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
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `HasFPowerSeriesWithinAt.eventually`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.add`：HasFPowerSeriesWithinOnBall.add (hf : H
asFPowerSeriesWithinOnBall f pf s x r) (hg : HasFPowerSeriesWithinOnBall g pg s 
x r) : HasFPowerSerie…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasFPowerSeriesWithinAt.add
    (hf : HasFPowerSeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) :
    HasFPowerSeriesWithinAt (f + g) (pf + pg) s x := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
/-
**HasFPowerSeriesAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.add (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSerie
sAt g pg x) : HasFPowerSeriesAt (f + g) (pf + pg) x
参数：hf : HasFPowerSeriesAt f pf x；hg : HasFPowerSeriesAt g pg x。
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
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `HasFPowerSeriesAt.eventually`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.add`：HasFPowerSeriesOnBall.add (hf : HasFPowerSeri
esOnBall f pf x r) (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall
 (f + g) (pf + …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasFPowerSeriesAt.add (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x) :
    HasFPowerSeriesAt (f + g) (pf + pg) x := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
/-
**AnalyticWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinA
t 𝕜 g s x) : AnalyticWithinAt 𝕜 (f + g) s x
参数：hf : AnalyticWithinAt 𝕜 f s x；hg : AnalyticWithinAt 𝕜 g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.analyticWithinAt`：HasFPowerSeriesWithinAt.analyt
icWithinAt (hf : HasFPowerSeriesWithinAt f p s x) : AnalyticWithinAt 𝕜 f s x
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
· 使用定理 `HasFPowerSeriesWithinAt.add`：HasFPowerSeriesWithinAt.add (hf : HasFPower
SeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) : HasFPowerSeri
esWithinAt (f + g…
-/
theorem AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (f + g) s x :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticWithinAt

@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticA
t 𝕜 (f + g) x
参数：hf : AnalyticAt 𝕜 f x；hg : AnalyticAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
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
· 使用定理 `HasFPowerSeriesAt.add`：HasFPowerSeriesAt.add (hf : HasFPowerSeriesAt f p
f x) (hg : HasFPowerSeriesAt g pg x) : HasFPowerSeriesAt (f + g) (pf + pg) x
-/
theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (f + g) x :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticAt
/-
**AnalyticOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.add (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) : AnalyticO
n 𝕜 (f + g) s
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.add`：AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s 
x) (hg : AnalyticWithinAt 𝕜 g s x) : AnalyticWithinAt 𝕜 (f + g) s x
-/
theorem AnalyticOn.add (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)
/-
**AnalyticOnNhd.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.add (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) : 
AnalyticOnNhd 𝕜 (f + g) s
参数：hf : AnalyticOnNhd 𝕜 f s；hg : AnalyticOnNhd 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
-/
theorem AnalyticOnNhd.add (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)
/-
**HasFPowerSeriesWithinOnBall.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.neg (hf : HasFPowerSeriesWithinOnBall f pf s x
 r) : HasFPowerSeriesWithinOnBall (-f) (-pf) s x r
参数：hf : HasFPowerSeriesWithinOnBall f pf s x r。
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
· 使用定理 `FormalMultilinearSeries.radius_neg`：radius_neg (p : FormalMultilinearSer
ies 𝕜 E F) : (-p).radius = p.radius
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasSum.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [ins
t : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f
…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesWithinOnBall.neg (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (-f) (-pf) s x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).neg }
/-
**HasFPowerSeriesOnBall.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.neg (hf : HasFPowerSeriesOnBall f pf x r) : HasFPowe
rSeriesOnBall (-f) (-pf) x r
参数：hf : HasFPowerSeriesOnBall f pf x r。
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
· 使用定理 `FormalMultilinearSeries.radius_neg`：radius_neg (p : FormalMultilinearSer
ies 𝕜 E F) : (-p).radius = p.radius
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasSum.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [ins
t : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f
…
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.neg (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (-f) (-pf) x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).neg }
/-
**HasFPowerSeriesWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.neg (hf : HasFPowerSeriesWithinAt f pf s x) : HasF
PowerSeriesWithinAt (-f) (-pf) s x
参数：hf : HasFPowerSeriesWithinAt f pf s x。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt`：HasFPowerSeriesWith
inOnBall.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : 
HasFPowerSeriesWithinAt f p s x
· 使用定理 `HasFPowerSeriesWithinOnBall.neg`：HasFPowerSeriesWithinOnBall.neg (hf : H
asFPowerSeriesWithinOnBall f pf s x r) : HasFPowerSeriesWithinOnBall (-f) (-pf) 
s x r
-/
theorem HasFPowerSeriesWithinAt.neg (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (-f) (-pf) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesWithinAt
/-
**HasFPowerSeriesAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.neg (hf : HasFPowerSeriesAt f pf x) : HasFPowerSeriesAt 
(-f) (-pf) x
参数：hf : HasFPowerSeriesAt f pf x。
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
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `HasFPowerSeriesOnBall.neg`：HasFPowerSeriesOnBall.neg (hf : HasFPowerSeri
esOnBall f pf x r) : HasFPowerSeriesOnBall (-f) (-pf) x r
-/
theorem HasFPowerSeriesAt.neg (hf : HasFPowerSeriesAt f pf x) : HasFPowerSeriesAt (-f) (-pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesAt
/-
**AnalyticWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.neg (hf : AnalyticWithinAt 𝕜 f s x) : AnalyticWithinAt 𝕜 
(-f) s x
参数：hf : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.analyticWithinAt`：HasFPowerSeriesWithinAt.analyt
icWithinAt (hf : HasFPowerSeriesWithinAt f p s x) : AnalyticWithinAt 𝕜 f s x
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
· 使用定理 `HasFPowerSeriesWithinAt.neg`：HasFPowerSeriesWithinAt.neg (hf : HasFPower
SeriesWithinAt f pf s x) : HasFPowerSeriesWithinAt (-f) (-pf) s x
-/
theorem AnalyticWithinAt.neg (hf : AnalyticWithinAt 𝕜 f s x) : AnalyticWithinAt 𝕜 (-f) s x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticWithinAt

@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
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
· 使用定理 `HasFPowerSeriesAt.neg`：HasFPowerSeriesAt.neg (hf : HasFPowerSeriesAt f p
f x) : HasFPowerSeriesAt (-f) (-pf) x
-/
theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticAt
/-
**analyticAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} {F : Ty
pe u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   AnalyticA
t 𝕜 (-f) x ↔ AnalyticAt 𝕜 f x
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `AnalyticAt.neg`：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-
f) x
-/
@[simp] lemma analyticAt_neg : AnalyticAt 𝕜 (-f) x ↔ AnalyticAt 𝕜 f x where
  mp hf := by simpa using hf.neg
  mpr := .neg
/-
**AnalyticOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.neg (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (-f) s
参数：hf : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.neg`：AnalyticWithinAt.neg (hf : AnalyticWithinAt 𝕜 f s 
x) : AnalyticWithinAt 𝕜 (-f) s x
-/
theorem AnalyticOn.neg (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (-f) s :=
  fun z hz ↦ (hf z hz).neg
/-
**AnalyticOnNhd.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.neg (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (-f) s
参数：hf : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.neg`：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-
f) x
-/
theorem AnalyticOnNhd.neg (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (-f) s :=
  fun z hz ↦ (hf z hz).neg
/-
**HasFPowerSeriesWithinOnBall.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.sub (hf : HasFPowerSeriesWithinOnBall f pf s x
 r) (hg : HasFPowerSeriesWithinOnBall g pg s x r) : HasFPowerSeriesWithinOnBall 
(f - g) (pf - pg) s x r
参数：hf : HasFPowerSeriesWithinOnBall f pf s x r；hg : HasFPowerSeriesWithinOnBall 
g pg s x r。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFPowerSeriesWithinOnBall.add`：HasFPowerSeriesWithinOnBall.add (hf : H
asFPowerSeriesWithinOnBall f pf s x r) (hg : HasFPowerSeriesWithinOnBall g pg s 
x r) : HasFPowerSerie…
· 使用定理 `HasFPowerSeriesWithinOnBall.neg`：HasFPowerSeriesWithinOnBall.neg (hf : H
asFPowerSeriesWithinOnBall f pf s x r) : HasFPowerSeriesWithinOnBall (-f) (-pf) 
s x r
-/
theorem HasFPowerSeriesWithinOnBall.sub (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (hg : HasFPowerSeriesWithinOnBall g pg s x r) :
    HasFPowerSeriesWithinOnBall (f - g) (pf - pg) s x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**HasFPowerSeriesOnBall.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.sub (hf : HasFPowerSeriesOnBall f pf x r) (hg : HasF
PowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall (f - g) (pf - pg) x r
参数：hf : HasFPowerSeriesOnBall f pf x r；hg : HasFPowerSeriesOnBall g pg x r。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFPowerSeriesOnBall.add`：HasFPowerSeriesOnBall.add (hf : HasFPowerSeri
esOnBall f pf x r) (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall
 (f + g) (pf + …
· 使用定理 `HasFPowerSeriesOnBall.neg`：HasFPowerSeriesOnBall.neg (hf : HasFPowerSeri
esOnBall f pf x r) : HasFPowerSeriesOnBall (-f) (-pf) x r
-/
theorem HasFPowerSeriesOnBall.sub (hf : HasFPowerSeriesOnBall f pf x r)
    (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall (f - g) (pf - pg) x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**HasFPowerSeriesWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.sub (hf : HasFPowerSeriesWithinAt f pf s x) (hg : 
HasFPowerSeriesWithinAt g pg s x) : HasFPowerSeriesWithinAt (f - g) (pf - pg) s 
x
参数：hf : HasFPowerSeriesWithinAt f pf s x；hg : HasFPowerSeriesWithinAt g pg s x。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFPowerSeriesWithinAt.add`：HasFPowerSeriesWithinAt.add (hf : HasFPower
SeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) : HasFPowerSeri
esWithinAt (f + g…
· 使用定理 `HasFPowerSeriesWithinAt.neg`：HasFPowerSeriesWithinAt.neg (hf : HasFPower
SeriesWithinAt f pf s x) : HasFPowerSeriesWithinAt (-f) (-pf) s x
-/
theorem HasFPowerSeriesWithinAt.sub
    (hf : HasFPowerSeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) :
    HasFPowerSeriesWithinAt (f - g) (pf - pg) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**HasFPowerSeriesAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.sub (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSerie
sAt g pg x) : HasFPowerSeriesAt (f - g) (pf - pg) x
参数：hf : HasFPowerSeriesAt f pf x；hg : HasFPowerSeriesAt g pg x。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFPowerSeriesAt.add`：HasFPowerSeriesAt.add (hf : HasFPowerSeriesAt f p
f x) (hg : HasFPowerSeriesAt g pg x) : HasFPowerSeriesAt (f + g) (pf + pg) x
· 使用定理 `HasFPowerSeriesAt.neg`：HasFPowerSeriesAt.neg (hf : HasFPowerSeriesAt f p
f x) : HasFPowerSeriesAt (-f) (-pf) x
-/
theorem HasFPowerSeriesAt.sub (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x) :
    HasFPowerSeriesAt (f - g) (pf - pg) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**AnalyticWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.sub (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinA
t 𝕜 g s x) : AnalyticWithinAt 𝕜 (f - g) s x
参数：hf : AnalyticWithinAt 𝕜 f s x；hg : AnalyticWithinAt 𝕜 g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `AnalyticWithinAt.add`：AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s 
x) (hg : AnalyticWithinAt 𝕜 g s x) : AnalyticWithinAt 𝕜 (f + g) s x
· 使用定理 `AnalyticWithinAt.neg`：AnalyticWithinAt.neg (hf : AnalyticWithinAt 𝕜 f s 
x) : AnalyticWithinAt 𝕜 (-f) s x
-/
theorem AnalyticWithinAt.sub (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (f - g) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticA
t 𝕜 (f - g) x
参数：hf : AnalyticAt 𝕜 f x；hg : AnalyticAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用定理 `AnalyticAt.neg`：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-
f) x
-/
theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**AnalyticOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.sub (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) : AnalyticO
n 𝕜 (f - g) s
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.sub`：AnalyticWithinAt.sub (hf : AnalyticWithinAt 𝕜 f s 
x) (hg : AnalyticWithinAt 𝕜 g s x) : AnalyticWithinAt 𝕜 (f - g) s x
-/
theorem AnalyticOn.sub (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)
/-
**AnalyticOnNhd.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) : 
AnalyticOnNhd 𝕜 (f - g) s
参数：hf : AnalyticOnNhd 𝕜 f s；hg : AnalyticOnNhd 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
-/
theorem AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)
/-
**HasFPowerSeriesWithinOnBall.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.const_smul (hf : HasFPowerSeriesWithinOnBall f
 pf s x r) : HasFPowerSeriesWithinOnBall (c • f) (c • pf) s x r where r_le
参数：hf : HasFPowerSeriesWithinOnBall f pf s x r。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.radius_le_smul`：radius_le_smul {p : FormalMultil
inearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [SMulComm
Class 𝕜 𝕜' F] [IsBoundedSMul…
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesWithinOnBall.const_smul (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (c • f) (c • pf) s x r where
  r_le := le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy h'y => (hf.hasSum hy h'y).const_smul _
/-
**HasFPowerSeriesOnBall.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.const_smul (hf : HasFPowerSeriesOnBall f pf x r) : H
asFPowerSeriesOnBall (c • f) (c • pf) x r where r_le
参数：hf : HasFPowerSeriesOnBall f pf x r。
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
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.radius_le_smul`：radius_le_smul {p : FormalMultil
inearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [SMulComm
Class 𝕜 𝕜' F] [IsBoundedSMul…
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.const_smul (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (c • f) (c • pf) x r where
  r_le := le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy => (hf.hasSum hy).const_smul _
/-
**HasFPowerSeriesWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.const_smul (hf : HasFPowerSeriesWithinAt f pf s x)
 : HasFPowerSeriesWithinAt (c • f) (c • pf) s x
参数：hf : HasFPowerSeriesWithinAt f pf s x。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt`：HasFPowerSeriesWith
inOnBall.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : 
HasFPowerSeriesWithinAt f p s x
· 使用定理 `HasFPowerSeriesWithinOnBall.const_smul`：HasFPowerSeriesWithinOnBall.cons
t_smul (hf : HasFPowerSeriesWithinOnBall f pf s x r) : HasFPowerSeriesWithinOnBa
ll (c • f) (c • pf) s x r wh…
-/
theorem HasFPowerSeriesWithinAt.const_smul (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (c • f) (c • pf) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesWithinAt
/-
**HasFPowerSeriesAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.const_smul (hf : HasFPowerSeriesAt f pf x) : HasFPowerSe
riesAt (c • f) (c • pf) x
参数：hf : HasFPowerSeriesAt f pf x。
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
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `HasFPowerSeriesOnBall.const_smul`：HasFPowerSeriesOnBall.const_smul (hf :
 HasFPowerSeriesOnBall f pf x r) : HasFPowerSeriesOnBall (c • f) (c • pf) x r wh
ere r_le
-/
theorem HasFPowerSeriesAt.const_smul (hf : HasFPowerSeriesAt f pf x) :
    HasFPowerSeriesAt (c • f) (c • pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesAt
/-
**AnalyticWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.const_smul (hf : AnalyticWithinAt 𝕜 f s x) : AnalyticWith
inAt 𝕜 (c • f) s x
参数：hf : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.analyticWithinAt`：HasFPowerSeriesWithinAt.analyt
icWithinAt (hf : HasFPowerSeriesWithinAt f p s x) : AnalyticWithinAt 𝕜 f s x
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
· 使用定理 `HasFPowerSeriesWithinAt.const_smul`：HasFPowerSeriesWithinAt.const_smul (
hf : HasFPowerSeriesWithinAt f pf s x) : HasFPowerSeriesWithinAt (c • f) (c • pf
) s x
-/
theorem AnalyticWithinAt.const_smul (hf : AnalyticWithinAt 𝕜 f s x) :
    AnalyticWithinAt 𝕜 (c • f) s x :=
  let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticWithinAt

@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.const_smul (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (c • f) x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
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
· 使用定理 `HasFPowerSeriesAt.const_smul`：HasFPowerSeriesAt.const_smul (hf : HasFPow
erSeriesAt f pf x) : HasFPowerSeriesAt (c • f) (c • pf) x
-/
theorem AnalyticAt.const_smul (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (c • f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticAt

@[to_fun]
/-
**AnalyticOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.const_smul (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (c • f) s
参数：hf : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.const_smul`：AnalyticWithinAt.const_smul (hf : AnalyticW
ithinAt 𝕜 f s x) : AnalyticWithinAt 𝕜 (c • f) s x
-/
theorem AnalyticOn.const_smul (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (c • f) s :=
  fun x hx ↦ (hf x hx).const_smul

@[to_fun]
/-
**AnalyticOnNhd.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.const_smul (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (c •
 f) s
参数：hf : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.const_smul`：AnalyticAt.const_smul (hf : AnalyticAt 𝕜 f x) : A
nalyticAt 𝕜 (c • f) x
-/
theorem AnalyticOnNhd.const_smul (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (c • f) s :=
  fun x hx ↦ (hf x hx).const_smul
/-
**AnalyticWithinAt.div_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.div_const {f : E -> 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c
 : 𝕝} : AnalyticWithinAt 𝕜 (f · / c) s x
参数：hf : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `AnalyticWithinAt.const_smul`：AnalyticWithinAt.const_smul (hf : AnalyticW
ithinAt 𝕜 f s x) : AnalyticWithinAt 𝕜 (c • f) s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AnalyticWithinAt.div_const {f : E → 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c : 𝕝} :
    AnalyticWithinAt 𝕜 (f · / c) s x := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

@[fun_prop]
/-
**AnalyticAt.div_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.div_const {f : E -> 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝} : Analyt
icAt 𝕜 (f · / c) x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `AnalyticAt.const_smul`：AnalyticAt.const_smul (hf : AnalyticAt 𝕜 f x) : A
nalyticAt 𝕜 (c • f) x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AnalyticAt.div_const {f : E → 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝} :
    AnalyticAt 𝕜 (f · / c) x := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)
/-
**AnalyticOn.div_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.div_const {f : E -> 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝} : Analyt
icOn 𝕜 (f · / c) s
参数：hf : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `AnalyticOn.const_smul`：AnalyticOn.const_smul (hf : AnalyticOn 𝕜 f s) : A
nalyticOn 𝕜 (c • f) s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AnalyticOn.div_const {f : E → 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝} :
    AnalyticOn 𝕜 (f · / c) s := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)
/-
**AnalyticOnNhd.div_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.div_const {f : E -> 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝} : 
AnalyticOnNhd 𝕜 (f · / c) s
参数：hf : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `AnalyticOnNhd.const_smul`：AnalyticOnNhd.const_smul (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOnNhd 𝕜 (c • f) s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AnalyticOnNhd.div_const {f : E → 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝} :
    AnalyticOnNhd 𝕜 (f · / c) s := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

end

/-!
### Cartesian products are analytic
-/

/-- The radius of the Cartesian product of two formal series is the minimum of their radii. -/
/-
**FormalMultilinearSeries.radius_prod_eq_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FormalMultilinearSeries.radius_prod_eq_min (p : FormalMultilinearSeries 𝕜 
E F) (q : FormalMultilinearSeries 𝕜 E G) : (p.prod q).radius = min p.radius q.ra
dius
参数：p : FormalMultilinearSeries 𝕜 E F；q : FormalMultilinearSeries 𝕜 E G。
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
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_min_iff`：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
· 使用定理 `FormalMultilinearSeries.isLittleO_one_of_lt_radius`：isLittleO_one_of_lt_
radius (h : ↑r < p.radius) : (fun n => ‖p n‖ * (r : Real) ^ n) =o[atTop] (fun _ 
=> 1 : Nat -> Real)
· 使用定理 `FormalMultilinearSeries.le_radius_of_isBigO`：le_radius_of_isBigO (h : (f
un n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : ↑r <= p.radius
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `FormalMultilinearSeries.prod.eq_1`：∀ {𝕜 : Type u} {E : Type v} {F : Type
 w} {G : Type x} [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E]   [inst_2 : _roo
t_.Module 𝕜 E] [inst_3 …
· 使用定理 `ContinuousMultilinearMap.opNorm_prod`：opNorm_prod (f : ContinuousMultili
nearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') : ‖f.prod g‖ = max ‖f‖ ‖g‖
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The radius of the Cartesian product of two formal series is the minimum of their
 radii.
-/
lemma FormalMultilinearSeries.radius_prod_eq_min
    (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    (p.prod q).radius = min p.radius q.radius := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [le_min_iff]
    have := (p.prod q).isLittleO_one_of_lt_radius hr
    constructor
    all_goals
      apply FormalMultilinearSeries.le_radius_of_isBigO
      refine (isBigO_of_le _ fun n ↦ ?_).trans this.isBigO
      rw [norm_mul, norm_norm, norm_mul, norm_norm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.opNorm_prod]
    · apply le_max_left
    · apply le_max_right
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [lt_min_iff] at hr
    have := ((p.isLittleO_one_of_lt_radius hr.1).add
      (q.isLittleO_one_of_lt_radius hr.2)).isBigO
    refine (p.prod q).le_radius_of_isBigO ((isBigO_of_le _ fun n ↦ ?_).trans this)
    rw [norm_mul, norm_norm, ← add_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.opNorm_prod]
    refine (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans ?_
    apply Real.le_norm_self
/-
**HasFPowerSeriesWithinOnBall.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.prod {e : E} {f : E -> F} {g : E -> G} {r s : 
Real>=0∞} {t : Set E} {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinear
Series 𝕜 E G} (hf : HasFPowerSeriesWithinOnBall f p t e r) (hg : HasFPowerSeries
WithinOnBall g q t e s) : HasFPowerSeriesWithinOnBall (fun x => (f x, g x)) (p.p
rod q) t e (min r s) where r_le
参数：hf : HasFPowerSeriesWithinOnBall f p t e r；hg : HasFPowerSeriesWithinOnBall g
 q t e s。
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
· 使用引理 `FormalMultilinearSeries.radius_prod_eq_min`：FormalMultilinearSeries.radi
us_prod_eq_min (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 
𝕜 E G) : (p.prod q).radius = min…
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasSum.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {L : Summa
tionFilter β} [inst : AddCommMonoid α]   [inst_1 : TopologicalSpace α] [inst_2 :
 Ad…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
lemma HasFPowerSeriesWithinOnBall.prod {e : E} {f : E → F} {g : E → G} {r s : ℝ≥0∞} {t : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinOnBall f p t e r) (hg : HasFPowerSeriesWithinOnBall g q t e s) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f x, g x)) (p.prod q) t e (min r s) where
  r_le := by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y h'y hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum h'y ?_).prodMk (hg.hasSum h'y ?_)
    · exact Metric.mem_eball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
    · exact Metric.mem_eball.mpr (lt_of_lt_of_le hy (min_le_right _ _))
/-
**HasFPowerSeriesOnBall.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.prod {e : E} {f : E -> F} {g : E -> G} {r s : Real>=
0∞} {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G} (hf 
: HasFPowerSeriesOnBall f p e r) (hg : HasFPowerSeriesOnBall g q e s) : HasFPowe
rSeriesOnBall (fun x => (f x, g x)) (p.prod q) e (min r s)
参数：hf : HasFPowerSeriesOnBall f p e r；hg : HasFPowerSeriesOnBall g q e s。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.prod`：HasFPowerSeriesWithinOnBall.prod {e : 
E} {f : E -> F} {g : E -> G} {r s : Real>=0∞} {t : Set E} {p : FormalMultilinear
Series 𝕜 E F} {q : For…
-/
lemma HasFPowerSeriesOnBall.prod {e : E} {f : E → F} {g : E → G} {r s : ℝ≥0∞}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesOnBall f p e r) (hg : HasFPowerSeriesOnBall g q e s) :
    HasFPowerSeriesOnBall (fun x ↦ (f x, g x)) (p.prod q) e (min r s) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.prod hg
/-
**HasFPowerSeriesWithinAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.prod {e : E} {f : E -> F} {g : E -> G} {s : Set E}
 {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G} (hf : H
asFPowerSeriesWithinAt f p s e) (hg : HasFPowerSeriesWithinAt g q s e) : HasFPow
erSeriesWithinAt (fun x => (f x, g x)) (p.prod q) s e
参数：hf : HasFPowerSeriesWithinAt f p s e；hg : HasFPowerSeriesWithinAt g q s e。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.prod`：HasFPowerSeriesWithinOnBall.prod {e : 
E} {f : E -> F} {g : E -> G} {r s : Real>=0∞} {t : Set E} {p : FormalMultilinear
Series 𝕜 E F} {q : For…
-/
lemma HasFPowerSeriesWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinAt f p s e) (hg : HasFPowerSeriesWithinAt g q s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (f x, g x)) (p.prod q) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩
/-
**HasFPowerSeriesAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.prod {e : E} {f : E -> F} {g : E -> G} {p : FormalMultil
inearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G} (hf : HasFPowerSeriesAt f
 p e) (hg : HasFPowerSeriesAt g q e) : HasFPowerSeriesAt (fun x => (f x, g x)) (
p.prod q) e
参数：hf : HasFPowerSeriesAt f p e；hg : HasFPowerSeriesAt g q e。
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
· 使用引理 `HasFPowerSeriesOnBall.prod`：HasFPowerSeriesOnBall.prod {e : E} {f : E ->
 F} {g : E -> G} {r s : Real>=0∞} {p : FormalMultilinearSeries 𝕜 E F} {q : Forma
lMultilinearSeri…
-/
lemma HasFPowerSeriesAt.prod {e : E} {f : E → F} {g : E → G}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesAt f p e) (hg : HasFPowerSeriesAt g q e) :
    HasFPowerSeriesAt (fun x ↦ (f x, g x)) (p.prod q) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
/-
**AnalyticWithinAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.prod {e : E} {f : E -> F} {g : E -> G} {s : Set E} (hf : 
AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s e) : AnalyticWithinAt 𝕜 (
fun x => (f x, g x)) s e
参数：hf : AnalyticWithinAt 𝕜 f s e；hg : AnalyticWithinAt 𝕜 g s e。
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
· 使用引理 `HasFPowerSeriesWithinAt.prod`：HasFPowerSeriesWithinAt.prod {e : E} {f : 
E -> F} {g : E -> G} {s : Set E} {p : FormalMultilinearSeries 𝕜 E F} {q : Formal
MultilinearSeries …

--- 原说明 ---
The Cartesian product of analytic functions is analytic.
-/
lemma AnalyticWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f x, g x)) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
@[fun_prop]
/-
**AnalyticAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.prod {e : E} {f : E -> F} {g : E -> G} (hf : AnalyticAt 𝕜 f e) 
(hg : AnalyticAt 𝕜 g e) : AnalyticAt 𝕜 (fun x => (f x, g x)) e
参数：hf : AnalyticAt 𝕜 f e；hg : AnalyticAt 𝕜 g e。
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
· 使用引理 `HasFPowerSeriesAt.prod`：HasFPowerSeriesAt.prod {e : E} {f : E -> F} {g :
 E -> G} {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
 (hf : HasFP…

--- 原说明 ---
The Cartesian product of analytic functions is analytic.
-/
lemma AnalyticAt.prod {e : E} {f : E → F} {g : E → G}
    (hf : AnalyticAt 𝕜 f e) (hg : AnalyticAt 𝕜 g e) :
    AnalyticAt 𝕜 (fun x ↦ (f x, g x)) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions within a set is analytic. -/
/-
**AnalyticOn.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.prod {f : E -> F} {g : E -> G} {s : Set E} (hf : AnalyticOn 𝕜 f
 s) (hg : AnalyticOn 𝕜 g s) : AnalyticOn 𝕜 (fun x => (f x, g x)) s
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.prod`：AnalyticWithinAt.prod {e : E} {f : E -> F} {g : E
 -> G} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s 
e) : Analyt…

--- 原说明 ---
The Cartesian product of analytic functions within a set is analytic.
-/
lemma AnalyticOn.prod {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-- The Cartesian product of analytic functions is analytic. -/
/-
**AnalyticOnNhd.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.prod {f : E -> F} {g : E -> G} {s : Set E} (hf : AnalyticOnN
hd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (fun x => (f x, g x)) s
参数：hf : AnalyticOnNhd 𝕜 f s；hg : AnalyticOnNhd 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.prod`：AnalyticAt.prod {e : E} {f : E -> F} {g : E -> G} (hf :
 AnalyticAt 𝕜 f e) (hg : AnalyticAt 𝕜 g e) : AnalyticAt 𝕜 (fun x => (f x, g x)) 
e

--- 原说明 ---
The Cartesian product of analytic functions is analytic.
-/
lemma AnalyticOnNhd.prod {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-- `AnalyticAt.comp` for functions on product spaces -/
/-
**AnalyticAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg : AnalyticAt 𝕜 g (f 
x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
参数：hg : AnalyticAt 𝕜 g (f x)；hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
`AnalyticAt.comp` for functions on product spaces
-/
theorem AnalyticAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {x : E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x)
    (ga : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun x ↦ h (f x, g x)) x :=
  AnalyticAt.comp ha (fa.prod ga)

/-- `AnalyticWithinAt.comp` for functions on product spaces -/
/-
**AnalyticWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {x : E} {t : Set F} {s : S
et E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : AnalyticWithinAt 𝕜 f s x) (h : S
et.MapsTo f s t) : AnalyticWithinAt 𝕜 (g ∘ f) s x
参数：hg : AnalyticWithinAt 𝕜 g t (f x)；hf : AnalyticWithinAt 𝕜 f s x；h : Set.MapsT
o f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.analyticWithinAt`：HasFPowerSeriesWithinAt.analyt
icWithinAt (hf : HasFPowerSeriesWithinAt f p s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesWithinAt.comp`：HasFPowerSeriesWithinAt.comp {g : F -> G} 
{f : E -> F} {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 
E F} {x : E} {t : …

--- 原说明 ---
`AnalyticWithinAt.comp` for functions on product spaces
-/
theorem AnalyticWithinAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
    {t : Set E} {x : E}
    (ha : AnalyticWithinAt 𝕜 h s (f x, g x)) (fa : AnalyticWithinAt 𝕜 f t x)
    (ga : AnalyticWithinAt 𝕜 g t x) (hf : Set.MapsTo (fun y ↦ (f y, g y)) t s) :
    AnalyticWithinAt 𝕜 (fun x ↦ h (f x, g x)) t x :=
  AnalyticWithinAt.comp ha (fa.prod ga) hf

/-- `AnalyticAt.comp_analyticWithinAt` for functions on product spaces -/
/-
**AnalyticAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg : AnalyticAt 𝕜 g (f 
x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
参数：hg : AnalyticAt 𝕜 g (f x)；hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
`AnalyticAt.comp_analyticWithinAt` for functions on product spaces
-/
theorem AnalyticAt.comp₂_analyticWithinAt
    {h : F × G → H} {f : E → F} {g : E → G} {x : E} {s : Set E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticWithinAt 𝕜 f s x)
    (ga : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (fun x ↦ h (f x, g x)) s x :=
  AnalyticAt.comp_analyticWithinAt ha (fa.prod ga)

/-- `AnalyticOnNhd.comp` for functions on product spaces -/
/-
**AnalyticOnNhd.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg :
 AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set.MapsTo f s t) : Analy
ticOnNhd 𝕜 (g ∘ f) s
参数：hg : AnalyticOnNhd 𝕜 g t；hf : AnalyticOnNhd 𝕜 f s；st : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.comp'`：AnalyticOnNhd.comp' {s : Set E} {g : F -> G} {f : E
 -> F} (hg : AnalyticOnNhd 𝕜 g (s.image f)) (hf : AnalyticOnNhd 𝕜 f s) : Analyti
cOnNhd 𝕜 …
· 使用定理 `AnalyticOnNhd.mono`：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd
 𝕜 f t) (hst : s subseteq t) : AnalyticOnNhd 𝕜 f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t

--- 原说明 ---
`AnalyticOnNhd.comp` for functions on product spaces
-/
theorem AnalyticOnNhd.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)} {t : Set E}
    (ha : AnalyticOnNhd 𝕜 h s) (fa : AnalyticOnNhd 𝕜 f t) (ga : AnalyticOnNhd 𝕜 g t)
    (m : ∀ x, x ∈ t → (f x, g x) ∈ s) : AnalyticOnNhd 𝕜 (fun x ↦ h (f x, g x)) t :=
  fun _ xt ↦ (ha _ (m _ xt)).comp₂ (fa _ xt) (ga _ xt)

/-- `AnalyticOn.comp` for functions on product spaces -/
/-
**AnalyticOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F} {t : Set E} (hf : An
alyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) : AnalyticOn 𝕜 (f
 ∘ g) t
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g t；h : Set.MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…

--- 原说明 ---
`AnalyticOn.comp` for functions on product spaces
-/
theorem AnalyticOn.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
    {t : Set E}
    (ha : AnalyticOn 𝕜 h s) (fa : AnalyticOn 𝕜 f t)
    (ga : AnalyticOn 𝕜 g t) (m : Set.MapsTo (fun y ↦ (f y, g y)) t s) :
    AnalyticOn 𝕜 (fun x ↦ h (f x, g x)) t :=
  fun x hx ↦ (ha _ (m hx)).comp₂ (fa x hx) (ga x hx) m

/-- Analytic functions on products are analytic in the first coordinate -/
/-
**AnalyticAt.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.curry_left {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p)
 : AnalyticAt 𝕜 (fun x => f (x, p.2)) p.1
参数：fa : AnalyticAt 𝕜 f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp₂`：AnalyticAt.comp₂ {h : F × G -> H} {f : E -> F} {g : E 
-> G} {x : E} (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x) (ga : Ana
lyticA…
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x

--- 原说明 ---
Analytic functions on products are analytic in the first coordinate
-/
theorem AnalyticAt.curry_left {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun x ↦ f (x, p.2)) p.1 :=
  AnalyticAt.comp₂ fa analyticAt_id analyticAt_const
alias AnalyticAt.along_fst := AnalyticAt.curry_left
/-
**AnalyticWithinAt.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.curry_left {f : E × F -> G} {s : Set (E × F)} {p : E × F}
 (fa : AnalyticWithinAt 𝕜 f s p) : AnalyticWithinAt 𝕜 (fun x => f (x, p.2)) {x |
 (x, p.2) in s} p.1
参数：E × F；fa : AnalyticWithinAt 𝕜 f s p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp₂`：AnalyticWithinAt.comp₂ {h : F × G -> H} {f : E -
> F} {g : E -> G} {s : Set (F × G)} {t : Set E} {x : E} (ha : AnalyticWithinAt 𝕜
 h s (f x, g…
· 使用引理 `analyticWithinAt_id`：analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E ->
 E) s z
· 使用定理 `analyticWithinAt_const`：analyticWithinAt_const {v : F} {s : Set E} {x : 
E} : AnalyticWithinAt 𝕜 (fun _ => v) s x
-/
theorem AnalyticWithinAt.curry_left
    {f : E × F → G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun x ↦ f (x, p.2)) {x | (x, p.2) ∈ s} p.1 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_id analyticWithinAt_const (fun _ hx ↦ hx)

/-- Analytic functions on products are analytic in the second coordinate -/
/-
**AnalyticAt.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.curry_right {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p
) : AnalyticAt 𝕜 (fun y => f (p.1, y)) p.2
参数：fa : AnalyticAt 𝕜 f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp₂`：AnalyticAt.comp₂ {h : F × G -> H} {f : E -> F} {g : E 
-> G} {x : E} (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x) (ga : Ana
lyticA…
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z

--- 原说明 ---
Analytic functions on products are analytic in the second coordinate
-/
theorem AnalyticAt.curry_right {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun y ↦ f (p.1, y)) p.2 :=
  AnalyticAt.comp₂ fa analyticAt_const analyticAt_id
alias AnalyticAt.along_snd := AnalyticAt.curry_right
/-
**AnalyticWithinAt.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.curry_right {f : E × F -> G} {s : Set (E × F)} {p : E × F
} (fa : AnalyticWithinAt 𝕜 f s p) : AnalyticWithinAt 𝕜 (fun y => f (p.1, y)) {y 
| (p.1, y) in s} p.2
参数：E × F；fa : AnalyticWithinAt 𝕜 f s p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp₂`：AnalyticWithinAt.comp₂ {h : F × G -> H} {f : E -
> F} {g : E -> G} {s : Set (F × G)} {t : Set E} {x : E} (ha : AnalyticWithinAt 𝕜
 h s (f x, g…
· 使用定理 `analyticWithinAt_const`：analyticWithinAt_const {v : F} {s : Set E} {x : 
E} : AnalyticWithinAt 𝕜 (fun _ => v) s x
· 使用引理 `analyticWithinAt_id`：analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E ->
 E) s z
-/
theorem AnalyticWithinAt.curry_right
    {f : E × F → G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun y ↦ f (p.1, y)) {y | (p.1, y) ∈ s} p.2 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_const analyticWithinAt_id (fun _ hx ↦ hx)

/-- Analytic functions on products are analytic in the first coordinate -/
/-
**AnalyticOnNhd.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.curry_left {f : E × F -> G} {s : Set (E × F)} {y : F} (fa : 
AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (fun x => f (x, y)) {x | (x, y) in s}
参数：E × F；fa : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.curry_left`：AnalyticAt.curry_left {f : E × F -> G} {p : E × F
} (fa : AnalyticAt 𝕜 f p) : AnalyticAt 𝕜 (fun x => f (x, p.2)) p.1

--- 原说明 ---
Analytic functions on products are analytic in the first coordinate
-/
theorem AnalyticOnNhd.curry_left {f : E × F → G} {s : Set (E × F)} {y : F}
    (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun x ↦ f (x, y)) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).curry_left
alias AnalyticOnNhd.along_fst := AnalyticOnNhd.curry_left
/-
**AnalyticOn.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.curry_left {f : E × F -> G} {s : Set (E × F)} {y : F} (fa : Ana
lyticOn 𝕜 f s) : AnalyticOn 𝕜 (fun x => f (x, y)) {x | (x, y) in s}
参数：E × F；fa : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.curry_left`：AnalyticWithinAt.curry_left {f : E × F -> G
} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) : AnalyticWithin
At 𝕜 (fun x => f …
-/
theorem AnalyticOn.curry_left
    {f : E × F → G} {s : Set (E × F)} {y : F} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun x ↦ f (x, y)) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).curry_left

/-- Analytic functions on products are analytic in the second coordinate -/
/-
**AnalyticOnNhd.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.curry_right {f : E × F -> G} {x : E} {s : Set (E × F)} (fa :
 AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (fun y => f (x, y)) {y | (x, y) in s}
参数：E × F；fa : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.curry_right`：AnalyticAt.curry_right {f : E × F -> G} {p : E ×
 F} (fa : AnalyticAt 𝕜 f p) : AnalyticAt 𝕜 (fun y => f (p.1, y)) p.2

--- 原说明 ---
Analytic functions on products are analytic in the second coordinate
-/
theorem AnalyticOnNhd.curry_right {f : E × F → G} {x : E} {s : Set (E × F)}
    (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun y ↦ f (x, y)) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).curry_right
alias AnalyticOnNhd.along_snd := AnalyticOnNhd.curry_right
/-
**AnalyticOn.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.curry_right {f : E × F -> G} {x : E} {s : Set (E × F)} (fa : An
alyticOn 𝕜 f s) : AnalyticOn 𝕜 (fun y => f (x, y)) {y | (x, y) in s}
参数：E × F；fa : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.curry_right`：AnalyticWithinAt.curry_right {f : E × F ->
 G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) : AnalyticWith
inAt 𝕜 (fun y => f…
-/
theorem AnalyticOn.curry_right
    {f : E × F → G} {x : E} {s : Set (E × F)} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun y ↦ f (x, y)) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).curry_right

/-!
### Analyticity in Pi spaces

In this section, `f : Π i, E → Fm i` is a family of functions, i.e., each `f i` is a function,
from `E` to a space `Fm i`. We discuss whether the family as a whole is analytic as a function
of `x : E`, i.e., whether `x ↦ (f 1 x, ..., f n x)` is analytic from `E` to the product space
`Π i, Fm i`. This function is denoted either by `fun x ↦ (fun i ↦ f i x)`, or `fun x i ↦ f i x`,
or `fun x ↦ (f ⬝ x)`. We use the latter spelling in the statements, for readability purposes.
-/

section

variable {ι : Type*} [Fintype ι] {e : E} {Fm : ι → Type*}
    [∀ i, NormedAddCommGroup (Fm i)] [∀ i, NormedSpace 𝕜 (Fm i)]
    {f : Π i, E → Fm i} {s : Set E} {r : ℝ≥0∞}
    {p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)}

/-
**FormalMultilinearSeries.radius_pi_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FormalMultilinearSeries.radius_pi_le (p : Π i, FormalMultilinearSeries 𝕜 E
 (Fm i)) (i : ι) : (FormalMultilinearSeries.pi p).radius <= (p i).radius
参数：p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)；i : ι。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius`：norm_mul_pow_le_of
_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>=0∞)
 < p.radius) : exists C > 0, forall n, ‖p …
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.pi.eq_1`：∀ {𝕜 : Type u} {E : Type v} [inst : Sem
iring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : Top
ologicalSpace E] [ins…
· 使用定理 `ContinuousMultilinearMap.opNorm_pi`：opNorm_pi {ι' : Type v'} [Fintype ι'
] {E' : ι' -> Type wE'} [forall i', SeminormedAddCommGroup (E' i')] [forall i', 
NormedSpace 𝕜 (E' i')] (…
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
lemma FormalMultilinearSeries.radius_pi_le (p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)) (i : ι) :
    (FormalMultilinearSeries.pi p).radius ≤ (p i).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  obtain ⟨C, -, hC⟩ : ∃ C > 0, ∀ n, ‖pi p n‖ * ↑r' ^ n ≤ C := norm_mul_pow_le_of_lt_radius _ hr'
  apply le_radius_of_bound _ C (fun n ↦ ?_)
  apply le_trans _ (hC n)
  gcongr
  rw [pi, ContinuousMultilinearMap.opNorm_pi]
  exact norm_le_pi_norm (fun i ↦ p i n) i
/-
**FormalMultilinearSeries.le_radius_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FormalMultilinearSeries.le_radius_pi (h : forall i, r <= (p i).radius) : r
 <= (FormalMultilinearSeries.pi p).radius
参数：h : forall i, r <= (p i).radius。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius`：norm_mul_pow_le_of
_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>=0∞)
 < p.radius) : exists C > 0, forall n, ‖p …
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `ContinuousMultilinearMap.opNorm_pi`：opNorm_pi {ι' : Type v'} [Fintype ι'
] {E' : ι' -> Type wE'} [forall i', SeminormedAddCommGroup (E' i')] [forall i', 
NormedSpace 𝕜 (E' i')] (…
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 35 条，此处仅展示前 30 条）
-/
lemma FormalMultilinearSeries.le_radius_pi (h : ∀ i, r ≤ (p i).radius) :
    r ≤ (FormalMultilinearSeries.pi p).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  have I i : ∃ C > 0, ∀ n, ‖p i n‖ * (r' : ℝ) ^ n ≤ C :=
    norm_mul_pow_le_of_lt_radius _ (hr'.trans_le (h i))
  choose C C_pos hC using I
  obtain ⟨D, D_nonneg, hD⟩ : ∃ D ≥ 0, ∀ i, C i ≤ D :=
    ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ (C_pos i).le),
      fun i ↦ Finset.single_le_sum (fun j _ ↦ (C_pos j).le) (Finset.mem_univ _)⟩
  apply le_radius_of_bound _ D (fun n ↦ ?_)
  rcases le_or_gt ((r' : ℝ) ^ n) 0 with hr' | hr'
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hr') D_nonneg
  · simp only [pi]
    rw [← le_div_iff₀ hr', ContinuousMultilinearMap.opNorm_pi,
      pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    exact (le_div_iff₀ hr').2 ((hC i n).trans (hD i))
/-
**FormalMultilinearSeries.radius_pi_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FormalMultilinearSeries.radius_pi_eq_iInf : (FormalMultilinearSeries.pi p)
.radius = ⨅ i, (p i).radius
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
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用引理 `FormalMultilinearSeries.le_radius_pi`：FormalMultilinearSeries.le_radius_
pi (h : forall i, r <= (p i).radius) : r <= (FormalMultilinearSeries.pi p).radiu
s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma FormalMultilinearSeries.radius_pi_eq_iInf :
    (FormalMultilinearSeries.pi p).radius = ⨅ i, (p i).radius := by
  refine le_antisymm (by simp [radius_pi_le]) ?_
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  exact le_radius_pi (fun i ↦ le_iInf_iff.1 hr'.le i)

/-- If each function in a finite family has a power series within a ball, then so does the
family as a whole. Note that the positivity assumption on the radius is only needed when
the family is empty. -/
/-
**HasFPowerSeriesWithinOnBall.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.pi (hf : forall i, HasFPowerSeriesWithinOnBall
 (f i) (p i) s e r) (hr : 0 < r) : HasFPowerSeriesWithinOnBall (fun x => (f · x)
) (FormalMultilinearSeries.pi p) s e r where r_le
参数：hf : forall i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r；hr : 0 < r。
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
· 使用引理 `FormalMultilinearSeries.le_radius_pi`：FormalMultilinearSeries.le_radius_
pi (h : forall i, r <= (p i).radius) : r <= (FormalMultilinearSeries.pi p).radiu
s
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.hasSum`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : (x
 : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L :…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If each function in a finite family has a power series within a ball, then so do
es the
family as a whole. Note that the positivity assumption on the radius is only nee
ded when
the family is empty.
-/
lemma HasFPowerSeriesWithinOnBall.pi
    (hf : ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e r where
  r_le := by
    apply FormalMultilinearSeries.le_radius_pi (fun i ↦ ?_)
    exact (hf i).r_le
  r_pos := hr
  hasSum {_} m hy := Pi.hasSum.2 (fun i ↦ (hf i).hasSum m hy)
/-
**hasFPowerSeriesWithinOnBall_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesWithinOnBall_pi_iff (hr : 0 < r) : HasFPowerSeriesWithinOnB
all (fun x => (f · x)) (FormalMultilinearSeries.pi p) s e r ↔ forall i, HasFPowe
rSeriesWithinOnBall (f i) (p i) s e r where mp h i
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `FormalMultilinearSeries.radius_pi_le`：FormalMultilinearSeries.radius_pi_
le (p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)) (i : ι) : (FormalMultilinearSer
ies.pi p).radius <= (p i).…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.hasSum`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : (x
 : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L :…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用引理 `HasFPowerSeriesWithinOnBall.pi`：HasFPowerSeriesWithinOnBall.pi (hf : for
all i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) : HasFPowerSe
riesWithinOnBall (fu…
-/
lemma hasFPowerSeriesWithinOnBall_pi_iff (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e r ↔
      ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r where
  mp h i :=
    ⟨h.r_le.trans (FormalMultilinearSeries.radius_pi_le _ _), hr,
      fun m hy ↦ Pi.hasSum.1 (h.hasSum m hy) i⟩
  mpr h := .pi h hr
/-
**HasFPowerSeriesOnBall.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.pi (hf : forall i, HasFPowerSeriesOnBall (f i) (p i)
 e r) (hr : 0 < r) : HasFPowerSeriesOnBall (fun x => (f · x)) (FormalMultilinear
Series.pi p) e r
参数：hf : forall i, HasFPowerSeriesOnBall (f i) (p i) e r；hr : 0 < r。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.pi`：HasFPowerSeriesWithinOnBall.pi (hf : for
all i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) : HasFPowerSe
riesWithinOnBall (fu…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma HasFPowerSeriesOnBall.pi
    (hf : ∀ i, HasFPowerSeriesOnBall (f i) (p i) e r) (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact HasFPowerSeriesWithinOnBall.pi hf hr
/-
**hasFPowerSeriesOnBall_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOnBall_pi_iff (hr : 0 < r) : HasFPowerSeriesOnBall (fun x =
> (f · x)) (FormalMultilinearSeries.pi p) e r ↔ forall i, HasFPowerSeriesOnBall 
(f i) (p i) e r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `hasFPowerSeriesWithinOnBall_pi_iff`：hasFPowerSeriesWithinOnBall_pi_iff (
hr : 0 < r) : HasFPowerSeriesWithinOnBall (fun x => (f · x)) (FormalMultilinearS
eries.pi p) s e r ↔ fora…
-/
lemma hasFPowerSeriesOnBall_pi_iff (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e r ↔
      ∀ i, HasFPowerSeriesOnBall (f i) (p i) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ]
  exact hasFPowerSeriesWithinOnBall_pi_iff hr
/-
**HasFPowerSeriesWithinAt.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.pi (hf : forall i, HasFPowerSeriesWithinAt (f i) (
p i) s e) : HasFPowerSeriesWithinAt (fun x => (f · x)) (FormalMultilinearSeries.
pi p) s e
参数：hf : forall i, HasFPowerSeriesWithinAt (f i) (p i) s e。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HasFPowerSeriesWithinAt.eventually`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用引理 `HasFPowerSeriesWithinOnBall.pi`：HasFPowerSeriesWithinOnBall.pi (hf : for
all i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) : HasFPowerSe
riesWithinOnBall (fu…
-/
lemma HasFPowerSeriesWithinAt.pi
    (hf : ∀ i, HasFPowerSeriesWithinAt (f i) (p i) s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e := by
  have : ∀ᶠ r in 𝓝[>] 0, ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r :=
    eventually_all.mpr (fun i ↦ (hf i).eventually)
  obtain ⟨r, hr, r_pos⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨r, HasFPowerSeriesWithinOnBall.pi hr r_pos⟩
/-
**hasFPowerSeriesWithinAt_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesWithinAt_pi_iff : HasFPowerSeriesWithinAt (fun x => (f · x)
) (FormalMultilinearSeries.pi p) s e ↔ forall i, HasFPowerSeriesWithinAt (f i) (
p i) s e
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `hasFPowerSeriesWithinOnBall_pi_iff`：hasFPowerSeriesWithinOnBall_pi_iff (
hr : 0 < r) : HasFPowerSeriesWithinOnBall (fun x => (f · x)) (FormalMultilinearS
eries.pi p) s e r ↔ fora…
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用引理 `HasFPowerSeriesWithinAt.pi`：HasFPowerSeriesWithinAt.pi (hf : forall i, H
asFPowerSeriesWithinAt (f i) (p i) s e) : HasFPowerSeriesWithinAt (fun x => (f ·
 x)) (FormalMult…
-/
lemma hasFPowerSeriesWithinAt_pi_iff :
    HasFPowerSeriesWithinAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e ↔
      ∀ i, HasFPowerSeriesWithinAt (f i) (p i) s e := by
  refine ⟨fun h i ↦ ?_, fun h ↦ .pi h⟩
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (hasFPowerSeriesWithinOnBall_pi_iff hr.r_pos).1 hr i⟩
/-
**HasFPowerSeriesAt.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.pi (hf : forall i, HasFPowerSeriesAt (f i) (p i) e) : Ha
sFPowerSeriesAt (fun x => (f · x)) (FormalMultilinearSeries.pi p) e
参数：hf : forall i, HasFPowerSeriesAt (f i) (p i) e。
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
· 使用引理 `HasFPowerSeriesWithinAt.pi`：HasFPowerSeriesWithinAt.pi (hf : forall i, H
asFPowerSeriesWithinAt (f i) (p i) s e) : HasFPowerSeriesWithinAt (fun x => (f ·
 x)) (FormalMult…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma HasFPowerSeriesAt.pi
    (hf : ∀ i, HasFPowerSeriesAt (f i) (p i) e) :
    HasFPowerSeriesAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ] at hf ⊢
  exact HasFPowerSeriesWithinAt.pi hf
/-
**hasFPowerSeriesAt_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_pi_iff : HasFPowerSeriesAt (fun x => (f · x)) (FormalMul
tilinearSeries.pi p) e ↔ forall i, HasFPowerSeriesAt (f i) (p i) e
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `hasFPowerSeriesWithinAt_pi_iff`：hasFPowerSeriesWithinAt_pi_iff : HasFPow
erSeriesWithinAt (fun x => (f · x)) (FormalMultilinearSeries.pi p) s e ↔ forall 
i, HasFPowerSeriesWi…
-/
lemma hasFPowerSeriesAt_pi_iff :
    HasFPowerSeriesAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e ↔
      ∀ i, HasFPowerSeriesAt (f i) (p i) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ]
  exact hasFPowerSeriesWithinAt_pi_iff
/-
**AnalyticWithinAt.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.pi (hf : forall i, AnalyticWithinAt 𝕜 (f i) s e) : Analyt
icWithinAt 𝕜 (fun x => (f · x)) s e
参数：hf : forall i, AnalyticWithinAt 𝕜 (f i) s e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `HasFPowerSeriesWithinAt.pi`：HasFPowerSeriesWithinAt.pi (hf : forall i, H
asFPowerSeriesWithinAt (f i) (p i) s e) : HasFPowerSeriesWithinAt (fun x => (f ·
 x)) (FormalMult…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma AnalyticWithinAt.pi (hf : ∀ i, AnalyticWithinAt 𝕜 (f i) s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f · x)) s e := by
  choose p hp using hf
  exact ⟨FormalMultilinearSeries.pi p, HasFPowerSeriesWithinAt.pi hp⟩
/-
**analyticWithinAt_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_pi_iff : AnalyticWithinAt 𝕜 (fun x => (f · x)) s e ↔ fora
ll i, AnalyticWithinAt 𝕜 (f i) s e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticWithinAt.pi`：AnalyticWithinAt.pi (hf : forall i, AnalyticWithinA
t 𝕜 (f i) s e) : AnalyticWithinAt 𝕜 (fun x => (f · x)) s e
-/
lemma analyticWithinAt_pi_iff :
    AnalyticWithinAt 𝕜 (fun x ↦ (f · x)) s e ↔ ∀ i, AnalyticWithinAt 𝕜 (f i) s e := by
  refine ⟨fun h i ↦ ?_, fun h ↦ .pi h⟩
  exact ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt _).comp_analyticWithinAt h
/-
**AnalyticAt.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.pi (hf : forall i, AnalyticAt 𝕜 (f i) e) : AnalyticAt 𝕜 (fun x 
=> (f · x)) e
参数：hf : forall i, AnalyticAt 𝕜 (f i) e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.pi`：AnalyticWithinAt.pi (hf : forall i, AnalyticWithinA
t 𝕜 (f i) s e) : AnalyticWithinAt 𝕜 (fun x => (f · x)) s e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma AnalyticAt.pi (hf : ∀ i, AnalyticAt 𝕜 (f i) e) :
    AnalyticAt 𝕜 (fun x ↦ (f · x)) e := by
  simp_rw [← analyticWithinAt_univ] at hf ⊢
  exact AnalyticWithinAt.pi hf
/-
**analyticAt_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_pi_iff : AnalyticAt 𝕜 (fun x => (f · x)) e ↔ forall i, Analytic
At 𝕜 (f i) e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `analyticWithinAt_pi_iff`：analyticWithinAt_pi_iff : AnalyticWithinAt 𝕜 (f
un x => (f · x)) s e ↔ forall i, AnalyticWithinAt 𝕜 (f i) s e
-/
lemma analyticAt_pi_iff :
    AnalyticAt 𝕜 (fun x ↦ (f · x)) e ↔ ∀ i, AnalyticAt 𝕜 (f i) e := by
  simp_rw [← analyticWithinAt_univ]
  exact analyticWithinAt_pi_iff
/-
**AnalyticOn.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.pi (hf : forall i, AnalyticOn 𝕜 (f i) s) : AnalyticOn 𝕜 (fun x 
=> (f · x)) s
参数：hf : forall i, AnalyticOn 𝕜 (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.pi`：AnalyticWithinAt.pi (hf : forall i, AnalyticWithinA
t 𝕜 (f i) s e) : AnalyticWithinAt 𝕜 (fun x => (f · x)) s e
-/
lemma AnalyticOn.pi (hf : ∀ i, AnalyticOn 𝕜 (f i) s) :
    AnalyticOn 𝕜 (fun x ↦ (f · x)) s :=
  fun x hx ↦ AnalyticWithinAt.pi (fun i ↦ hf i x hx)
/-
**analyticOn_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_pi_iff : AnalyticOn 𝕜 (fun x => (f · x)) s ↔ forall i, Analytic
On 𝕜 (f i) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `analyticWithinAt_pi_iff`：analyticWithinAt_pi_iff : AnalyticWithinAt 𝕜 (f
un x => (f · x)) s e ↔ forall i, AnalyticWithinAt 𝕜 (f i) s e
· 使用引理 `AnalyticOn.pi`：AnalyticOn.pi (hf : forall i, AnalyticOn 𝕜 (f i) s) : Ana
lyticOn 𝕜 (fun x => (f · x)) s
-/
lemma analyticOn_pi_iff :
    AnalyticOn 𝕜 (fun x ↦ (f · x)) s ↔ ∀ i, AnalyticOn 𝕜 (f i) s :=
  ⟨fun h i x hx ↦ analyticWithinAt_pi_iff.1 (h x hx) i, fun h ↦ .pi h⟩
/-
**AnalyticOnNhd.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.pi (hf : forall i, AnalyticOnNhd 𝕜 (f i) s) : AnalyticOnNhd 
𝕜 (fun x => (f · x)) s
参数：hf : forall i, AnalyticOnNhd 𝕜 (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.pi`：AnalyticAt.pi (hf : forall i, AnalyticAt 𝕜 (f i) e) : Ana
lyticAt 𝕜 (fun x => (f · x)) e
-/
lemma AnalyticOnNhd.pi (hf : ∀ i, AnalyticOnNhd 𝕜 (f i) s) :
    AnalyticOnNhd 𝕜 (fun x ↦ (f · x)) s :=
  fun x hx ↦ AnalyticAt.pi (fun i ↦ hf i x hx)
/-
**analyticOnNhd_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOnNhd_pi_iff : AnalyticOnNhd 𝕜 (fun x => (f · x)) s ↔ forall i, An
alyticOnNhd 𝕜 (f i) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `analyticAt_pi_iff`：analyticAt_pi_iff : AnalyticAt 𝕜 (fun x => (f · x)) e
 ↔ forall i, AnalyticAt 𝕜 (f i) e
· 使用引理 `AnalyticOnNhd.pi`：AnalyticOnNhd.pi (hf : forall i, AnalyticOnNhd 𝕜 (f i)
 s) : AnalyticOnNhd 𝕜 (fun x => (f · x)) s
-/
lemma analyticOnNhd_pi_iff :
    AnalyticOnNhd 𝕜 (fun x ↦ (f · x)) s ↔ ∀ i, AnalyticOnNhd 𝕜 (f i) s :=
  ⟨fun h i x hx ↦ analyticAt_pi_iff.1 (h x hx) i, fun h ↦ .pi h⟩

end

/-!
### Arithmetic on analytic functions
-/

/-- Scalar multiplication is analytic (jointly in both variables). The statement is a little
pedantic to allow towers of field extensions. -/
@[fun_prop]
/-
**analyticAt_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] (z 
: A × E) : AnalyticAt 𝕜 (fun x : A × E => x.1 • x.2) z
参数：z : A × E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.analyticAt_bilinear`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…

--- 原说明 ---
Scalar multiplication is analytic (jointly in both variables). The statement is 
a little
pedantic to allow towers of field extensions.
-/
lemma analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] (z : A × E) :
    AnalyticAt 𝕜 (fun x : A × E ↦ x.1 • x.2) z :=
  (ContinuousLinearMap.lsmul 𝕜 A).analyticAt_bilinear z

/-- Multiplication in a normed algebra over `𝕜` is analytic. -/
@[fun_prop]
/-
**analyticAt_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_mul (z : A × A) : AnalyticAt 𝕜 (fun x : A × A => x.1 * x.2) z
参数：z : A × A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticAt_smul`：analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsSca
larTower 𝕜 A E] (z : A × E) : AnalyticAt 𝕜 (fun x : A × E => x.1 • x.2) z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Multiplication in a normed algebra over `𝕜` is analytic.
-/
lemma analyticAt_mul (z : A × A) : AnalyticAt 𝕜 (fun x : A × A ↦ x.1 * x.2) z :=
  analyticAt_smul z

/-- Scalar multiplication of one analytic function by another. -/
/-
**AnalyticWithinAt.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A 
F] {f : E -> A} {g : E -> F} {s : Set E} {z : E} (hf : AnalyticWithinAt 𝕜 f s z)
 (hg : AnalyticWithinAt 𝕜 g s z) : AnalyticWithinAt 𝕜 (fun x => f x • g x) s z
参数：hf : AnalyticWithinAt 𝕜 f s z；hg : AnalyticWithinAt 𝕜 g s z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp₂_analyticWithinAt`：AnalyticAt.comp₂_analyticWithinAt {h 
: F × G -> H} {f : E -> F} {g : E -> G} {x : E} {s : Set E} (ha : AnalyticAt 𝕜 h
 (f x, g x)) (fa : Anal…
· 使用引理 `analyticAt_smul`：analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsSca
larTower 𝕜 A E] (z : A × E) : AnalyticAt 𝕜 (fun x : A × E => x.1 • x.2) z

--- 原说明 ---
Scalar multiplication of one analytic function by another.
-/
lemma AnalyticWithinAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : E → A} {g : E → F} {s : Set E} {z : E}
    (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x • g x) s z :=
  (analyticAt_smul _).comp₂_analyticWithinAt hf hg

/-- Scalar multiplication of one analytic function by another. -/
@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f 
: E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
 AnalyticAt 𝕜 (f • g) z
参数：hf : AnalyticAt 𝕜 f z；hg : AnalyticAt 𝕜 g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp₂`：AnalyticAt.comp₂ {h : F × G -> H} {f : E -> F} {g : E 
-> G} {x : E} (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x) (ga : Ana
lyticA…
· 使用引理 `analyticAt_smul`：analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsSca
larTower 𝕜 A E] (z : A × E) : AnalyticAt 𝕜 (fun x : A × E => x.1 • x.2) z

--- 原说明 ---
Scalar multiplication of one analytic function by another.
-/
lemma AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f : E → A}
    {g : E → F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (f • g) z :=
  (analyticAt_smul _).comp₂ hf hg

/-- Scalar multiplication of one analytic function by another. -/
/-
**AnalyticOn.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f 
: E -> A} {g : E -> F} {s : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g 
s) : AnalyticOn 𝕜 (fun x => f x • g x) s
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.smul`：AnalyticWithinAt.smul [Module A F] [IsBoundedSMul
 A F] [IsScalarTower 𝕜 A F] {f : E -> A} {g : E -> F} {s : Set E} {z : E} (hf : 
AnalyticWit…

--- 原说明 ---
Scalar multiplication of one analytic function by another.
-/
lemma AnalyticOn.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : E → A} {g : E → F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ f x • g x) s :=
  fun _ m ↦ (hf _ m).smul (hg _ m)

/-- Scalar multiplication of one analytic function by another. -/
/-
**AnalyticOnNhd.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] 
{f : E -> A} {g : E -> F} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticO
nNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (fun x => f x • g x) s
参数：hf : AnalyticOnNhd 𝕜 f s；hg : AnalyticOnNhd 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…

--- 原说明 ---
Scalar multiplication of one analytic function by another.
-/
lemma AnalyticOnNhd.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : E → A} {g : E → F} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x ↦ f x • g x) s :=
  fun _ m ↦ (hf _ m).smul (hg _ m)

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
/-
**AnalyticWithinAt.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z : E} (hf : AnalyticWith
inAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) : AnalyticWithinAt 𝕜 (fun x => f x
 * g x) s z
参数：hf : AnalyticWithinAt 𝕜 f s z；hg : AnalyticWithinAt 𝕜 g s z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp₂_analyticWithinAt`：AnalyticAt.comp₂_analyticWithinAt {h 
: F × G -> H} {f : E -> F} {g : E -> G} {x : E} {s : Set E} (ha : AnalyticAt 𝕜 h
 (f x, g x)) (fa : Anal…
· 使用引理 `analyticAt_mul`：analyticAt_mul (z : A × A) : AnalyticAt 𝕜 (fun x : A × A
 => x.1 * x.2) z

--- 原说明 ---
Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analyti
c.
-/
lemma AnalyticWithinAt.mul {f g : E → A} {s : Set E} {z : E}
    (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x * g x) s z :=
  (analyticAt_mul _).comp₂_analyticWithinAt hf hg

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.mul {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : Analyt
icAt 𝕜 g z) : AnalyticAt 𝕜 (f * g) z
参数：hf : AnalyticAt 𝕜 f z；hg : AnalyticAt 𝕜 g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analyti
c.
-/
lemma AnalyticAt.mul {f g : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (f * g) z :=
  hf.smul hg

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
/-
**AnalyticOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.mul {f g : E -> A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (hg : An
alyticOn 𝕜 g s) : AnalyticOn 𝕜 (fun x => f x * g x) s
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOn.smul`：AnalyticOn.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {s : Set E} (hf : AnalyticOn 𝕜 f s) (h
g : A…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analyti
c.
-/
lemma AnalyticOn.mul {f g : E → A} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ f x * g x) s :=
  hf.smul hg

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
/-
**AnalyticOnNhd.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.mul {f g : E -> A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (h
g : AnalyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (fun x => f x * g x) s
参数：hf : AnalyticOnNhd 𝕜 f s；hg : AnalyticOnNhd 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.smul`：AnalyticOnNhd.smul [Module A F] [IsBoundedSMul A F] 
[IsScalarTower 𝕜 A F] {f : E -> A} {g : E -> F} {s : Set E} (hf : AnalyticOnNhd 
𝕜 f s) (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analyti
c.
-/
lemma AnalyticOnNhd.mul {f g : E → A} {s : Set E}
    (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x ↦ f x * g x) s :=
  hf.smul hg

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
/-
**AnalyticWithinAt.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.pow {f : E -> A} {z : E} {s : Set E} (hf : AnalyticWithin
At 𝕜 f s z) (n : Nat) : AnalyticWithinAt 𝕜 (f ^ n) s z
参数：hf : AnalyticWithinAt 𝕜 f s z；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `analyticWithinAt_const`：analyticWithinAt_const {v : F} {s : Set E} {x : 
E} : AnalyticWithinAt 𝕜 (fun _ => v) s x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `AnalyticWithinAt.mul`：AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z
 : E} (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) : Analytic
WithinAt 𝕜…

--- 原说明 ---
Powers of analytic functions (into a normed `𝕜`-algebra) are analytic.
-/
lemma AnalyticWithinAt.pow {f : E → A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z)
    (n : ℕ) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply analyticWithinAt_const
  | succ m hm =>
    simp only [pow_succ]
    exact hm.mul hf

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : Nat) : An
alyticAt 𝕜 (f ^ n) z
参数：hf : AnalyticAt 𝕜 f z；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用引理 `AnalyticWithinAt.pow`：AnalyticWithinAt.pow {f : E -> A} {z : E} {s : Set
 E} (hf : AnalyticWithinAt 𝕜 f s z) (n : Nat) : AnalyticWithinAt 𝕜 (f ^ n) s z

--- 原说明 ---
Powers of analytic functions (into a normed `𝕜`-algebra) are analytic.
-/
lemma AnalyticAt.pow {f : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 (f ^ n) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
/-
**AnalyticOn.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.pow {f : E -> A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : Nat) 
: AnalyticOn 𝕜 (f ^ n) s
参数：hf : AnalyticOn 𝕜 f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.pow`：AnalyticWithinAt.pow {f : E -> A} {z : E} {s : Set
 E} (hf : AnalyticWithinAt 𝕜 f s z) (n : Nat) : AnalyticWithinAt 𝕜 (f ^ n) s z

--- 原说明 ---
Powers of analytic functions (into a normed `𝕜`-algebra) are analytic.
-/
lemma AnalyticOn.pow {f : E → A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (f ^ n) s :=
  fun _ m ↦ (hf _ m).pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
/-
**AnalyticOnNhd.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.pow {f : E -> A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n :
 Nat) : AnalyticOnNhd 𝕜 (f ^ n) s
参数：hf : AnalyticOnNhd 𝕜 f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z

--- 原说明 ---
Powers of analytic functions (into a normed `𝕜`-algebra) are analytic.
-/
lemma AnalyticOnNhd.pow {f : E → A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (f ^ n) s :=
  fun _ m ↦ (hf _ m).pow n

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/-
**AnalyticWithinAt.zpow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.zpow_nonneg {f : E -> 𝕝} {z : E} {s : Set E} {n : Int} (h
f : AnalyticWithinAt 𝕜 f s z) (hn : 0 <= n) : AnalyticWithinAt 𝕜 (f ^ n) s z
参数：hf : AnalyticWithinAt 𝕜 f s z；hn : 0 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用引理 `AnalyticWithinAt.pow`：AnalyticWithinAt.pow {f : E -> A} {z : E} {s : Set
 E} (hf : AnalyticWithinAt 𝕜 f s z) (n : Nat) : AnalyticWithinAt 𝕜 (f ^ n) s z

--- 原说明 ---
ZPowers of analytic functions (into a normed division algebra over `𝕜`) are anal
ytic if the
exponent is nonnegative.
-/
lemma AnalyticWithinAt.zpow_nonneg {f : E → 𝕝} {z : E} {s : Set E} {n : ℤ}
    (hf : AnalyticWithinAt 𝕜 f s z) (hn : 0 ≤ n) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/-
**AnalyticAt.zpow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n : Int} (hf : AnalyticAt 𝕜 f
 z) (hn : 0 <= n) : AnalyticAt 𝕜 (f ^ n) z
参数：hf : AnalyticAt 𝕜 f z；hn : 0 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z

--- 原说明 ---
ZPowers of analytic functions (into a normed division algebra over `𝕜`) are anal
ytic if the
exponent is nonnegative.
-/
lemma AnalyticAt.zpow_nonneg {f : E → 𝕝} {z : E} {n : ℤ} (hf : AnalyticAt 𝕜 f z) (hn : 0 ≤ n) :
    AnalyticAt 𝕜 (f ^ n) z := by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/-
**AnalyticOn.zpow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.zpow_nonneg {f : E -> 𝕝} {s : Set E} {n : Int} (hf : AnalyticOn
 𝕜 f s) (hn : 0 <= n) : AnalyticOn 𝕜 (f ^ n) s
参数：hf : AnalyticOn 𝕜 f s；hn : 0 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用引理 `AnalyticOn.pow`：AnalyticOn.pow {f : E -> A} {s : Set E} (hf : AnalyticOn
 𝕜 f s) (n : Nat) : AnalyticOn 𝕜 (f ^ n) s

--- 原说明 ---
ZPowers of analytic functions (into a normed division algebra over `𝕜`) are anal
ytic if the
exponent is nonnegative.
-/
lemma AnalyticOn.zpow_nonneg {f : E → 𝕝} {s : Set E} {n : ℤ} (hf : AnalyticOn 𝕜 f s)
    (hn : 0 ≤ n) :
    AnalyticOn 𝕜 (f ^ n) s := by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/-
**AnalyticOnNhd.zpow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.zpow_nonneg {f : E -> 𝕝} {s : Set E} {n : Int} (hf : Analyti
cOnNhd 𝕜 f s) (hn : 0 <= n) : AnalyticOnNhd 𝕜 (f ^ n) s
参数：hf : AnalyticOnNhd 𝕜 f s；hn : 0 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `AnalyticOnNhd.pow`：AnalyticOnNhd.pow {f : E -> A} {s : Set E} (hf : Anal
yticOnNhd 𝕜 f s) (n : Nat) : AnalyticOnNhd 𝕜 (f ^ n) s

--- 原说明 ---
ZPowers of analytic functions (into a normed division algebra over `𝕜`) are anal
ytic if the
exponent is nonnegative.
-/
lemma AnalyticOnNhd.zpow_nonneg {f : E → 𝕝} {s : Set E} {n : ℤ} (hf : AnalyticOnNhd 𝕜 f s)
    (hn : 0 ≤ n) :
    AnalyticOnNhd 𝕜 (f ^ n) s := by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply pow hf

/-!
### Composition with a linear map
-/

section compContinuousLinearMap

variable {u : E →L[𝕜] F} {f : F → G} {pf : FormalMultilinearSeries 𝕜 F G} {s : Set F} {x : E}
  {r : ℝ≥0∞}

/-
**HasFPowerSeriesWithinOnBall.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasFPowerSeriesWithinOnBall.compContinuousLinearMap (hf : HasFPowerSeriesW
ithinOnBall f pf s (u x) r) : HasFPowerSeriesWithinOnBall (f ∘ u) (pf.compContin
uousLinearMap u) (u ⁻¹' s) x (r / ‖u‖ₑ) where r_le
参数：hf : HasFPowerSeriesWithinOnBall f pf s (u x) r。
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
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `FormalMultilinearSeries.div_le_radius_compContinuousLinearMap`：div_le_ra
dius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F
) : p.radius / ‖u‖ₑ <= (p.compContinuousLinearMap u…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 41 条，此处仅展示前 30 条）
-/
theorem HasFPowerSeriesWithinOnBall.compContinuousLinearMap
    (hf : HasFPowerSeriesWithinOnBall f pf s (u x) r) :
    HasFPowerSeriesWithinOnBall (f ∘ u) (pf.compContinuousLinearMap u) (u ⁻¹' s) x (r / ‖u‖ₑ) where
  r_le := by
    calc
      _ ≤ pf.radius / ‖u‖ₑ := by
        gcongr
        exact hf.r_le
      _ ≤ _ := pf.div_le_radius_compContinuousLinearMap _
  r_pos := by
    simp only [ENNReal.div_pos_iff, ne_eq, enorm_ne_top, not_false_eq_true, and_true]
    exact pos_iff_ne_zero.mp hf.r_pos
  hasSum hy1 hy2 := by
    convert! hf.hasSum _ _
    · simp
    · simp only [Set.mem_insert_iff, add_eq_left, Set.mem_preimage, map_add] at hy1 ⊢
      rcases hy1 with (hy1 | hy1) <;> simp [hy1]
    · simp only [Metric.eball, edist_zero_right, Set.mem_ofPred_eq] at hy2 ⊢
      exact lt_of_le_of_lt (ContinuousLinearMap.le_opENorm _ _) (mul_lt_of_lt_div' hy2)
/-
**HasFPowerSeriesOnBall.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.compContinuousLinearMap (hf : HasFPowerSeriesOnBall 
f pf (u x) r) : HasFPowerSeriesOnBall (f ∘ u) (pf.compContinuousLinearMap u) x (
r / ‖u‖ₑ)
参数：hf : HasFPowerSeriesOnBall f pf (u x) r。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.compContinuousLinearMap`：HasFPowerSeriesWith
inOnBall.compContinuousLinearMap (hf : HasFPowerSeriesWithinOnBall f pf s (u x) 
r) : HasFPowerSeriesWithinOnBall (f ∘ u) …
-/
theorem HasFPowerSeriesOnBall.compContinuousLinearMap (hf : HasFPowerSeriesOnBall f pf (u x) r) :
    HasFPowerSeriesOnBall (f ∘ u) (pf.compContinuousLinearMap u) x (r / ‖u‖ₑ) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.compContinuousLinearMap
/-
**HasFPowerSeriesAt.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.compContinuousLinearMap (hf : HasFPowerSeriesAt f pf (u 
x)) : HasFPowerSeriesAt (f ∘ u) (pf.compContinuousLinearMap u) x
参数：hf : HasFPowerSeriesAt f pf (u x)。
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
· 使用定理 `HasFPowerSeriesOnBall.compContinuousLinearMap`：HasFPowerSeriesOnBall.com
pContinuousLinearMap (hf : HasFPowerSeriesOnBall f pf (u x) r) : HasFPowerSeries
OnBall (f ∘ u) (pf.compContinuousLi…
-/
theorem HasFPowerSeriesAt.compContinuousLinearMap (hf : HasFPowerSeriesAt f pf (u x)) :
    HasFPowerSeriesAt (f ∘ u) (pf.compContinuousLinearMap u) x :=
  let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩
/-
**HasFPowerSeriesWithinAt.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.compContinuousLinearMap (hf : HasFPowerSeriesWithi
nAt f pf s (u x)) : HasFPowerSeriesWithinAt (f ∘ u) (pf.compContinuousLinearMap 
u) (u ⁻¹' s) x
参数：hf : HasFPowerSeriesWithinAt f pf s (u x)。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.compContinuousLinearMap`：HasFPowerSeriesWith
inOnBall.compContinuousLinearMap (hf : HasFPowerSeriesWithinOnBall f pf s (u x) 
r) : HasFPowerSeriesWithinOnBall (f ∘ u) …
-/
theorem HasFPowerSeriesWithinAt.compContinuousLinearMap
    (hf : HasFPowerSeriesWithinAt f pf s (u x)) :
    HasFPowerSeriesWithinAt (f ∘ u) (pf.compContinuousLinearMap u) (u ⁻¹' s) x :=
  let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩
/-
**AnalyticAt.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.compContinuousLinearMap (hf : AnalyticAt 𝕜 f (u x)) : AnalyticA
t 𝕜 (f ∘ u) x
参数：hf : AnalyticAt 𝕜 f (u x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.compContinuousLinearMap`：HasFPowerSeriesAt.compContinu
ousLinearMap (hf : HasFPowerSeriesAt f pf (u x)) : HasFPowerSeriesAt (f ∘ u) (pf
.compContinuousLinearMap u) x
-/
theorem AnalyticAt.compContinuousLinearMap (hf : AnalyticAt 𝕜 f (u x)) :
    AnalyticAt 𝕜 (f ∘ u) x :=
  let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩
/-
**AnalyticAtWithin.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAtWithin.compContinuousLinearMap (hf : AnalyticWithinAt 𝕜 f s (u x
)) : AnalyticWithinAt 𝕜 (f ∘ u) (u ⁻¹' s) x
参数：hf : AnalyticWithinAt 𝕜 f s (u x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.compContinuousLinearMap`：HasFPowerSeriesWithinAt
.compContinuousLinearMap (hf : HasFPowerSeriesWithinAt f pf s (u x)) : HasFPower
SeriesWithinAt (f ∘ u) (pf.compContin…
-/
theorem AnalyticAtWithin.compContinuousLinearMap (hf : AnalyticWithinAt 𝕜 f s (u x)) :
    AnalyticWithinAt 𝕜 (f ∘ u) (u ⁻¹' s) x :=
  let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩
/-
**AnalyticOn.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.compContinuousLinearMap (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 
(f ∘ u) (u ⁻¹' s)
参数：hf : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAtWithin.compContinuousLinearMap`：AnalyticAtWithin.compContinuou
sLinearMap (hf : AnalyticWithinAt 𝕜 f s (u x)) : AnalyticWithinAt 𝕜 (f ∘ u) (u ⁻
¹' s) x
-/
theorem AnalyticOn.compContinuousLinearMap (hf : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (f ∘ u) (u ⁻¹' s) := fun x hx =>
  AnalyticAtWithin.compContinuousLinearMap (hf (u x) hx)
/-
**AnalyticOnNhd.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.compContinuousLinearMap (hf : AnalyticOnNhd 𝕜 f s) : Analyti
cOnNhd 𝕜 (f ∘ u) (u ⁻¹' s)
参数：hf : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.compContinuousLinearMap`：AnalyticAt.compContinuousLinearMap (
hf : AnalyticAt 𝕜 f (u x)) : AnalyticAt 𝕜 (f ∘ u) x
-/
theorem AnalyticOnNhd.compContinuousLinearMap (hf : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (f ∘ u) (u ⁻¹' s) := fun x hx =>
  AnalyticAt.compContinuousLinearMap (hf (u x) hx)

end compContinuousLinearMap

/-!
### Restriction of scalars
-/

section

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {f : E → F} {p : FormalMultilinearSeries 𝕜' E F} {x : E} {s : Set E} {r : ℝ≥0∞}

/-
**HasFPowerSeriesWithinOnBall.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.restrictScalars (hf : HasFPowerSeriesWithinOnB
all f p s x r) : HasFPowerSeriesWithinOnBall f (p.restrictScalars 𝕜) s x r
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `FormalMultilinearSeries.radius_le_of_le`：radius_le_of_le {𝕜' E' F' : Typ
e*} [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E'] [No
rmedAddCommGroup F'] [NormedS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
lemma HasFPowerSeriesWithinOnBall.restrictScalars (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    HasFPowerSeriesWithinOnBall f (p.restrictScalars 𝕜) s x r :=
  ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n ↦ by simp)), hf.r_pos, hf.hasSum⟩
/-
**HasFPowerSeriesOnBall.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.restrictScalars (hf : HasFPowerSeriesOnBall f p x r)
 : HasFPowerSeriesOnBall f (p.restrictScalars 𝕜) x r
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用引理 `FormalMultilinearSeries.radius_le_of_le`：radius_le_of_le {𝕜' E' F' : Typ
e*} [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E'] [No
rmedAddCommGroup F'] [NormedS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
lemma HasFPowerSeriesOnBall.restrictScalars (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall f (p.restrictScalars 𝕜) x r :=
  ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n ↦ by simp)), hf.r_pos, hf.hasSum⟩
/-
**HasFPowerSeriesWithinAt.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.restrictScalars (hf : HasFPowerSeriesWithinAt f p 
s x) : HasFPowerSeriesWithinAt f (p.restrictScalars 𝕜) s x
参数：hf : HasFPowerSeriesWithinAt f p s x。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.restrictScalars`：HasFPowerSeriesWithinOnBall
.restrictScalars (hf : HasFPowerSeriesWithinOnBall f p s x r) : HasFPowerSeriesW
ithinOnBall f (p.restrictScalars …
-/
lemma HasFPowerSeriesWithinAt.restrictScalars (hf : HasFPowerSeriesWithinAt f p s x) :
    HasFPowerSeriesWithinAt f (p.restrictScalars 𝕜) s x := by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩
/-
**HasFPowerSeriesAt.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.restrictScalars (hf : HasFPowerSeriesAt f p x) : HasFPow
erSeriesAt f (p.restrictScalars 𝕜) x
参数：hf : HasFPowerSeriesAt f p x。
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
· 使用引理 `HasFPowerSeriesOnBall.restrictScalars`：HasFPowerSeriesOnBall.restrictSca
lars (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesOnBall f (p.restrictS
calars 𝕜) x r
-/
lemma HasFPowerSeriesAt.restrictScalars (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt f (p.restrictScalars 𝕜) x := by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩
/-
**AnalyticWithinAt.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.restrictScalars (hf : AnalyticWithinAt 𝕜' f s x) : Analyt
icWithinAt 𝕜 f s x
参数：hf : AnalyticWithinAt 𝕜' f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `HasFPowerSeriesWithinAt.restrictScalars`：HasFPowerSeriesWithinAt.restric
tScalars (hf : HasFPowerSeriesWithinAt f p s x) : HasFPowerSeriesWithinAt f (p.r
estrictScalars 𝕜) s x
-/
lemma AnalyticWithinAt.restrictScalars (hf : AnalyticWithinAt 𝕜' f s x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩
/-
**AnalyticAt.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.restrictScalars (hf : AnalyticAt 𝕜' f x) : AnalyticAt 𝕜 f x
参数：hf : AnalyticAt 𝕜' f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `HasFPowerSeriesAt.restrictScalars`：HasFPowerSeriesAt.restrictScalars (hf
 : HasFPowerSeriesAt f p x) : HasFPowerSeriesAt f (p.restrictScalars 𝕜) x
-/
lemma AnalyticAt.restrictScalars (hf : AnalyticAt 𝕜' f x) :
    AnalyticAt 𝕜 f x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩
/-
**AnalyticOn.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.restrictScalars (hf : AnalyticOn 𝕜' f s) : AnalyticOn 𝕜 f s
参数：hf : AnalyticOn 𝕜' f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.restrictScalars`：AnalyticWithinAt.restrictScalars (hf :
 AnalyticWithinAt 𝕜' f s x) : AnalyticWithinAt 𝕜 f s x
-/
lemma AnalyticOn.restrictScalars (hf : AnalyticOn 𝕜' f s) :
    AnalyticOn 𝕜 f s :=
  fun x hx ↦ (hf x hx).restrictScalars
/-
**AnalyticOnNhd.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.restrictScalars (hf : AnalyticOnNhd 𝕜' f s) : AnalyticOnNhd 
𝕜 f s
参数：hf : AnalyticOnNhd 𝕜' f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.restrictScalars`：AnalyticAt.restrictScalars (hf : AnalyticAt 
𝕜' f x) : AnalyticAt 𝕜 f x
-/
lemma AnalyticOnNhd.restrictScalars (hf : AnalyticOnNhd 𝕜' f s) :
    AnalyticOnNhd 𝕜 f s :=
  fun x hx ↦ (hf x hx).restrictScalars

end


/-!
### Inversion is analytic
-/

section Geometric
variable (𝕜 A)

/-- The geometric series `1 + x + x ^ 2 + ...` as a `FormalMultilinearSeries`. -/
/-
**formalMultilinearSeries_geometric** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：formalMultilinearSeries_geometric : FormalMultilinearSeries 𝕜 A A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The geometric series `1 + x + x ^ 2 + ...` as a `FormalMultilinearSeries`.
-/
def formalMultilinearSeries_geometric : FormalMultilinearSeries 𝕜 A A :=
  fun n ↦ ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A

/-- The geometric series as an `ofScalars` series. -/
/-
**formalMultilinearSeries_geometric_eq_ofScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：formalMultilinearSeries_geometric_eq_ofScalars : formalMultilinearSeries_g
eometric 𝕜 A = FormalMultilinearSeries.ofScalars A fun _ => (1 : 𝕜)
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The geometric series as an `ofScalars` series.
-/
theorem formalMultilinearSeries_geometric_eq_ofScalars :
    formalMultilinearSeries_geometric 𝕜 A =
      FormalMultilinearSeries.ofScalars A fun _ ↦ (1 : 𝕜) := by
  simp_rw [FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.ofScalars,
    formalMultilinearSeries_geometric, one_smul, implies_true]
/-
**formalMultilinearSeries_geometric_apply_norm_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：formalMultilinearSeries_geometric_apply_norm_le (n : Nat) : ‖formalMultili
nearSeries_geometric 𝕜 A n‖ <= max 1 ‖(1 : A)‖
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_le`：norm_mkPiAlgebraFin_le 
: ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <= max 1 ‖(1 : A)‖
-/
lemma formalMultilinearSeries_geometric_apply_norm_le (n : ℕ) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ ≤ max 1 ‖(1 : A)‖ :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
/-
**formalMultilinearSeries_geometric_apply_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：formalMultilinearSeries_geometric_apply_norm [NormOneClass A] (n : Nat) : 
‖formalMultilinearSeries_geometric 𝕜 A n‖ = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin`：norm_mkPiAlgebraFin [NormO
neClass A] : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ = 1
-/
lemma formalMultilinearSeries_geometric_apply_norm [NormOneClass A] (n : ℕ) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ = 1 :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin
/-
**one_le_formalMultilinearSeries_geometric_radius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_formalMultilinearSeries_geometric_radius : 1 <= (formalMultilinearS
eries_geometric 𝕜 A).radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto`：inv_le_ofSca
lars_radius_of_tendsto {r : Real>=0} (hr : r != 0) (hc : Tendsto (fun n => ‖c n.
succ‖ / ‖c n‖) atTop (𝓝 r)) : ofNNReal r⁻¹ <= (o…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
（共 34 条，此处仅展示前 30 条）
-/
lemma one_le_formalMultilinearSeries_geometric_radius :
    1 ≤ (formalMultilinearSeries_geometric 𝕜 A).radius := by
  convert!
    formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
      FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto A _ one_ne_zero (by simp)
  simp
/-
**formalMultilinearSeries_geometric_radius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：formalMultilinearSeries_geometric_radius [NormOneClass A] : (formalMultili
nearSeries_geometric 𝕜 A).radius = 1
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto`：ofScalars_radius
_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r != 0) (hc : Tendsto (fun n 
=> ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) : (ofSca…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 32 条，此处仅展示前 30 条）
-/
lemma formalMultilinearSeries_geometric_radius [NormOneClass A] :
    (formalMultilinearSeries_geometric 𝕜 A).radius = 1 :=
  formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
    FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)
/-
**hasFPowerSeriesOnBall_inverse_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOnBall_inverse_one_sub [HasSummableGeomSeries A] : HasFPowe
rSeriesOnBall (fun x : A => (1 - x)⁻¹ʳ) (formalMultilinearSeries_geometric 𝕜 A) 
0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_le_formalMultilinearSeries_geometric_radius`：one_le_formalMultilinea
rSeries_geometric_radius : 1 <= (formalMultilinearSeries_geometric 𝕜 A).radius
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `NormedRing.inverse_one_sub`：inverse_one_sub (t : R) (h : ‖t‖ < 1) : inve
rse (1 - t) = ↑(Units.oneSub t h)⁻¹
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
-/
lemma hasFPowerSeriesOnBall_inverse_one_sub [HasSummableGeomSeries A] :
    HasFPowerSeriesOnBall (fun x : A ↦ (1 - x)⁻¹ʳ)
      (formalMultilinearSeries_geometric 𝕜 A) 0 1 := by
  constructor
  · exact one_le_formalMultilinearSeries_geometric_radius 𝕜 A
  · exact one_pos
  · intro y hy
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ofReal_lt_one] at hy
    simp only [zero_add, NormedRing.inverse_one_sub _ hy, Units.oneSub, Units.inv_mk,
      formalMultilinearSeries_geometric, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.ofFn_const, List.prod_replicate]
    exact (summable_geometric_of_norm_lt_one hy).hasSum

@[fun_prop]
/-
**analyticAt_inverse_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_inverse_one_sub [HasSummableGeomSeries A] : AnalyticAt 𝕜 (fun x
 : A => (1 - x)⁻¹ʳ) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasFPowerSeriesOnBall_inverse_one_sub`：hasFPowerSeriesOnBall_inverse_one
_sub [HasSummableGeomSeries A] : HasFPowerSeriesOnBall (fun x : A => (1 - x)⁻¹ʳ)
 (formalMultilinearSeries_g…
-/
lemma analyticAt_inverse_one_sub [HasSummableGeomSeries A] :
    AnalyticAt 𝕜 (fun x : A ↦ (1 - x)⁻¹ʳ) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A⟩⟩

/-- The alternating geometric series `1 - x + x ^ 2 - ...` as a `FormalMultilinearSeries`. -/
/-
**alternatingGeometricSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：alternatingGeometricSeries : FormalMultilinearSeries 𝕜 A A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alternating geometric series `1 - x + x ^ 2 - ...` as a `FormalMultilinearSe
ries`.
-/
def alternatingGeometricSeries : FormalMultilinearSeries 𝕜 A A :=
  .ofScalars A fun n ↦ (-1 : 𝕜) ^ n
/-
**alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg** 是 M
athlib 中的一个引理，位于命名空间 ``。
形式化陈述：alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg :
 alternatingGeometricSeries 𝕜 A = (formalMultilinearSeries_geometric 𝕜 A).compCo
ntinuousLinearMap (-ContinuousLinearMap.id 𝕜 A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `formalMultilinearSeries_geometric_eq_ofScalars`：formalMultilinearSeries_
geometric_eq_ofScalars : formalMultilinearSeries_geometric 𝕜 A = FormalMultiline
arSeries.ofScalars A fun _ => (1 : 𝕜…
· 使用定理 `FormalMultilinearSeries.ofScalars_comp_neg_id`：ofScalars_comp_neg_id : (
ofScalars E c).compContinuousLinearMap (-ContinuousLinearMap.id _ _) = (ofScalar
s E (fun k => (-1) ^ k * c k))
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg :
    alternatingGeometricSeries 𝕜 A =
    (formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap
      (-ContinuousLinearMap.id 𝕜 A) := by
  simp [formalMultilinearSeries_geometric_eq_ofScalars, alternatingGeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
/-
**alternatingGeometricSeries_apply_norm_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：alternatingGeometricSeries_apply_norm_le (n : Nat) : ‖alternatingGeometric
Series 𝕜 A n‖ <= max 1 ‖(1 : A)‖
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_norm_eq_mul`：ofScalars_norm_eq_mul : ‖
ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_le`：norm_mkPiAlgebraFin_le 
: ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <= max 1 ‖(1 : A)‖
-/
lemma alternatingGeometricSeries_apply_norm_le (n : ℕ) :
    ‖alternatingGeometricSeries 𝕜 A n‖ ≤ max 1 ‖(1 : A)‖ := by
  simpa [alternatingGeometricSeries] using
    ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
/-
**alternatingGeometricSeries_apply_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：alternatingGeometricSeries_apply_norm [NormOneClass A] (n : Nat) : ‖altern
atingGeometricSeries 𝕜 A n‖ = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `FormalMultilinearSeries.ofScalars_norm_eq_mul`：ofScalars_norm_eq_mul : ‖
ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin`：norm_mkPiAlgebraFin [NormO
neClass A] : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma alternatingGeometricSeries_apply_norm [NormOneClass A] (n : ℕ) :
    ‖alternatingGeometricSeries 𝕜 A n‖ = 1 := by
  simp [alternatingGeometricSeries]
/-
**one_le_alternatingGeometricSeries_radius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_alternatingGeometricSeries_radius [Nontrivial A] : 1 <= (alternatin
gGeometricSeries 𝕜 A).radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg
`：alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg : alt
ernatingGeometricSeries 𝕜 A = (formalMultilinearSeries_geometr…
· 使用定理 `FormalMultilinearSeries.radius_compNeg`：radius_compNeg [Nontrivial E] (p
 : FormalMultilinearSeries 𝕜 E F) : (p.compContinuousLinearMap (-(.id _ _))).rad
ius = p.radius
· 使用引理 `one_le_formalMultilinearSeries_geometric_radius`：one_le_formalMultilinea
rSeries_geometric_radius : 1 <= (formalMultilinearSeries_geometric 𝕜 A).radius
-/
lemma one_le_alternatingGeometricSeries_radius [Nontrivial A] :
    1 ≤ (alternatingGeometricSeries 𝕜 A).radius := by
  simpa only [FormalMultilinearSeries.radius_compNeg,
    alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
    using one_le_formalMultilinearSeries_geometric_radius 𝕜 A
/-
**alternatingGeometricSeries_radius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：alternatingGeometricSeries_radius [NormOneClass A] : (alternatingGeometric
Series 𝕜 A).radius = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto`：ofScalars_radius
_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r != 0) (hc : Tendsto (fun n 
=> ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) : (ofSca…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma alternatingGeometricSeries_radius [NormOneClass A] :
    (alternatingGeometricSeries 𝕜 A).radius = 1 :=
  FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)
/-
**hasFPowerSeriesOnBall_inverse_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOnBall_inverse_one_add [HasSummableGeomSeries A] [Nontrivia
l A] : HasFPowerSeriesOnBall (fun x : A => Ring.inverse (1 + x)) (alternatingGeo
metricSeries 𝕜 A) 0 1
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg
`：alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg : alt
ernatingGeometricSeries 𝕜 A = (formalMultilinearSeries_geometr…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FunLike.coe_neg`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Neg F] [inst_2 : Neg β]   [IsNegApply F α β] (f : F), ⇑
(-f) …
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `ContinuousLinearMap.norm_id`：norm_id [NontrivialTopology E] : ‖Continuou
sLinearMap.id 𝕜 E‖ = 1
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `HasFPowerSeriesOnBall.compContinuousLinearMap`：HasFPowerSeriesOnBall.com
pContinuousLinearMap (hf : HasFPowerSeriesOnBall f pf (u x) r) : HasFPowerSeries
OnBall (f ∘ u) (pf.compContinuousLi…
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `hasFPowerSeriesOnBall_inverse_one_sub`：hasFPowerSeriesOnBall_inverse_one
_sub [HasSummableGeomSeries A] : HasFPowerSeriesOnBall (fun x : A => (1 - x)⁻¹ʳ)
 (formalMultilinearSeries_g…
-/
lemma hasFPowerSeriesOnBall_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] :
    HasFPowerSeriesOnBall (fun x : A ↦ Ring.inverse (1 + x))
      (alternatingGeometricSeries 𝕜 A) 0 1 := by
  rw [alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
  convert_to HasFPowerSeriesOnBall ((fun x ↦ Ring.inverse (1 - x)) ∘ (-ContinuousLinearMap.id 𝕜 A))
    ((formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap (-ContinuousLinearMap.id 𝕜 A))
    0 1
  · ext; simp
  convert HasFPowerSeriesOnBall.compContinuousLinearMap _ (r := 1)
  · simp [← ofReal_norm]
  · simpa using (hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A)

@[fun_prop]
/-
**analyticAt_inverse_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] : Anal
yticAt 𝕜 (fun x : A => Ring.inverse (1 + x)) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasFPowerSeriesOnBall_inverse_one_add`：hasFPowerSeriesOnBall_inverse_one
_add [HasSummableGeomSeries A] [Nontrivial A] : HasFPowerSeriesOnBall (fun x : A
 => Ring.inverse (1 + x)) (…
-/
lemma analyticAt_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] :
    AnalyticAt 𝕜 (fun x : A ↦ Ring.inverse (1 + x)) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_add 𝕜 A⟩⟩

end Geometric

/-- If `A` is a normed algebra over `𝕜` with summable geometric series, then inversion on `A` is
analytic at any unit. -/
@[fun_prop]
/-
**analyticAt_inverse** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ) : AnalyticAt 𝕜 Ring.
inverse (z : A)
参数：z : Aˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Units.oneSub.congr_simp`：∀ {R : Type u_4} [inst : NormedRing R] [inst_1 
: HasSummableGeomSeries R] (t t_1 : R) (e_t : t = t_1) (h : ‖t‖ < 1),   Units.on
eSub t h = Un…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Units.copy.congr_simp`：∀ {α : Type u} [inst : Monoid α] (u u_1 : αˣ) (e_
u : u = u_1) (val val_1 : α) (e_val : val = val_1) (hv : val = ↑u)   (inv inv_1 
: α) (e_inv…
· 使用定理 `Units.val_inv_copy`：∀ {α : Type u} [inst : Monoid α] (u : αˣ) (val : α) 
(hv : val = ↑u) (inv : α) (hi : inv = ↑u⁻¹),   ↑(u.copy val hv inv hi)⁻¹ = inv
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` is a normed algebra over `𝕜` with summable geometric series, then inversi
on on `A` is
analytic at any unit.
-/
lemma analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ) :
    AnalyticAt 𝕜 Ring.inverse (z : A) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · convert! analyticAt_const (v := (0 : A))
  · let f1 : A → A := fun a ↦ a * z.inv
    let f2 : A → A := fun b ↦ (1 - b)⁻¹ʳ
    let f3 : A → A := fun c ↦ 1 - z.inv * c
    have feq : ∀ᶠ y in 𝓝 (z : A), (f1 ∘ f2 ∘ f3) y = y⁻¹ʳ := by
      have : Metric.ball (z : A) (‖(↑z⁻¹ : A)‖⁻¹) ∈ 𝓝 (z : A) := by
        apply Metric.ball_mem_nhds
        simp
      filter_upwards [this] with y hy
      simp only [Metric.mem_ball, dist_eq_norm] at hy
      have : y = Units.ofNearby z y hy := rfl
      rw [this, Eq.comm]
      simp only [Ring.inverse_unit, Function.comp_apply]
      simp only [Units.ofNearby, Units.add, mul_sub, Units.inv_mul, neg_sub, add_sub_cancel,
        mul_inv_rev, Units.val_mul, Units.val_inv_copy, Units.inv_eq_val_inv, Units.val_copy,
        _root_.sub_sub_cancel, Units.mul_left_inj, f1, f2, f3]
      rw [← Ring.inverse_unit]
      congr
      simp
    apply AnalyticAt.congr _ feq
    apply (analyticAt_id.mul analyticAt_const).comp
    apply AnalyticAt.comp
    · simp only [Units.inv_eq_val_inv, Units.inv_mul, sub_self, f2, f3]
      exact analyticAt_inverse_one_sub 𝕜 A
    · exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
/-
**analyticOnNhd_inverse** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOnNhd_inverse [HasSummableGeomSeries A] : AnalyticOnNhd 𝕜 Ring.inv
erse {x : A | IsUnit x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticAt_inverse`：analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ
) : AnalyticAt 𝕜 Ring.inverse (z : A)
-/
lemma analyticOnNhd_inverse [HasSummableGeomSeries A] :
    AnalyticOnNhd 𝕜 Ring.inverse {x : A | IsUnit x} :=
  fun _ hx ↦ analyticAt_inverse (IsUnit.unit hx)

variable (𝕜 𝕝) in
/-
**hasFPowerSeriesOnBall_inv_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOnBall_inv_one_sub : HasFPowerSeriesOnBall (fun x : 𝕝 => (1
 - x)⁻¹) (formalMultilinearSeries_geometric 𝕜 𝕝) 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用引理 `hasFPowerSeriesOnBall_inverse_one_sub`：hasFPowerSeriesOnBall_inverse_one
_sub [HasSummableGeomSeries A] : HasFPowerSeriesOnBall (fun x : A => (1 - x)⁻¹ʳ)
 (formalMultilinearSeries_g…
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
-/
lemma hasFPowerSeriesOnBall_inv_one_sub :
    HasFPowerSeriesOnBall (fun x : 𝕝 ↦ (1 - x)⁻¹) (formalMultilinearSeries_geometric 𝕜 𝕝) 0 1 := by
  convert! hasFPowerSeriesOnBall_inverse_one_sub 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

variable (𝕝) in
@[fun_prop]
/-
**analyticAt_inv_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_inv_one_sub : AnalyticAt 𝕜 (fun x : 𝕝 => (1 - x)⁻¹) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasFPowerSeriesOnBall_inv_one_sub`：hasFPowerSeriesOnBall_inv_one_sub : H
asFPowerSeriesOnBall (fun x : 𝕝 => (1 - x)⁻¹) (formalMultilinearSeries_geometric
 𝕜 𝕝) 0 1
-/
lemma analyticAt_inv_one_sub : AnalyticAt 𝕜 (fun x : 𝕝 ↦ (1 - x)⁻¹) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_sub 𝕜 𝕝⟩⟩

variable (𝕜 𝕝) in
/-
**hasFPowerSeriesOnBall_inv_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOnBall_inv_one_add : HasFPowerSeriesOnBall (fun x : 𝕝 => (1
 + x)⁻¹) (alternatingGeometricSeries 𝕜 𝕝) 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用引理 `hasFPowerSeriesOnBall_inverse_one_add`：hasFPowerSeriesOnBall_inverse_one
_add [HasSummableGeomSeries A] [Nontrivial A] : HasFPowerSeriesOnBall (fun x : A
 => Ring.inverse (1 + x)) (…
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
lemma hasFPowerSeriesOnBall_inv_one_add :
    HasFPowerSeriesOnBall (fun x : 𝕝 ↦ (1 + x)⁻¹) (alternatingGeometricSeries 𝕜 𝕝) 0 1 := by
  convert! hasFPowerSeriesOnBall_inverse_one_add 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

variable (𝕝) in
@[fun_prop]
/-
**analyticAt_inv_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_inv_one_add : AnalyticAt 𝕜 (fun x : 𝕝 => (1 + x)⁻¹) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasFPowerSeriesOnBall_inv_one_add`：hasFPowerSeriesOnBall_inv_one_add : H
asFPowerSeriesOnBall (fun x : 𝕝 => (1 + x)⁻¹) (alternatingGeometricSeries 𝕜 𝕝) 0
 1
-/
lemma analyticAt_inv_one_add : AnalyticAt 𝕜 (fun x : 𝕝 ↦ (1 + x)⁻¹) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_add 𝕜 𝕝⟩⟩

/-- If `𝕝` is a normed field extension of `𝕜`, then the inverse map `𝕝 → 𝕝` is `𝕜`-analytic
away from 0. -/
@[fun_prop]
/-
**analyticAt_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_inv {z : 𝕝} (hz : z != 0) : AnalyticAt 𝕜 Inv.inv z
参数：hz : z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用引理 `analyticAt_inverse`：analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ
) : AnalyticAt 𝕜 Ring.inverse (z : A)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K

--- 原说明 ---
If `𝕝` is a normed field extension of `𝕜`, then the inverse map `𝕝 → 𝕝` is `𝕜`-a
nalytic
away from 0.
-/
lemma analyticAt_inv {z : 𝕝} (hz : z ≠ 0) : AnalyticAt 𝕜 Inv.inv z := by
  convert! analyticAt_inverse (𝕜 := 𝕜) (Units.mk0 _ hz)
  exact Ring.inverse_eq_inv'.symm

/-- `x⁻¹` is analytic away from zero -/
/-
**analyticOnNhd_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOnNhd_inv : AnalyticOnNhd 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticAt_inv`：analyticAt_inv {z : 𝕝} (hz : z != 0) : AnalyticAt 𝕜 Inv.
inv z

--- 原说明 ---
`x⁻¹` is analytic away from zero
-/
lemma analyticOnNhd_inv : AnalyticOnNhd 𝕜 (fun z ↦ z⁻¹) {z : 𝕝 | z ≠ 0} := by
  intro z m; exact analyticAt_inv m
/-
**analyticOn_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_inv : AnalyticOn 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `analyticOnNhd_inv`：analyticOnNhd_inv : AnalyticOnNhd 𝕜 (fun z => z⁻¹) {z
 : 𝕝 | z != 0}
-/
lemma analyticOn_inv : AnalyticOn 𝕜 (fun z ↦ z⁻¹) {z : 𝕝 | z ≠ 0} :=
  analyticOnNhd_inv.analyticOn

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun]
/-
**AnalyticWithinAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.inv {f : E -> 𝕝} {x : E} {s : Set E} (fa : AnalyticWithin
At 𝕜 f s x) (f0 : f x != 0) : AnalyticWithinAt 𝕜 f⁻¹ s x
参数：fa : AnalyticWithinAt 𝕜 f s x；f0 : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用引理 `analyticAt_inv`：analyticAt_inv {z : 𝕝} (hz : z != 0) : AnalyticAt 𝕜 Inv.
inv z

--- 原说明 ---
`(f x)⁻¹` is analytic away from `f x = 0`
-/
theorem AnalyticWithinAt.inv {f : E → 𝕝} {x : E} {s : Set E} (fa : AnalyticWithinAt 𝕜 f s x)
    (f0 : f x ≠ 0) :
    AnalyticWithinAt 𝕜 f⁻¹ s x :=
  (analyticAt_inv f0).comp_analyticWithinAt fa

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x != 0
) : AnalyticAt 𝕜 f⁻¹ x
参数：fa : AnalyticAt 𝕜 f x；f0 : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `analyticAt_inv`：analyticAt_inv {z : 𝕝} (hz : z != 0) : AnalyticAt 𝕜 Inv.
inv z

--- 原说明 ---
`(f x)⁻¹` is analytic away from `f x = 0`
-/
theorem AnalyticAt.inv {f : E → 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x ≠ 0) :
    AnalyticAt 𝕜 f⁻¹ x :=
  (analyticAt_inv f0).comp fa

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun]
/-
**AnalyticOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.inv {f : E -> 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : fora
ll x in s, f x != 0) : AnalyticOn 𝕜 f⁻¹ s
参数：fa : AnalyticOn 𝕜 f s；f0 : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.inv`：AnalyticWithinAt.inv {f : E -> 𝕝} {x : E} {s : Set
 E} (fa : AnalyticWithinAt 𝕜 f s x) (f0 : f x != 0) : AnalyticWithinAt 𝕜 f⁻¹ s x

--- 原说明 ---
`(f x)⁻¹` is analytic away from `f x = 0`
-/
theorem AnalyticOn.inv {f : E → 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : ∀ x ∈ s, f x ≠ 0) :
    AnalyticOn 𝕜 f⁻¹ s :=
  fun x m ↦ (fa x m).inv (f0 x m)

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun]
/-
**AnalyticOnNhd.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.inv {f : E -> 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s) (f0 
: forall x in s, f x != 0) : AnalyticOnNhd 𝕜 f⁻¹ s
参数：fa : AnalyticOnNhd 𝕜 f s；f0 : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x

--- 原说明 ---
`(f x)⁻¹` is analytic away from `f x = 0`
-/
theorem AnalyticOnNhd.inv {f : E → 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s)
    (f0 : ∀ x ∈ s, f x ≠ 0) :
    AnalyticOnNhd 𝕜 f⁻¹ s :=
  fun x m ↦ (fa x m).inv (f0 x m)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/-
**AnalyticWithinAt.zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.zpow {f : E -> 𝕝} {z : E} {s : Set E} {n : Int} (h₁f : An
alyticWithinAt 𝕜 f s z) (h₂f : f z != 0) : AnalyticWithinAt 𝕜 (f ^ n) s z
参数：h₁f : AnalyticWithinAt 𝕜 f s z；h₂f : f z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.zpow_nonneg`：AnalyticWithinAt.zpow_nonneg {f : E -> 𝕝} 
{z : E} {s : Set E} {n : Int} (hf : AnalyticWithinAt 𝕜 f s z) (hn : 0 <= n) : An
alyticWithinAt 𝕜 (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.eq_neg_comm`：∀ {a b : ℤ}, a = -b ↔ b = -a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `AnalyticWithinAt.inv`：AnalyticWithinAt.inv {f : E -> 𝕝} {x : E} {s : Set
 E} (fa : AnalyticWithinAt 𝕜 f s x) (f0 : f x != 0) : AnalyticWithinAt 𝕜 f⁻¹ s x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away f
rom the zeros.
-/
lemma AnalyticWithinAt.zpow {f : E → 𝕝} {z : E} {s : Set E} {n : ℤ}
    (h₁f : AnalyticWithinAt 𝕜 f s z) (h₂f : f z ≠ 0) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  by_cases hn : 0 ≤ n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/-
**AnalyticAt.zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : AnalyticAt 𝕜 f z) (h
₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z
参数：h₁f : AnalyticAt 𝕜 f z；h₂f : f z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.zpow_nonneg`：AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n :
 Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.eq_neg_comm`：∀ {a b : ℤ}, a = -b ↔ b = -a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away f
rom the zeros.
-/
lemma AnalyticAt.zpow {f : E → 𝕝} {z : E} {n : ℤ} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 (f ^ n) z := by
  by_cases hn : 0 ≤ n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/-
**AnalyticOn.zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.zpow {f : E -> 𝕝} {s : Set E} {n : Int} (h₁f : AnalyticOn 𝕜 f s
) (h₂f : forall z in s, f z != 0) : AnalyticOn 𝕜 (f ^ n) s
参数：h₁f : AnalyticOn 𝕜 f s；h₂f : forall z in s, f z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.zpow`：AnalyticWithinAt.zpow {f : E -> 𝕝} {z : E} {s : S
et E} {n : Int} (h₁f : AnalyticWithinAt 𝕜 f s z) (h₂f : f z != 0) : AnalyticWith
inAt 𝕜 (f ^…

--- 原说明 ---
ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away f
rom the zeros.
-/
lemma AnalyticOn.zpow {f : E → 𝕝} {s : Set E} {n : ℤ} (h₁f : AnalyticOn 𝕜 f s)
    (h₂f : ∀ z ∈ s, f z ≠ 0) :
    AnalyticOn 𝕜 (f ^ n) s :=
  fun z hz ↦ (h₁f z hz).zpow (h₂f z hz)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/-
**AnalyticOnNhd.zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.zpow {f : E -> 𝕝} {s : Set E} {n : Int} (h₁f : AnalyticOnNhd
 𝕜 f s) (h₂f : forall z in s, f z != 0) : AnalyticOnNhd 𝕜 (f ^ n) s
参数：h₁f : AnalyticOnNhd 𝕜 f s；h₂f : forall z in s, f z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.zpow`：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : A
nalyticAt 𝕜 f z) (h₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z

--- 原说明 ---
ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away f
rom the zeros.
-/
lemma AnalyticOnNhd.zpow {f : E → 𝕝} {s : Set E} {n : ℤ} (h₁f : AnalyticOnNhd 𝕜 f s)
    (h₂f : ∀ z ∈ s, f z ≠ 0) :
    AnalyticOnNhd 𝕜 (f ^ n) s :=
  fun z hz ↦ (h₁f z hz).zpow (h₂f z hz)

/-- A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function. -/
/-
**analyticAt_iff_analytic_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_iff_analytic_fun_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScala
rTower 𝕜 𝕝 F] {f : E -> 𝕝} {g : E -> F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : 
f z != 0) : AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (fun z => f z • g z) z
参数：h₁f : AnalyticAt 𝕜 f z；h₂f : f z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `analyticAt_congr`：analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x 
↔ AnalyticAt 𝕜 g x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `compl_singleton_mem_nhds_iff`：compl_singleton_mem_nhds_iff [T1Space X] {
x y : X} : {x}ᶜ in 𝓝 y ↔ y != x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x

--- 原说明 ---
A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function.
-/
theorem analyticAt_iff_analytic_fun_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E → 𝕝} {g : E → F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (fun z ↦ f z • g z) z := by
  constructor
  · exact fun a ↦ h₁f.smul a
  · intro hprod
    rw [analyticAt_congr (g := (f⁻¹ • f) • g), smul_assoc]
    · exact (h₁f.inv h₂f).fun_smul hprod
    · filter_upwards [h₁f.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.2 h₂f)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hy
      simp [hy]

/-- A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function. -/
/-
**analyticAt_iff_analytic_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_iff_analytic_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTow
er 𝕜 𝕝 F] {f : E -> 𝕝} {g : E -> F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z 
!= 0) : AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f • g) z
参数：h₁f : AnalyticAt 𝕜 f z；h₂f : f z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_iff_analytic_fun_smul`：analyticAt_iff_analytic_fun_smul [Modu
le 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F] {f : E -> 𝕝} {g : E -> F} {z :
 E} (h₁f : AnalyticAt …

--- 原说明 ---
A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function.
-/
theorem analyticAt_iff_analytic_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E → 𝕝} {g : E → F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f • g) z :=
  analyticAt_iff_analytic_fun_smul h₁f h₂f

/-- A function is analytic at a point iff it is analytic after multiplication
with a non-vanishing analytic function. -/
@[to_fun analyticAt_iff_analytic_fun_mul]
/-
**analyticAt_iff_analytic_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_iff_analytic_mul {f g : E -> 𝕝} {z : E} (h₁f : AnalyticAt 𝕜 f z
) (h₂f : f z != 0) : AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f * g) z
参数：h₁f : AnalyticAt 𝕜 f z；h₂f : f z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_iff_analytic_smul`：analyticAt_iff_analytic_smul [Module 𝕝 F] 
[IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F] {f : E -> 𝕝} {g : E -> F} {z : E} (h₁f
 : AnalyticAt 𝕜 f …
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
A function is analytic at a point iff it is analytic after multiplication
with a non-vanishing analytic function.
-/
theorem analyticAt_iff_analytic_mul {f g : E → 𝕝} {z : E} (h₁f : AnalyticAt 𝕜 f z)
    (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f * g) z := by
  simp_rw [← smul_eq_mul]
  exact analyticAt_iff_analytic_smul h₁f h₂f

/-- `f x / g x` is analytic away from `g x = 0` -/
/-
**AnalyticWithinAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.div {f g : E -> 𝕝} {s : Set E} {x : E} (fa : AnalyticWith
inAt 𝕜 f s x) (ga : AnalyticWithinAt 𝕜 g s x) (g0 : g x != 0) : AnalyticWithinAt
 𝕜 (fun x => f x / g x) s x
参数：fa : AnalyticWithinAt 𝕜 f s x；ga : AnalyticWithinAt 𝕜 g s x；g0 : g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `AnalyticWithinAt.mul`：AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z
 : E} (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) : Analytic
WithinAt 𝕜…
· 使用定理 `AnalyticWithinAt.inv`：AnalyticWithinAt.inv {f : E -> 𝕝} {x : E} {s : Set
 E} (fa : AnalyticWithinAt 𝕜 f s x) (f0 : f x != 0) : AnalyticWithinAt 𝕜 f⁻¹ s x

--- 原说明 ---
`f x / g x` is analytic away from `g x = 0`
-/
theorem AnalyticWithinAt.div {f g : E → 𝕝} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (ga : AnalyticWithinAt 𝕜 g s x) (g0 : g x ≠ 0) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x / g x) s x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- `f x / g x` is analytic away from `g x = 0` -/
@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.div {f g : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (ga : Analyt
icAt 𝕜 g x) (g0 : g x != 0) : AnalyticAt 𝕜 (f / g) x
参数：fa : AnalyticAt 𝕜 f x；ga : AnalyticAt 𝕜 g x；g0 : g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `AnalyticAt.mul`：AnalyticAt.mul {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜
 f z) (hg : AnalyticAt 𝕜 g z) : AnalyticAt 𝕜 (f * g) z
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x

--- 原说明 ---
`f x / g x` is analytic away from `g x = 0`
-/
theorem AnalyticAt.div {f g : E → 𝕝} {x : E}
    (fa : AnalyticAt 𝕜 f x) (ga : AnalyticAt 𝕜 g x) (g0 : g x ≠ 0) :
    AnalyticAt 𝕜 (f / g) x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- `f x / g x` is analytic away from `g x = 0` -/
/-
**AnalyticOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.div {f g : E -> 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (ga : An
alyticOn 𝕜 g s) (g0 : forall x in s, g x != 0) : AnalyticOn 𝕜 (fun x => f x / g 
x) s
参数：fa : AnalyticOn 𝕜 f s；ga : AnalyticOn 𝕜 g s；g0 : forall x in s, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.div`：AnalyticWithinAt.div {f g : E -> 𝕝} {s : Set E} {x
 : E} (fa : AnalyticWithinAt 𝕜 f s x) (ga : AnalyticWithinAt 𝕜 g s x) (g0 : g x 
!= 0) : An…

--- 原说明 ---
`f x / g x` is analytic away from `g x = 0`
-/
theorem AnalyticOn.div {f g : E → 𝕝} {s : Set E}
    (fa : AnalyticOn 𝕜 f s) (ga : AnalyticOn 𝕜 g s) (g0 : ∀ x ∈ s, g x ≠ 0) :
    AnalyticOn 𝕜 (fun x ↦ f x / g x) s := fun x m ↦
  (fa x m).div (ga x m) (g0 x m)

/-- `f x / g x` is analytic away from `g x = 0` -/
/-
**AnalyticOnNhd.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.div {f g : E -> 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s) (g
a : AnalyticOnNhd 𝕜 g s) (g0 : forall x in s, g x != 0) : AnalyticOnNhd 𝕜 (fun x
 => f x / g x) s
参数：fa : AnalyticOnNhd 𝕜 f s；ga : AnalyticOnNhd 𝕜 g s；g0 : forall x in s, g x != 
0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.div`：AnalyticAt.div {f g : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜
 f x) (ga : AnalyticAt 𝕜 g x) (g0 : g x != 0) : AnalyticAt 𝕜 (f / g) x

--- 原说明 ---
`f x / g x` is analytic away from `g x = 0`
-/
theorem AnalyticOnNhd.div {f g : E → 𝕝} {s : Set E}
    (fa : AnalyticOnNhd 𝕜 f s) (ga : AnalyticOnNhd 𝕜 g s) (g0 : ∀ x ∈ s, g x ≠ 0) :
    AnalyticOnNhd 𝕜 (fun x ↦ f x / g x) s := fun x m ↦
  (fa x m).div (ga x m) (g0 x m)

/-!
### Finite sums and products of analytic functions
-/

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticWithinAt_fun_sum]
/-
**Finset.analyticWithinAt_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticWithinAt_sum {f : α -> E -> F} {c : E} {s : Set E} (N : Fin
set α) (h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c) : AnalyticWithinAt 𝕜 (∑
 n in N, f n) s c
参数：N : Finset α；h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `analyticWithinAt_const`：analyticWithinAt_const {v : F} {s : Set E} {x : 
E} : AnalyticWithinAt 𝕜 (fun _ => v) s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `AnalyticWithinAt.add`：AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s 
x) (hg : AnalyticWithinAt 𝕜 g s x) : AnalyticWithinAt 𝕜 (f + g) s x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Finite sums of analytic functions are analytic
-/
theorem Finset.analyticWithinAt_sum {f : α → E → F} {c : E} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (∑ n ∈ N, f n) s c := by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.sum_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).add (hB fun b m ↦ h b (Or.inr m))

/-- Finite sums of analytic functions are analytic -/
@[to_fun (attr := fun_prop) Finset.analyticAt_fun_sum]
/-
**Finset.analyticAt_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticAt_sum {f : α -> E -> F} {c : E} (N : Finset α) (h : forall
 n in N, AnalyticAt 𝕜 (f n) c) : AnalyticAt 𝕜 (∑ n in N, f n) c
参数：N : Finset α；h : forall n in N, AnalyticAt 𝕜 (f n) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticWithinAt_sum`：Finset.analyticWithinAt_sum {f : α -> E -> 
F} {c : E} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticWithinAt 𝕜 (f 
n) s c) : Analyti…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Finite sums of analytic functions are analytic
-/
theorem Finset.analyticAt_sum {f : α → E → F} {c : E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (∑ n ∈ N, f n) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_sum h

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticOn_fun_sum]
/-
**Finset.analyticOn_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticOn_sum {f : α -> E -> F} {s : Set E} (N : Finset α) (h : fo
rall n in N, AnalyticOn 𝕜 (f n) s) : AnalyticOn 𝕜 (∑ n in N, f n) s
参数：N : Finset α；h : forall n in N, AnalyticOn 𝕜 (f n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticWithinAt_sum`：Finset.analyticWithinAt_sum {f : α -> E -> 
F} {c : E} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticWithinAt 𝕜 (f 
n) s c) : Analyti…

--- 原说明 ---
Finite sums of analytic functions are analytic
-/
theorem Finset.analyticOn_sum {f : α → E → F} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (∑ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticWithinAt_sum (fun n m ↦ h n m z zs)

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticOnNhd_fun_sum]
/-
**Finset.analyticOnNhd_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticOnNhd_sum {f : α -> E -> F} {s : Set E} (N : Finset α) (h :
 forall n in N, AnalyticOnNhd 𝕜 (f n) s) : AnalyticOnNhd 𝕜 (∑ n in N, f n) s
参数：N : Finset α；h : forall n in N, AnalyticOnNhd 𝕜 (f n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticAt_sum`：Finset.analyticAt_sum {f : α -> E -> F} {c : E} (
N : Finset α) (h : forall n in N, AnalyticAt 𝕜 (f n) c) : AnalyticAt 𝕜 (∑ n in N
, f n) c

--- 原说明 ---
Finite sums of analytic functions are analytic
-/
theorem Finset.analyticOnNhd_sum {f : α → E → F} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (∑ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticAt_sum (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
/-
**Finset.analyticWithinAt_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticWithinAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlg
ebra 𝕜 A] {f : α -> E -> A} {c : E} {s : Set E} (N : Finset α) (h : forall n in 
N, AnalyticWithinAt 𝕜 (f n) s c) : AnalyticWithinAt 𝕜 (fun z => ∏ n in N, f n z)
 s c
参数：N : Finset α；h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `analyticWithinAt_const`：analyticWithinAt_const {v : F} {s : Set E} {x : 
E} : AnalyticWithinAt 𝕜 (fun _ => v) s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用引理 `AnalyticWithinAt.mul`：AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z
 : E} (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) : Analytic
WithinAt 𝕜…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticWithinAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s c := by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.prod_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).mul (hB fun b m ↦ h b (Or.inr m))

/-- Finite products of analytic functions are analytic -/
/-
**Finset.analyticWithinAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticWithinAt_prod {A : Type*} [NormedCommRing A] [NormedAlgebra
 𝕜 A] {f : α -> E -> A} {c : E} {s : Set E} (N : Finset α) (h : forall n in N, A
nalyticWithinAt 𝕜 (f n) s c) : AnalyticWithinAt 𝕜 (∏ n in N, f n) s c
参数：N : Finset α；h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.analyticWithinAt_fun_prod`：Finset.analyticWithinAt_fun_prod {A : 
Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} {s : Set
 E} (N : Finset α) (h …

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticWithinAt_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (∏ n ∈ N, f n) s c := by
  convert! N.analyticWithinAt_fun_prod h
  simp

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
/-
**Finset.analyticAt_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜
 A] {f : α -> E -> A} {c : E} (N : Finset α) (h : forall n in N, AnalyticAt 𝕜 (f
 n) c) : AnalyticAt 𝕜 (fun z => ∏ n in N, f n z) c
参数：N : Finset α；h : forall n in N, AnalyticAt 𝕜 (f n) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticWithinAt_fun_prod`：Finset.analyticWithinAt_fun_prod {A : 
Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} {s : Set
 E} (N : Finset α) (h …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (fun z ↦ ∏ n ∈ N, f n z) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_fun_prod h

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
/-
**Finset.analyticAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticAt_prod {α : Type*} {A : Type*} [NormedCommRing A] [NormedA
lgebra 𝕜 A] {f : α -> E -> A} {c : E} (N : Finset α) (h : forall n in N, Analyti
cAt 𝕜 (f n) c) : AnalyticAt 𝕜 (∏ n in N, f n) c
参数：N : Finset α；h : forall n in N, AnalyticAt 𝕜 (f n) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.analyticAt_fun_prod`：Finset.analyticAt_fun_prod {A : Type*} [Norm
edCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} (N : Finset α) (h : 
forall n in N, A…

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticAt_prod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (∏ n ∈ N, f n) c := by
  convert! N.analyticAt_fun_prod h
  simp

/-- Finite products of analytic functions are analytic -/
/-
**Finset.analyticOn_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticOn_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜
 A] {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOn 
𝕜 (f n) s) : AnalyticOn 𝕜 (fun z => ∏ n in N, f n z) s
参数：N : Finset α；h : forall n in N, AnalyticOn 𝕜 (f n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticWithinAt_fun_prod`：Finset.analyticWithinAt_fun_prod {A : 
Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} {s : Set
 E} (N : Finset α) (h …

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticOn_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticWithinAt_fun_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
/-
**Finset.analyticOn_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticOn_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A] 
{f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOn 𝕜 (f
 n) s) : AnalyticOn 𝕜 (∏ n in N, f n) s
参数：N : Finset α；h : forall n in N, AnalyticOn 𝕜 (f n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticWithinAt_prod`：Finset.analyticWithinAt_prod {A : Type*} [
NormedCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} {s : Set E} (N :
 Finset α) (h : fo…

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticOn_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (∏ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticWithinAt_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
/-
**Finset.analyticOnNhd_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticOnNhd_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebr
a 𝕜 A] {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, Analytic
OnNhd 𝕜 (f n) s) : AnalyticOnNhd 𝕜 (fun z => ∏ n in N, f n z) s
参数：N : Finset α；h : forall n in N, AnalyticOnNhd 𝕜 (f n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticAt_fun_prod`：Finset.analyticAt_fun_prod {A : Type*} [Norm
edCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} (N : Finset α) (h : 
forall n in N, A…

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticOnNhd_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticAt_fun_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
/-
**Finset.analyticOnNhd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.analyticOnNhd_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 
A] {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOnNh
d 𝕜 (f n) s) : AnalyticOnNhd 𝕜 (∏ n in N, f n) s
参数：N : Finset α；h : forall n in N, AnalyticOnNhd 𝕜 (f n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.analyticAt_prod`：Finset.analyticAt_prod {α : Type*} {A : Type*} [
NormedCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} (N : Finset α) (
h : forall n…

--- 原说明 ---
Finite products of analytic functions are analytic
-/
theorem Finset.analyticOnNhd_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (∏ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticAt_prod (fun n m ↦ h n m z zs)

/-- Finproducts of analytic functions are analytic -/
@[fun_prop]
/-
**analyticAt_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_finprod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgeb
ra 𝕜 A] {f : α -> E -> A} {c : E} (h : forall a, AnalyticAt 𝕜 (f a) c) : Analyti
cAt 𝕜 (∏ᶠ n, f n) c
参数：h : forall a, AnalyticAt 𝕜 (f a) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x

--- 原说明 ---
Finproducts of analytic functions are analytic
-/
theorem analyticAt_finprod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (h : ∀ a, AnalyticAt 𝕜 (f a) c) :
    AnalyticAt 𝕜 (∏ᶠ n, f n) c := by
  by_cases hf : (Function.mulSupport f).Finite
  · simp_all [finprod_eq_prod _ hf, Finset.analyticAt_prod]
  · rw [finprod_of_infinite_mulSupport hf]
    apply analyticAt_const

/-!
### Unshifting
-/

section

variable {f : E → (E →L[𝕜] F)} {pf : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)} {s : Set E} {x : E}
  {r : ℝ≥0∞} {z : F}

/-
**HasFPowerSeriesWithinOnBall.unshift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.unshift (hf : HasFPowerSeriesWithinOnBall f pf
 s x r) : HasFPowerSeriesWithinOnBall (fun y => z + f y (y - x)) (pf.unshift z) 
s x r where r_le
参数：hf : HasFPowerSeriesWithinOnBall f pf s x r。
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
· 使用定理 `FormalMultilinearSeries.radius_unshift`：radius_unshift (p : FormalMultil
inearSeries 𝕜 E (E ->L[𝕜] F)) (z : F) : (p.unshift z).radius = p.radius
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasSum.zero_add`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : Top
ologicalSpace M] {m : M} [ContinuousAdd M] {f : ℕ → M},   HasSum (fun n => f (n 
+ 1))…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesWithinOnBall.unshift (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (fun y ↦ z + f y (y - x)) (pf.unshift z) s x r where
  r_le := by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy h'y
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    exact (ContinuousLinearMap.apply 𝕜 F y).hasSum (hf.hasSum hy h'y)
/-
**HasFPowerSeriesOnBall.unshift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.unshift (hf : HasFPowerSeriesOnBall f pf x r) : HasF
PowerSeriesOnBall (fun y => z + f y (y - x)) (pf.unshift z) x r where r_le
参数：hf : HasFPowerSeriesOnBall f pf x r。
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
· 使用定理 `FormalMultilinearSeries.radius_unshift`：radius_unshift (p : FormalMultil
inearSeries 𝕜 E (E ->L[𝕜] F)) (z : F) : (p.unshift z).radius = p.radius
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasSum.zero_add`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : Top
ologicalSpace M] {m : M} [ContinuousAdd M] {f : ℕ → M},   HasSum (fun n => f (n 
+ 1))…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.unshift (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (fun y ↦ z + f y (y - x)) (pf.unshift z) x r where
  r_le := by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    exact (ContinuousLinearMap.apply 𝕜 F y).hasSum (hf.hasSum hy)
/-
**HasFPowerSeriesWithinAt.unshift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.unshift (hf : HasFPowerSeriesWithinAt f pf s x) : 
HasFPowerSeriesWithinAt (fun y => z + f y (y - x)) (pf.unshift z) s x
参数：hf : HasFPowerSeriesWithinAt f pf s x。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt`：HasFPowerSeriesWith
inOnBall.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : 
HasFPowerSeriesWithinAt f p s x
· 使用定理 `HasFPowerSeriesWithinOnBall.unshift`：HasFPowerSeriesWithinOnBall.unshift
 (hf : HasFPowerSeriesWithinOnBall f pf s x r) : HasFPowerSeriesWithinOnBall (fu
n y => z + f y (y - x)) (…
-/
theorem HasFPowerSeriesWithinAt.unshift (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (fun y ↦ z + f y (y - x)) (pf.unshift z) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.unshift.hasFPowerSeriesWithinAt

end

