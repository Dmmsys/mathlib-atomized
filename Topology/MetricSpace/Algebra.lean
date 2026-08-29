/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `LipschitzMul`, `LipschitzAdd`,
`IsBoundedSMul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure. The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `ContinuousMul` instance from `LipschitzMul`, etc. In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`IsUniformGroup`) is structured differently.

-/

@[expose] public section

open NNReal Filter Set
open scoped Topology Uniformity

noncomputable section

variable (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

/--
Definition of `LipschitzAdd` / `LipschitzAdd` 的定义

English:
class LipschitzAdd
  parameters: [AddMonoid β]
  axioms and operations (1):
    - lipschitz_add : exists C, LipschitzWith C fun p : β × β => p.1 + p.2

中文:
类 LipschitzAdd
  参数: [AddMonoid β]
  公理与运算 (1 个):
    - lipschitz_add : 存在 C, LipschitzWith C fun p : β × β => p.1 + p.2
-/
class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : exists C, LipschitzWith C fun p : β × β => p.1 + p.2

/-- Class `LipschitzMul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive]
/--
Definition of `LipschitzMul` / `LipschitzMul` 的定义

English:
class LipschitzMul
  parameters: [Monoid β]
  axioms and operations (1):
    - lipschitz_mul : exists C, LipschitzWith C fun p : β × β => p.1 * p.2

中文:
类 LipschitzMul
  参数: [Monoid β]
  公理与运算 (1 个):
    - lipschitz_mul : 存在 C, LipschitzWith C fun p : β × β => p.1 * p.2
-/
class LipschitzMul [Monoid β] : Prop where
  lipschitz_mul : exists C, LipschitzWith C fun p : β × β => p.1 * p.2

variable [Monoid β]

/-- The Lipschitz constant of a monoid `β` satisfying `LipschitzMul` -/
@[to_additive /-- The Lipschitz constant of an `AddMonoid` `β` satisfying `LipschitzAdd` -/]
/--
Definition of `LipschitzMul.C` / `LipschitzMul.C` 的定义

English:
definition LipschitzMul.C
  signature: [_i : LipschitzMul β]
  body: Classical.choose _i.lipschitz_mul

中文:
定义 LipschitzMul.C
  签名: [_i : LipschitzMul β]
  定义体: Classical.choose _i.lipschitz_mul

Depends on / 依赖: Classical, Classical.choose, _i.lipschitz_mul, lipschitz_mul
-/
def LipschitzMul.C [_i : LipschitzMul β] : Real>=0 := Classical.choose _i.lipschitz_mul

variable {β}

@[to_additive]
/--
theorem `lipschitzWith_lipschitz_const_mul_edist` / 定理 `lipschitzWith_lipschitz_const_mul_edist`

English:
theorem lipschitzWith_lipschitz_const_mul_edist
  given: [_i : LipschitzMul β]
  proof: Classical.choose_spec _i.lipschitz_mul

中文:
定理 lipschitzWith_lipschitz_const_mul_edist
  条件: [_i : LipschitzMul β]
  证明: Classical.choose_spec _i.lipschitz_mul

Depends on / 依赖: Classical, Classical.choose_spec, _i.lipschitz_mul, choose_spec, lipschitz_mul
-/
theorem lipschitzWith_lipschitz_const_mul_edist [_i : LipschitzMul β] :
    LipschitzWith (LipschitzMul.C β) fun p : β × β => p.1 * p.2 :=
  Classical.choose_spec _i.lipschitz_mul

variable [LipschitzMul β]

@[to_additive]
/--
theorem `lipschitz_with_lipschitz_const_mul` / 定理 `lipschitz_with_lipschitz_const_mul`

English:
theorem lipschitz_with_lipschitz_const_mul
  proof: by
  rw [← lipschitzWith_iff_dist_le_mul]
  exact lipschitzWith_lipschitz_const_mul_edist

中文:
定理 lipschitz_with_lipschitz_const_mul
  证明: by
  rw [← lipschitzWith_iff_dist_le_mul]
  exact lipschitzWith_lipschitz_const_mul_edist

Depends on / 依赖: lipschitzWith_iff_dist_le_mul, lipschitzWith_lipschitz_const_mul_edist
-/
theorem lipschitz_with_lipschitz_const_mul :
    forall p q : β × β, dist (p.1 * p.2) (q.1 * q.2) <= LipschitzMul.C β * dist p q := by
  rw [← lipschitzWith_iff_dist_le_mul]
  exact lipschitzWith_lipschitz_const_mul_edist

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LipschitzMul.continuousMul : ContinuousMul β :=
  ⟨lipschitzWith_lipschitz_const_mul_edist.continuous⟩

@[to_additive]
/--
Instance `Submonoid.lipschitzMul` / 实例 `Submonoid.lipschitzMul`

English:
instance Submonoid.lipschitzMul
  signature: (s : Submonoid β)
  body: ⟨LipschitzMul.C β, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    convert! lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩

@[to_additive]

中文:
实例 Submonoid.lipschitzMul
  签名: (s : Submonoid β)
  定义体: ⟨LipschitzMul.C β, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    convert! lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩

@[to_additive]

Depends on / 依赖: LipschitzMul, LipschitzMul.C, convert, lipschitzWith_lipschitz_const_mul_edist
-/
instance Submonoid.lipschitzMul (s : Submonoid β) : LipschitzMul s where
  lipschitz_mul := ⟨LipschitzMul.C β, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    convert! lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩

@[to_additive]
/--
Instance `MulOpposite.lipschitzMul` / 实例 `MulOpposite.lipschitzMul`

English:
instance MulOpposite.lipschitzMul
  signature: : LipschitzMul βᵐᵒᵖ where
  body: ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
    (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
      (congr_arg _ <| max_comm _ _)⟩

中文:
实例 MulOpposite.lipschitzMul
  签名: : LipschitzMul βᵐᵒᵖ where
  定义体: ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
    (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
      (congr_arg _ <| max_comm _ _)⟩

Depends on / 依赖: LipschitzMul, LipschitzMul.C
-/
instance MulOpposite.lipschitzMul : LipschitzMul βᵐᵒᵖ where
  lipschitz_mul := ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
    (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
      (congr_arg _ <| max_comm _ _)⟩

-- this instance could be deduced from `NormedAddCommGroup.lipschitzAdd`, but we prove it
-- separately here so that it is available earlier in the hierarchy
/--
Instance `Real.hasLipschitzAdd` / 实例 `Real.hasLipschitzAdd`

English:
instance Real.hasLipschitzAdd
  signature: : LipschitzAdd Real where
  body: ⟨2, LipschitzWith.of_dist_le_mul fun p q => by
    simp only [Real.dist_eq, Prod.dist_eq, NNReal.coe_ofNat,
      add_sub_add_comm, two_mul]
    refine le_trans (abs_add_le (p.1 - q.1) (p.2 - q.2)) ?_
    exact add_le_add (le_max_left _ _) (le_max_right _ _)⟩

中文:
实例 Real.hasLipschitzAdd
  签名: : LipschitzAdd 实数 where
  定义体: ⟨2, LipschitzWith.of_dist_le_mul fun p q => by
    simp only [Real.dist_eq, Prod.dist_eq, NNReal.coe_ofNat,
      add_sub_add_comm, two_mul]
    refine le_trans (abs_add_le (p.1 - q.1) (p.2 - q.2)) ?_
    exact add_le_add (le_max_left _ _) (le_max_right _ _)⟩

Depends on / 依赖: LipschitzWith, LipschitzWith.of_dist_le_mul, NNReal, NNReal.coe_ofNat, Prod.dist_eq, Real.dist_eq, abs_add_le, add_le_add, add_sub_add_comm, coe_ofNat, dist_eq, le_max_left, le_max_right, le_trans, of_dist_le_mul, two_mul
-/
instance Real.hasLipschitzAdd : LipschitzAdd Real where
  lipschitz_add := ⟨2, LipschitzWith.of_dist_le_mul fun p q => by
    simp only [Real.dist_eq, Prod.dist_eq, NNReal.coe_ofNat,
      add_sub_add_comm, two_mul]
    refine le_trans (abs_add_le (p.1 - q.1) (p.2 - q.2)) ?_
    exact add_le_add (le_max_left _ _) (le_max_right _ _)⟩

-- this instance has the same proof as `AddSubmonoid.lipschitzAdd`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
/--
Instance `NNReal.hasLipschitzAdd` / 实例 `NNReal.hasLipschitzAdd`

English:
instance NNReal.hasLipschitzAdd
  signature: : LipschitzAdd Real>=0 where
  body: ⟨LipschitzAdd.C Real, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    exact lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : Real), x₂⟩ ⟨y₁, y₂⟩⟩

中文:
实例 NNReal.hasLipschitzAdd
  签名: : LipschitzAdd 实数>=0 where
  定义体: ⟨LipschitzAdd.C Real, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    exact lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : Real), x₂⟩ ⟨y₁, y₂⟩⟩

Depends on / 依赖: LipschitzAdd, LipschitzAdd.C, lipschitzWith_lipschitz_const_add_edist
-/
instance NNReal.hasLipschitzAdd : LipschitzAdd Real>=0 where
  lipschitz_add := ⟨LipschitzAdd.C Real, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    exact lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : Real), x₂⟩ ⟨y₁, y₂⟩⟩

end LipschitzMul

section IsBoundedSMul

variable [Zero α] [Zero β] [SMul α β]

/--
Definition of `IsBoundedSMul` / `IsBoundedSMul` 的定义

English:
class IsBoundedSMul
  parameters: : Prop where
  axioms and operations (2):
    - dist_smul_pair' : forall x : α, forall y₁ y₂ : β, dist (x • y₁) (x • y₂) <= dist x 0 * dist y₁ y₂
    - dist_pair_smul' : forall x₁ x₂ : α, forall y : β, dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ * dist y 0

中文:
类 IsBoundedSMul
  参数: : 命题 where
  公理与运算 (2 个):
    - dist_smul_pair' : 对任意 x : α, 对任意 y₁ y₂ : β, dist (x • y₁) (x • y₂) <= dist x 0 * dist y₁ y₂
    - dist_pair_smul' : 对任意 x₁ x₂ : α, 对任意 y : β, dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ * dist y 0
-/
class IsBoundedSMul : Prop where
  dist_smul_pair' : forall x : α, forall y₁ y₂ : β, dist (x • y₁) (x • y₂) <= dist x 0 * dist y₁ y₂
  dist_pair_smul' : forall x₁ x₂ : α, forall y : β, dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ * dist y 0

variable {α β}
variable [IsBoundedSMul α β]

/--
theorem `dist_smul_pair` / 定理 `dist_smul_pair`

English:
theorem dist_smul_pair
  given: (x : α) (y₁ y₂ : β)
  statement: dist (x • y₁) (x • y₂) <= dist x 0 * dist y₁ y₂
  proof: IsBoundedSMul.dist_smul_pair' x y₁ y₂

中文:
定理 dist_smul_pair
  条件: (x : α) (y₁ y₂ : β)
  结论: dist (x • y₁) (x • y₂) <= dist x 0 * dist y₁ y₂
  证明: IsBoundedSMul.dist_smul_pair' x y₁ y₂

Depends on / 依赖: IsBoundedSMul, IsBoundedSMul.dist_smul_pair, dist_smul_pair
-/
theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) <= dist x 0 * dist y₁ y₂ :=
  IsBoundedSMul.dist_smul_pair' x y₁ y₂

/--
theorem `dist_pair_smul` / 定理 `dist_pair_smul`

English:
theorem dist_pair_smul
  given: (x₁ x₂ : α) (y : β)
  statement: dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ * dist y 0
  proof: IsBoundedSMul.dist_pair_smul' x₁ x₂ y

中文:
定理 dist_pair_smul
  条件: (x₁ x₂ : α) (y : β)
  结论: dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ * dist y 0
  证明: IsBoundedSMul.dist_pair_smul' x₁ x₂ y

Depends on / 依赖: IsBoundedSMul, IsBoundedSMul.dist_pair_smul, dist_pair_smul
-/
theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ * dist y 0 :=
  IsBoundedSMul.dist_pair_smul' x₁ x₂ y

/--
theorem `Bornology.IsBounded.uniformContinuousOn_smul` / 定理 `Bornology.IsBounded.uniformContinuousOn_smul`

English:
theorem Bornology.IsBounded.uniformContinuousOn_smul
  given: {s : Set (α × β)} (hs : IsBounded s)
  proof: by
  rcases hs.subset_ball_lt 0 0 with ⟨C, hC₀, hC⟩
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  refine ⟨ε / (2 * C), by positivity, fun ⟨a, b⟩ hab ⟨x, y⟩ hxy h => ?_⟩
  grw [hC, Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hab hxy
  rw [Prod.dist_eq]; rw [max_le_iff] at h
  dsimp at hab

中文:
定理 Bornology.IsBounded.uniformContinuousOn_smul
  条件: {s : Set (α × β)} (hs : IsBounded s)
  证明: by
  rcases hs.subset_ball_lt 0 0 with ⟨C, hC₀, hC⟩
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  refine ⟨ε / (2 * C), by positivity, fun ⟨a, b⟩ hab ⟨x, y⟩ hxy h => ?_⟩
  grw [hC, Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hab hxy
  rw [Prod.dist_eq]; rw [max_le_iff] at h
  dsimp at hab

Depends on / 依赖: Metric, Metric.mem_ball, Metric.uniformContinuousOn_iff_le, Prod.dist_eq, dist_eq, dist_pair_smul, dist_smul_pair, dist_triangle, hs.subset_ball_lt, max_le_iff, max_lt_iff, mem_ball, norm_num1, subset_ball_lt, uniformContinuousOn_iff_le
-/
theorem Bornology.IsBounded.uniformContinuousOn_smul {s : Set (α × β)} (hs : IsBounded s) :
    UniformContinuousOn (· • ·).uncurry s := by
  rcases hs.subset_ball_lt 0 0 with ⟨C, hC₀, hC⟩
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  refine ⟨ε / (2 * C), by positivity, fun ⟨a, b⟩ hab ⟨x, y⟩ hxy h => ?_⟩
  grw [hC, Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hab hxy
  rw [Prod.dist_eq]; rw [max_le_iff] at h
  dsimp at hab hxy h ⊢
  grw [dist_triangle _ (a • y), dist_pair_smul, dist_smul_pair, hab.1, hxy.2, h.2, h.1]
  field_simp
  norm_num1

-- see Note [lower instance priority]
/-- The typeclass `IsBoundedSMul` on a metric-space scalar action implies continuity of the
action. -/
instance (priority := 100) IsBoundedSMul.continuousSMul : ContinuousSMul α β where
  continuous_smul := by
    rw [continuous_iff_continuousAt]
    intro x
.uniformContinuousOn_smul refine Metric.isBounded_ball (x := 0) (r := dist x 0 + 1)
.continuousAt ?_ .continuousOn
    exact Metric.isOpen_ball.mem_nhds (by simp)

instance (priority := 100) IsBoundedSMul.toUniformContinuousConstSMul :
    UniformContinuousConstSMul α β :=
  ⟨fun c => ((lipschitzWith_iff_dist_le_mul (K := nndist c 0)).2 fun _ _ =>
    dist_smul_pair c _ _).uniformContinuous⟩

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder` / 定理 `TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder`

English:
theorem TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  have H := hF.prodMk hG
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases (hf x hx).sup (hg x hx) with ⟨C, hC⟩
  simp_rw [Filter.eventually_map, max_le_iff] at hC
  refine Tendsto.comp
    (Metric.isBounded_ball (x := (0 : α × β)) (r := C + 1)).uniformContinuousOn_sm

中文:
定理 TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: by
  have H := hF.prodMk hG
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases (hf x hx).sup (hg x hx) with ⟨C, hC⟩
  simp_rw [Filter.eventually_map, max_le_iff] at hC
  refine Tendsto.comp
    (Metric.isBounded_ball (x := (0 : α × β)) (r := C + 1)).uniformContinuousOn_sm

Depends on / 依赖: Filter, Filter.eventually_map, Metric, Metric.dist_mem_uniformity, Metric.isBounded_ball, Tendsto, Tendsto.comp, dist_mem_uniformity, eventually_map, filter_upwards, hF.prodMk, isBounded_ball, max_le_iff, one_pos, prodMk, simp_rw, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendsto_inf, tendsto_inf.mpr, tendsto_principal
-/
theorem TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι -> X -> α} {G : ι -> X -> β} {f : X -> α} {g : X -> β} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : forall x in s, (𝓝[s] x).IsBoundedUnder (· <= ·) (fun y => dist (f y) 0))
    (hg : forall x in s, (𝓝[s] x).IsBoundedUnder (· <= ·) (fun y => dist (g y) 0)) :
    TendstoLocallyUniformlyOn (F • G) (f • g) l s := by
  have H := hF.prodMk hG
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases (hf x hx).sup (hg x hx) with ⟨C, hC⟩
  simp_rw [Filter.eventually_map, max_le_iff] at hC
  refine Tendsto.comp
    (Metric.isBounded_ball (x := (0 : α × β)) (r := C + 1)).uniformContinuousOn_smul
    (tendsto_inf.mpr ⟨H x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hF x hx (Metric.dist_mem_uniformity one_pos),
    hG x hx (Metric.dist_mem_uniformity one_pos), tendsto_snd hC] with ⟨n, y⟩ hFn hGn hfg
  simp only [mem_prod, Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, sup_lt_iff,
    mem_preimage, mem_ofPred] at hFn hGn hfg ⊢
  grw [dist_triangle_left (F n y) 0 (f y), dist_triangle_left (G n y) 0 (g y)]
  constructor <;> constructor <;> linarith

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder` / 定理 `TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder`

English:
theorem TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder
  statement: {X M ι : Type*} [TopologicalSpace X]
  proof: hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]

中文:
定理 TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder
  结论: {X M ι : 类型} [TopologicalSpace X]
  证明: hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]

Depends on / 依赖: hF.smul
-/
theorem TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {s : Set X} {F : ι -> X -> M} {G : ι -> X -> M} {f : X -> M} {g : X -> M} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : forall x in s, (𝓝[s] x).IsBoundedUnder (· <= ·) (fun y => dist (f y) 0))
    (hg : forall x in s, (𝓝[s] x).IsBoundedUnder (· <= ·) (fun y => dist (g y) 0)) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]
/--
theorem `TendstoLocallyUniformly.smul₀_of_isBoundedUnder` / 定理 `TendstoLocallyUniformly.smul₀_of_isBoundedUnder`

English:
theorem TendstoLocallyUniformly.smul₀_of_isBoundedUnder
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.smul₀_of_isBoundedUnder hG <;> simpa

@[to_fun]

中文:
定理 TendstoLocallyUniformly.smul₀_of_isBoundedUnder
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.smul₀_of_isBoundedUnder hG <;> simpa

@[to_fun]

Depends on / 依赖: hF.smul, tendstoLocallyUniformlyOn_univ
-/
theorem TendstoLocallyUniformly.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
    {F : ι -> X -> α} {G : ι -> X -> β} {f : X -> α} {g : X -> β} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : forall x, (𝓝 x).IsBoundedUnder (· <= ·) (fun y => dist (f y) 0))
    (hg : forall x, (𝓝 x).IsBoundedUnder (· <= ·) (fun y => dist (g y) 0)) :
    TendstoLocallyUniformly (F • G) (f • g) l := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.smul₀_of_isBoundedUnder hG <;> simpa

@[to_fun]
/--
theorem `TendstoLocallyUniformly.mul₀_of_isBoundedUnder` / 定理 `TendstoLocallyUniformly.mul₀_of_isBoundedUnder`

English:
theorem TendstoLocallyUniformly.mul₀_of_isBoundedUnder
  statement: {X M ι : Type*} [TopologicalSpace X]
  proof: hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]

中文:
定理 TendstoLocallyUniformly.mul₀_of_isBoundedUnder
  结论: {X M ι : 类型} [TopologicalSpace X]
  证明: hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]

Depends on / 依赖: hF.smul
-/
theorem TendstoLocallyUniformly.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {F : ι -> X -> M} {G : ι -> X -> M} {f : X -> M} {g : X -> M} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : forall x, (𝓝 x).IsBoundedUnder (· <= ·) (fun y => dist (f y) 0))
    (hg : forall x, (𝓝 x).IsBoundedUnder (· <= ·) (fun y => dist (g y) 0)) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.smul₀` / 定理 `TendstoLocallyUniformlyOn.smul₀`

English:
theorem TendstoLocallyUniformlyOn.smul₀
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: hF.smul₀_of_isBoundedUnder hG
    (fun x hx => ((hfc x hx).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x hx => ((hgc x hx).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]

中文:
定理 TendstoLocallyUniformlyOn.smul₀
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: hF.smul₀_of_isBoundedUnder hG
    (fun x hx => ((hfc x hx).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x hx => ((hgc x hx).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]

Depends on / 依赖: hF.smul, isBoundedUnder_le, tendsto_const_nhds
-/
theorem TendstoLocallyUniformlyOn.smul₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι -> X -> α} {G : ι -> X -> β} {f : X -> α} {g : X -> β} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hfc : ContinuousOn f s) (hgc : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (F • G) (f • g) l s :=
  hF.smul₀_of_isBoundedUnder hG
    (fun x hx => ((hfc x hx).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x hx => ((hgc x hx).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.mul₀` / 定理 `TendstoLocallyUniformlyOn.mul₀`

English:
theorem TendstoLocallyUniformlyOn.mul₀
  statement: {X M ι : Type*} [TopologicalSpace X]
  proof: hF.smul₀ hG hf hg

@[to_fun]

中文:
定理 TendstoLocallyUniformlyOn.mul₀
  结论: {X M ι : 类型} [TopologicalSpace X]
  证明: hF.smul₀ hG hf hg

@[to_fun]

Depends on / 依赖: hF.smul
-/
theorem TendstoLocallyUniformlyOn.mul₀ {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {s : Set X} {F : ι -> X -> M} {G : ι -> X -> M} {f : X -> M} {g : X -> M} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  hF.smul₀ hG hf hg

@[to_fun]
/--
theorem `TendstoLocallyUniformly.smul₀` / 定理 `TendstoLocallyUniformly.smul₀`

English:
theorem TendstoLocallyUniformly.smul₀
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: hF.smul₀_of_isBoundedUnder hG
    (fun x => ((hfc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x => ((hgc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]

中文:
定理 TendstoLocallyUniformly.smul₀
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: hF.smul₀_of_isBoundedUnder hG
    (fun x => ((hfc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x => ((hgc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]

Depends on / 依赖: hF.smul, hfc.tendsto, hgc.tendsto, isBoundedUnder_le, tendsto, tendsto_const_nhds
-/
theorem TendstoLocallyUniformly.smul₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι -> X -> α} {G : ι -> X -> β} {f : X -> α} {g : X -> β} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hfc : Continuous f) (hgc : Continuous g) :
    TendstoLocallyUniformly (F • G) (f • g) l :=
  hF.smul₀_of_isBoundedUnder hG
    (fun x => ((hfc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x => ((hgc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]
/--
theorem `TendstoLocallyUniformly.mul₀` / 定理 `TendstoLocallyUniformly.mul₀`

English:
theorem TendstoLocallyUniformly.mul₀
  statement: {X M ι : Type*} [TopologicalSpace X]
  proof: hF.smul₀ hG hf hg

中文:
定理 TendstoLocallyUniformly.mul₀
  结论: {X M ι : 类型} [TopologicalSpace X]
  证明: hF.smul₀ hG hf hg

Depends on / 依赖: hF.smul
-/
theorem TendstoLocallyUniformly.mul₀ {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {F : ι -> X -> M} {G : ι -> X -> M} {f : X -> M} {g : X -> M} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  hF.smul₀ hG hf hg

-- this instance could be deduced from `NormedSpace.isBoundedSMul`, but we prove it separately
-- here so that it is available earlier in the hierarchy
/--
Instance `Real.isBoundedSMul` / 实例 `Real.isBoundedSMul`

English:
instance Real.isBoundedSMul
  signature: : IsBoundedSMul Real Real where
  body: by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le

中文:
实例 Real.isBoundedSMul
  签名: : IsBoundedSMul 实数 实数 where
  定义体: by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le

Depends on / 依赖: Real.dist_eq, abs_mul, dist_eq, dist_pair_smul, mul_sub, sub_mul
-/
instance Real.isBoundedSMul : IsBoundedSMul Real Real where
  dist_smul_pair' x y₁ y₂ := by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le

/--
Instance `NNReal.isBoundedSMul` / 实例 `NNReal.isBoundedSMul`

English:
instance NNReal.isBoundedSMul
  signature: : IsBoundedSMul Real>=0 Real>=0 where
  body: by convert! dist_smul_pair (x : Real) (y₁ : Real) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert! dist_pair_smul (x₁ : Real) x₂ (y : Real) using 1

中文:
实例 NNReal.isBoundedSMul
  签名: : IsBoundedSMul 实数>=0 实数>=0 where
  定义体: by convert! dist_smul_pair (x : Real) (y₁ : Real) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert! dist_pair_smul (x₁ : Real) x₂ (y : Real) using 1

Depends on / 依赖: convert, dist_pair_smul, dist_smul_pair
-/
instance NNReal.isBoundedSMul : IsBoundedSMul Real>=0 Real>=0 where
  dist_smul_pair' x y₁ y₂ := by convert! dist_smul_pair (x : Real) (y₁ : Real) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert! dist_pair_smul (x₁ : Real) x₂ (y : Real) using 1

/--
Instance `IsBoundedSMul.op` / 实例 `IsBoundedSMul.op`

English:
instance IsBoundedSMul.op
  signature: [SMul αᵐᵒᵖ β] [IsCentralScalar α β]
  body: MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using! dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using! dist_pair_smul x₁ x₂ y

中文:
实例 IsBoundedSMul.op
  签名: [SMul αᵐᵒᵖ β] [IsCentralScalar α β]
  定义体: MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using! dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using! dist_pair_smul x₁ x₂ y

Depends on / 依赖: MulOpposite, MulOpposite.rec, dist_pair_smul, dist_smul_pair, op_smul_eq_smul
-/
instance IsBoundedSMul.op [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : IsBoundedSMul αᵐᵒᵖ β where
  dist_smul_pair' :=
    MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using! dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using! dist_pair_smul x₁ x₂ y

end IsBoundedSMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [LipschitzMul α] : LipschitzAdd (Additive α)
  body: ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩

中文:
实例 [Monoid
  签名: α] [LipschitzMul α] : LipschitzAdd (Additive α)
  定义体: ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩

Depends on / 依赖: LipschitzMul, LipschitzMul.lipschitz_mul, lipschitz_mul
-/
instance [Monoid α] [LipschitzMul α] : LipschitzAdd (Additive α) :=
  ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] [LipschitzAdd α] : LipschitzMul (Multiplicative α)
  body: ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]

中文:
实例 [AddMonoid
  签名: α] [LipschitzAdd α] : LipschitzMul (Multiplicative α)
  定义体: ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]

Depends on / 依赖: LipschitzAdd, LipschitzAdd.lipschitz_add, lipschitz_add
-/
instance [AddMonoid α] [LipschitzAdd α] : LipschitzMul (Multiplicative α) :=
  ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [LipschitzMul α] : LipschitzMul αᵒᵈ
  body: ‹LipschitzMul α›

中文:
实例 [Monoid
  签名: α] [LipschitzMul α] : LipschitzMul αᵒᵈ
  定义体: ‹LipschitzMul α›

Depends on / 依赖: LipschitzMul
-/
instance [Monoid α] [LipschitzMul α] : LipschitzMul αᵒᵈ :=
  ‹LipschitzMul α›

variable {ι : Type*} [Fintype ι]

/--
Instance `Pi.instIsBoundedSMul` / 实例 `Pi.instIsBoundedSMul`

English:
instance Pi.instIsBoundedSMul
  signature: {α : Type*} {β : ι -> Type*} [PseudoMetricSpace α]
  body: (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_smul_pair _ _ _).trans mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_pair_smul _ _ _).trans mul_le_mul_of_nonneg_left (dist_le_pi_dist _ 0 _) dist_no

中文:
实例 Pi.instIsBoundedSMul
  签名: {α : 类型} {β : ι -> 类型} [PseudoMetricSpace α]
  定义体: (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_smul_pair _ _ _).trans mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_pair_smul _ _ _).trans mul_le_mul_of_nonneg_left (dist_le_pi_dist _ 0 _) dist_no

Depends on / 依赖: dist_le_pi_dist, dist_nonneg, dist_pair_smul, dist_pi_le_iff, dist_smul_pair, mul_le_mul_of_nonneg_left
-/
instance Pi.instIsBoundedSMul {α : Type*} {β : ι -> Type*} [PseudoMetricSpace α]
    [forall i, PseudoMetricSpace (β i)] [Zero α] [forall i, Zero (β i)] [forall i, SMul α (β i)]
    [forall i, IsBoundedSMul α (β i)] : IsBoundedSMul α (forall i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_smul_pair _ _ _).trans mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_pair_smul _ _ _).trans mul_le_mul_of_nonneg_left (dist_le_pi_dist _ 0 _) dist_nonneg

/--
Instance `Pi.instIsBoundedSMul'` / 实例 `Pi.instIsBoundedSMul'`

English:
instance Pi.instIsBoundedSMul'
  signature: {α β : ι -> Type*} [forall i, PseudoMetricSpace (α i)]
  body: (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_smul_pair _ _ _).trans
        mul_le_mul (dist_le_pi_dist _ 0 _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_pair_smul _ _ _).trans
        mul_le_mul (dist_le_

中文:
实例 Pi.instIsBoundedSMul'
  签名: {α β : ι -> 类型} [对任意 i, PseudoMetricSpace (α i)]
  定义体: (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_smul_pair _ _ _).trans
        mul_le_mul (dist_le_pi_dist _ 0 _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_pair_smul _ _ _).trans
        mul_le_mul (dist_le_

Depends on / 依赖: dist_le_pi_dist, dist_nonneg, dist_pair_smul, dist_pi_le_iff, dist_smul_pair, mul_le_mul
-/
instance Pi.instIsBoundedSMul' {α β : ι -> Type*} [forall i, PseudoMetricSpace (α i)]
    [forall i, PseudoMetricSpace (β i)] [forall i, Zero (α i)] [forall i, Zero (β i)] [forall i, SMul (α i) (β i)]
    [forall i, IsBoundedSMul (α i) (β i)] : IsBoundedSMul (forall i, α i) (forall i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_smul_pair _ _ _).trans
        mul_le_mul (dist_le_pi_dist _ 0 _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ =>
(dist_pair_smul _ _ _).trans
        mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ 0 _) dist_nonneg dist_nonneg

/--
Instance `Prod.instIsBoundedSMul` / 实例 `Prod.instIsBoundedSMul`

English:
instance Prod.instIsBoundedSMul
  signature: {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
  body: max_le ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' _x₁ _x₂ _y :=
    max_le ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_

中文:
实例 Prod.instIsBoundedSMul
  签名: {α β γ : 类型} [PseudoMetricSpace α] [PseudoMetricSpace β]
  定义体: max_le ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' _x₁ _x₂ _y :=
    max_le ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_

Depends on / 依赖: dist_nonneg, dist_pair_smul, dist_smul_pair, le_max_left, le_max_right, max_le, mul_le_mul_of_nonneg_left
-/
instance Prod.instIsBoundedSMul {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] [Zero α] [Zero β] [Zero γ] [SMul α β] [SMul α γ] [IsBoundedSMul α β]
    [IsBoundedSMul α γ] : IsBoundedSMul α (β × γ) where
  dist_smul_pair' _x _y₁ _y₂ :=
    max_le ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' _x₁ _x₂ _y :=
    max_le ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)

instance {α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β] [Zero α] [Zero β] [SMul α β] [IsBoundedSMul α β] :
    IsBoundedSMul α (SeparationQuotient β) where
dist_smul_pair' _ := Quotient.ind₂ dist_smul_pair _
dist_pair_smul' _ _ := Quotient.ind dist_pair_smul _ _

-- We don't have the `SMul α γ → SMul β δ → SMul (α × β) (γ × δ)` instance, but if we did, then
-- `IsBoundedSMul α γ → IsBoundedSMul β δ → IsBoundedSMul (α × β) (γ × δ)` would hold
