/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Dilation

/-!
# Normed rings

In this file we continue building the theory of (semi)normed rings.
-/

@[expose] public section

variable {α : Type*} {β : Type*} {ι : Type*}

open Filter Bornology
open scoped Topology NNReal Pointwise

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

/--
theorem `Filter.Tendsto.zero_mul_isBoundedUnder_le` / 定理 `Filter.Tendsto.zero_mul_isBoundedUnder_le`

English:
theorem Filter.Tendsto.zero_mul_isBoundedUnder_le
  statement: {f g : ι -> α} {l : Filter ι}
  proof: hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le

中文:
定理 滤子.收敛.zero_mul_isBoundedUnder_le
  结论: {f g : ι -> α} {l : 滤子 ι}
  证明: hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le

Depends on / 依赖: hf.op_zero_isBoundedUnder_le, norm_mul_le, op_zero_isBoundedUnder_le
-/
theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι -> α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· <= ·) l ((‖·‖) ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le

/--
theorem `Filter.isBoundedUnder_le_mul_tendsto_zero` / 定理 `Filter.isBoundedUnder_le_mul_tendsto_zero`

English:
theorem Filter.isBoundedUnder_le_mul_tendsto_zero
  statement: {f g : ι -> α} {l : Filter ι}
  proof: hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

中文:
定理 滤子.isBoundedUnder_le_mul_tendsto_zero
  结论: {f g : ι -> α} {l : 滤子 ι}
  证明: hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

Depends on / 依赖: hg.op_zero_isBoundedUnder_le, mul_comm, norm_mul_le, op_zero_isBoundedUnder_le, trans_eq
-/
theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι -> α} {l : Filter ι}
    (hf : IsBoundedUnder (· <= ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

open Finset in
/--
Instance `Pi.nonUnitalSeminormedRing` / 实例 `Pi.nonUnitalSeminormedRing`

English:
instance Pi.nonUnitalSeminormedRing
  signature: {R : ι -> Type*} [Fintype ι]
  body: { seminormedAddCommGroup, nonUnitalRing with
norm_mul_le x y := NNReal.coe_mono calc
      (univ.sup fun i => ‖x i * y i‖₊) <= univ.sup ((‖x ·‖₊) * (‖y ·‖₊)) :=
        sup_mono_fun fun _ _ => nnnorm_mul_le _ _
      _ <= (univ.sup (‖x ·‖₊)) * univ.sup (‖y ·‖₊) :=
        sup_mul_le_mul_sup_of_nonneg (fun _ _ => zero_le) fun _ _ => zero_le }

中文:
实例 依赖函数类型.nonUnitalSeminormedRing
  签名: {R : ι -> 类型} [有限类型 ι]
  定义体: { seminormedAddCommGroup, nonUnitalRing with
norm_mul_le x y := NNReal.coe_mono calc
      (univ.sup fun i => ‖x i * y i‖₊) <= univ.sup ((‖x ·‖₊) * (‖y ·‖₊)) :=
        sup_mono_fun fun _ _ => nnnorm_mul_le _ _
      _ <= (univ.sup (‖x ·‖₊)) * univ.sup (‖y ·‖₊) :=
        sup_mul_le_mul_sup_of_nonneg (fun _ _ => zero_le) fun _ _ => zero_le }

Depends on / 依赖: NNReal, NNReal.coe_mono, coe_mono, nnnorm_mul_le, nonUnitalRing, norm_mul_le, seminormedAddCommGroup, sup_mono_fun, sup_mul_le_mul_sup_of_nonneg, univ.sup, zero_le
-/
instance Pi.nonUnitalSeminormedRing {R : ι -> Type*} [Fintype ι]
    [forall i, NonUnitalSeminormedRing (R i)] : NonUnitalSeminormedRing (forall i, R i) :=
  { seminormedAddCommGroup, nonUnitalRing with
norm_mul_le x y := NNReal.coe_mono calc
      (univ.sup fun i => ‖x i * y i‖₊) <= univ.sup ((‖x ·‖₊) * (‖y ·‖₊)) :=
        sup_mono_fun fun _ _ => nnnorm_mul_le _ _
      _ <= (univ.sup (‖x ·‖₊)) * univ.sup (‖y ·‖₊) :=
        sup_mul_le_mul_sup_of_nonneg (fun _ _ => zero_le) fun _ _ => zero_le }

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/--
Instance `Pi.seminormedRing` / 实例 `Pi.seminormedRing`

English:
instance Pi.seminormedRing
  signature: {R : ι -> Type*} [Fintype ι] [forall i, SeminormedRing (R i)]
  body: { Pi.nonUnitalSeminormedRing, Pi.ring with }

中文:
实例 依赖函数类型.seminormedRing
  签名: {R : ι -> 类型} [有限类型 ι] [对任意 i, Seminormed环 (R i)]
  定义体: { Pi.nonUnitalSeminormedRing, Pi.ring with }

Depends on / 依赖: Pi.nonUnitalSeminormedRing, Pi.ring, nonUnitalSeminormedRing
-/
instance Pi.seminormedRing {R : ι -> Type*} [Fintype ι] [forall i, SeminormedRing (R i)] :
    SeminormedRing (forall i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.ring with }

/--
lemma `RingHom.isometry` / 引理 `RingHom.isometry`

English:
lemma RingHom.isometry
  statement: {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
  proof: AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map

中文:
引理 环态射.isometry
  结论: {𝕜₁ 𝕜₂ : 类型} [Seminormed环 𝕜₁] [Seminormed环 𝕜₂]
  证明: AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, RingHomIsometric, RingHomIsometric.norm_map, isometry_of_norm, norm_map
-/
lemma RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ ->+* 𝕜₂) [RingHomIsometric σ] :
    Isometry σ := AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map

/--
lemma `RingHomIsometric.inv` / 引理 `RingHomIsometric.inv`

English:
lemma RingHomIsometric.inv
  statement: {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
  proof: ⟨fun {x} => by rw [← RingHomIsometric.norm_map (σ := σ), RingHomInvPair.comp_apply_eq₂]⟩

中文:
引理 RingHomIsometric.inv
  结论: {𝕜₁ 𝕜₂ : 类型} [Seminormed环 𝕜₁] [Seminormed环 𝕜₂]
  证明: ⟨fun {x} => by rw [← RingHomIsometric.norm_map (σ := σ), RingHomInvPair.comp_apply_eq₂]⟩

Depends on / 依赖: RingHomInvPair, RingHomInvPair.comp_apply_eq, RingHomIsometric, RingHomIsometric.norm_map, norm_map
-/
lemma RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ ->+* 𝕜₂) {σ' : 𝕜₂ ->+* 𝕜₁} [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    RingHomIsometric σ' :=
  ⟨fun {x} => by rw [← RingHomIsometric.norm_map (σ := σ), RingHomInvPair.comp_apply_eq₂]⟩

/--
lemma `tendsto_pow_cobounded_cobounded` / 引理 `tendsto_pow_cobounded_cobounded`

English:
lemma tendsto_pow_cobounded_cobounded
  proof: by
  simpa [← tendsto_norm_atTop_iff_cobounded] using!
    (tendsto_pow_atTop hm).comp (tendsto_norm_cobounded_atTop (E := α))

中文:
引理 tendsto_pow_cobounded_cobounded
  证明: by
  simpa [← tendsto_norm_atTop_iff_cobounded] using!
    (tendsto_pow_atTop hm).comp (tendsto_norm_cobounded_atTop (E := α))

Depends on / 依赖: tendsto_norm_atTop_iff_cobounded, tendsto_norm_cobounded_atTop, tendsto_pow_atTop
-/
lemma tendsto_pow_cobounded_cobounded
    [NormOneClass α] [NormMulClass α] {m : Nat} (hm : m != 0) :
    Tendsto (· ^ m) (cobounded α) (cobounded α) := by
  simpa [← tendsto_norm_atTop_iff_cobounded] using!
    (tendsto_pow_atTop hm).comp (tendsto_norm_cobounded_atTop (E := α))

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

/--
Instance `Pi.nonUnitalNormedRing` / 实例 `Pi.nonUnitalNormedRing`

English:
instance Pi.nonUnitalNormedRing
  signature: {R : ι -> Type*} [Fintype ι] [forall i, NonUnitalNormedRing (R i)]
  body: { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

中文:
实例 依赖函数类型.nonUnitalNormedRing
  签名: {R : ι -> 类型} [有限类型 ι] [对任意 i, 非幺赋范环 (R i)]
  定义体: { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

Depends on / 依赖: Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup, nonUnitalSeminormedRing, normedAddCommGroup
-/
instance Pi.nonUnitalNormedRing {R : ι -> Type*} [Fintype ι] [forall i, NonUnitalNormedRing (R i)] :
    NonUnitalNormedRing (forall i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/--
Instance `Pi.normedRing` / 实例 `Pi.normedRing`

English:
instance Pi.normedRing
  signature: {R : ι -> Type*} [Fintype ι] [forall i, NormedRing (R i)]
  body: { Pi.seminormedRing, Pi.normedAddCommGroup with }

中文:
实例 依赖函数类型.normedRing
  签名: {R : ι -> 类型} [有限类型 ι] [对任意 i, 赋范环 (R i)]
  定义体: { Pi.seminormedRing, Pi.normedAddCommGroup with }

Depends on / 依赖: Pi.normedAddCommGroup, Pi.seminormedRing, normedAddCommGroup, seminormedRing
-/
instance Pi.normedRing {R : ι -> Type*} [Fintype ι] [forall i, NormedRing (R i)] :
    NormedRing (forall i, R i) :=
  { Pi.seminormedRing, Pi.normedAddCommGroup with }

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

/--
Instance `Pi.nonUnitalSeminormedCommRing` / 实例 `Pi.nonUnitalSeminormedCommRing`

English:
instance Pi.nonUnitalSeminormedCommRing
  signature: {R : ι -> Type*} [Fintype ι]
  body: { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

中文:
实例 依赖函数类型.nonUnitalSeminormedCommRing
  签名: {R : ι -> 类型} [有限类型 ι]
  定义体: { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

Depends on / 依赖: Pi.nonUnitalCommRing, Pi.nonUnitalSeminormedRing, nonUnitalCommRing, nonUnitalSeminormedRing
-/
instance Pi.nonUnitalSeminormedCommRing {R : ι -> Type*} [Fintype ι]
    [forall i, NonUnitalSeminormedCommRing (R i)] : NonUnitalSeminormedCommRing (forall i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/--
Instance `Pi.nonUnitalNormedCommRing` / 实例 `Pi.nonUnitalNormedCommRing`

English:
instance Pi.nonUnitalNormedCommRing
  signature: {R : ι -> Type*} [Fintype ι]
  body: { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

中文:
实例 依赖函数类型.nonUnitalNormedCommRing
  签名: {R : ι -> 类型} [有限类型 ι]
  定义体: { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

Depends on / 依赖: Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup, nonUnitalSeminormedCommRing, normedAddCommGroup
-/
instance Pi.nonUnitalNormedCommRing {R : ι -> Type*} [Fintype ι]
    [forall i, NonUnitalNormedCommRing (R i)] : NonUnitalNormedCommRing (forall i, R i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

/--
Instance `Pi.seminormedCommRing` / 实例 `Pi.seminormedCommRing`

English:
instance Pi.seminormedCommRing
  signature: {R : ι -> Type*} [Fintype ι] [forall i, SeminormedCommRing (R i)]
  body: { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

中文:
实例 依赖函数类型.seminormedCommRing
  签名: {R : ι -> 类型} [有限类型 ι] [对任意 i, SeminormedComm环 (R i)]
  定义体: { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

Depends on / 依赖: Pi.nonUnitalSeminormedCommRing, Pi.ring, nonUnitalSeminormedCommRing
-/
instance Pi.seminormedCommRing {R : ι -> Type*} [Fintype ι] [forall i, SeminormedCommRing (R i)] :
    SeminormedCommRing (forall i, R i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

end SeminormedCommRing

section NormedCommRing

variable [NormedCommRing α]

/--
Instance `Pi.normedCommutativeRing` / 实例 `Pi.normedCommutativeRing`

English:
instance Pi.normedCommutativeRing
  signature: {R : ι -> Type*} [Fintype ι] [forall i, NormedCommRing (R i)]
  body: { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

中文:
实例 依赖函数类型.normedCommutativeRing
  签名: {R : ι -> 类型} [有限类型 ι] [对任意 i, NormedComm环 (R i)]
  定义体: { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

Depends on / 依赖: Pi.normedAddCommGroup, Pi.seminormedCommRing, normedAddCommGroup, seminormedCommRing
-/
instance Pi.normedCommutativeRing {R : ι -> Type*} [Fintype ι] [forall i, NormedCommRing (R i)] :
    NormedCommRing (forall i, R i) :=
  { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

end NormedCommRing

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedRing.toContinuousMul [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
tendsto_iff_norm_sub_tendsto_zero.2 by
        have : forall e : α × α,
            ‖e.1 * e.2 - x.1 * x.2‖ <= ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ <= ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [mul_sub]; rw [sub_mul]; rw [sub_add_sub_cancel]
            _ <= ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine squeeze_zero (fun e => norm_nonneg _) this ?_
        convert!
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul tendsto_const_nhds)
        simp⟩

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) NonUnitalSeminormedRing.toIsTopologicalRing [NonUnitalSeminormedRing α] :
    IsTopologicalRing α where

namespace SeparationQuotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSeminormedRing
  signature: α] : NonUnitalNormedRing (SeparationQuotient α) where
  body: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

中文:
实例 [非幺Seminormed环
  签名: α] : 非幺赋范环 (SeparationQuotient α) where
  定义体: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
-/
instance [NonUnitalSeminormedRing α] : NonUnitalNormedRing (SeparationQuotient α) where
  __ : NonUnitalRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSeminormedCommRing
  signature: α] : NonUnitalNormedCommRing (SeparationQuotient α) where
  body: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

中文:
实例 [非幺SeminormedComm环
  签名: α] : 非幺NormedComm环 (SeparationQuotient α) where
  定义体: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
-/
instance [NonUnitalSeminormedCommRing α] : NonUnitalNormedCommRing (SeparationQuotient α) where
  __ : NonUnitalCommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedRing
  signature: α] : NormedRing (SeparationQuotient α) where
  body: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

中文:
实例 [Seminormed环
  签名: α] : 赋范环 (SeparationQuotient α) where
  定义体: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
-/
instance [SeminormedRing α] : NormedRing (SeparationQuotient α) where
  __ : Ring (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedCommRing
  signature: α] : NormedCommRing (SeparationQuotient α) where
  body: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

中文:
实例 [SeminormedComm环
  签名: α] : NormedComm环 (SeparationQuotient α) where
  定义体: inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
-/
instance [SeminormedCommRing α] : NormedCommRing (SeparationQuotient α) where
  __ : CommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedAddCommGroup
  signature: α] [One α] [NormOneClass α] :
  body: norm_one (α := α)

中文:
实例 [SeminormedAddComm群
  签名: α] [幺 α] [NormOne类 α] :
  定义体: norm_one (α := α)

Depends on / 依赖: norm_one
-/
instance [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (SeparationQuotient α) where
  norm_one := norm_one (α := α)

end SeparationQuotient

namespace NNReal

/--
lemma `lipschitzWith_sub` / 引理 `lipschitzWith_sub`

English:
lemma lipschitzWith_sub
  statement: LipschitzWith 2 (fun (p : Real>=0 × Real>=0) => p.1 - p.2)
  proof: by
  rw [← NNReal.isometry_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : Real>=0 -> Real) ((↑) : Real>=0 -> Real)) :=
    NNReal.isometry_coe.prodMap NNReal.isometry_coe
  convert!
    (((LipschitzWith.prod_fst.comp this.lipschitz).sub
          (LipschitzWith.prod_snd.comp this.lipschitz)).max_const
      0)
  norm_num

中文:
引理 lipschitzWith_sub
  结论: LipschitzWith 2 (fun (p : 实数>=0 × 实数>=0) => p.1 - p.2)
  证明: by
  rw [← NNReal.isometry_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : Real>=0 -> Real) ((↑) : Real>=0 -> Real)) :=
    NNReal.isometry_coe.prodMap NNReal.isometry_coe
  convert!
    (((LipschitzWith.prod_fst.comp this.lipschitz).sub
          (LipschitzWith.prod_snd.comp this.lipschitz)).max_const
      0)
  norm_num

Depends on / 依赖: Isometry, LipschitzWith, LipschitzWith.prod_fst.comp, LipschitzWith.prod_snd.comp, NNReal, NNReal.isometry_coe, NNReal.isometry_coe.lipschitzWith_iff, NNReal.isometry_coe.prodMap, Prod.map, convert, isometry_coe, lipschitz, lipschitzWith_iff, max_const, prodMap, prod_fst, prod_snd, this.lipschitz
-/
lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : Real>=0 × Real>=0) => p.1 - p.2) := by
  rw [← NNReal.isometry_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : Real>=0 -> Real) ((↑) : Real>=0 -> Real)) :=
    NNReal.isometry_coe.prodMap NNReal.isometry_coe
  convert!
    (((LipschitzWith.prod_fst.comp this.lipschitz).sub
          (LipschitzWith.prod_snd.comp this.lipschitz)).max_const
      0)
  norm_num

end NNReal

/--
Instance `Int.instNormedCommRing` / 实例 `Int.instNormedCommRing`

English:
instance Int.instNormedCommRing
  signature: : NormedCommRing Int where
  body: instCommRing
  __ := instNormedAddCommGroup
  norm_mul_le m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

中文:
实例 整数.instNormedCommRing
  签名: : NormedComm环 整数 where
  定义体: instCommRing
  __ := instNormedAddCommGroup
  norm_mul_le m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

Depends on / 依赖: instCommRing
-/
instance Int.instNormedCommRing : NormedCommRing Int where
  __ := instCommRing
  __ := instNormedAddCommGroup
  norm_mul_le m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

/--
Instance `Int.instNormOneClass` / 实例 `Int.instNormOneClass`

English:
instance Int.instNormOneClass
  signature: : NormOneClass Int
  body: ⟨by simp [← Int.norm_cast_real]⟩

中文:
实例 整数.instNormOneClass
  签名: : NormOne类 整数
  定义体: ⟨by simp [← Int.norm_cast_real]⟩

Depends on / 依赖: Int.norm_cast_real, norm_cast_real
-/
instance Int.instNormOneClass : NormOneClass Int :=
  ⟨by simp [← Int.norm_cast_real]⟩

/--
Instance `Int.instNormMulClass` / 实例 `Int.instNormMulClass`

English:
instance Int.instNormMulClass
  signature: : NormMulClass Int
  body: ⟨fun a b => by simp [← Int.norm_cast_real, abs_mul]⟩

中文:
实例 整数.instNormMulClass
  签名: : NormMul类 整数
  定义体: ⟨fun a b => by simp [← Int.norm_cast_real, abs_mul]⟩

Depends on / 依赖: Int.norm_cast_real, abs_mul, norm_cast_real
-/
instance Int.instNormMulClass : NormMulClass Int :=
  ⟨fun a b => by simp [← Int.norm_cast_real, abs_mul]⟩

section NonUnitalNormedRing
variable [NonUnitalNormedRing α] [NormMulClass α] {a : α}

/--
lemma `antilipschitzWith_mul_left` / 引理 `antilipschitzWith_mul_left`

English:
lemma antilipschitzWith_mul_left
  given: {a : α} (ha : a != 0)
  statement: AntilipschitzWith (‖a‖₊⁻¹) (a * ·)
  proof: AntilipschitzWith.of_le_mul_dist fun _ _ => by simp [dist_eq_norm, ← mul_sub, ha]

中文:
引理 antilipschitzWith_mul_left
  条件: {a : α} (ha : a != 0)
  结论: AntilipschitzWith (‖a‖₊⁻¹) (a * ·)
  证明: AntilipschitzWith.of_le_mul_dist fun _ _ => by simp [dist_eq_norm, ← mul_sub, ha]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm, mul_sub, of_le_mul_dist
-/
lemma antilipschitzWith_mul_left {a : α} (ha : a != 0) : AntilipschitzWith (‖a‖₊⁻¹) (a * ·) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ => by simp [dist_eq_norm, ← mul_sub, ha]

/--
lemma `antilipschitzWith_mul_right` / 引理 `antilipschitzWith_mul_right`

English:
lemma antilipschitzWith_mul_right
  given: {a : α} (ha : a != 0)
  statement: AntilipschitzWith (‖a‖₊⁻¹) (· * a)
  proof: AntilipschitzWith.of_le_mul_dist fun _ _ => by simp [dist_eq_norm, ← sub_mul, mul_comm, ha]

中文:
引理 antilipschitzWith_mul_right
  条件: {a : α} (ha : a != 0)
  结论: AntilipschitzWith (‖a‖₊⁻¹) (· * a)
  证明: AntilipschitzWith.of_le_mul_dist fun _ _ => by simp [dist_eq_norm, ← sub_mul, mul_comm, ha]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm, mul_comm, of_le_mul_dist, sub_mul
-/
lemma antilipschitzWith_mul_right {a : α} (ha : a != 0) : AntilipschitzWith (‖a‖₊⁻¹) (· * a) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ => by simp [dist_eq_norm, ← sub_mul, mul_comm, ha]

/-- Multiplication by a nonzero element `a` on the left, as a `Dilation` of a ring with a strictly
multiplicative norm. -/
@[simps!]
/--
Definition of `Dilation.mulLeft` / `Dilation.mulLeft` 的定义

English:
definition Dilation.mulLeft
  signature: (a : α) (ha : a != 0)
  body: a * b
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y => by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

中文:
定义 Dilation.mulLeft
  签名: (a : α) (ha : a != 0)
  定义体: a * b
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y => by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩
-/
def Dilation.mulLeft (a : α) (ha : a != 0) : α ->ᵈ α where
  toFun b := a * b
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y => by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

/-- Multiplication by a nonzero element `a` on the right, as a `Dilation` of a ring with a strictly
multiplicative norm. -/
@[simps!]
/--
Definition of `Dilation.mulRight` / `Dilation.mulRight` 的定义

English:
definition Dilation.mulRight
  signature: (a : α) (ha : a != 0)
  body: b * a
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y => by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

中文:
定义 Dilation.mulRight
  签名: (a : α) (ha : a != 0)
  定义体: b * a
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y => by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩
-/
def Dilation.mulRight (a : α) (ha : a != 0) : α ->ᵈ α where
  toFun b := b * a
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y => by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

namespace Filter

@[simp]
/--
lemma `comap_mul_left_cobounded` / 引理 `comap_mul_left_cobounded`

English:
lemma comap_mul_left_cobounded
  given: {a : α} (ha : a != 0)
  proof: Dilation.comap_cobounded (Dilation.mulLeft a ha)

@[simp]

中文:
引理 comap_mul_left_cobounded
  条件: {a : α} (ha : a != 0)
  证明: Dilation.comap_cobounded (Dilation.mulLeft a ha)

@[simp]

Depends on / 依赖: Dilation, Dilation.comap_cobounded, Dilation.mulLeft, comap_cobounded, mulLeft
-/
lemma comap_mul_left_cobounded {a : α} (ha : a != 0) :
    comap (a * ·) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (Dilation.mulLeft a ha)

@[simp]
/--
lemma `comap_mul_right_cobounded` / 引理 `comap_mul_right_cobounded`

English:
lemma comap_mul_right_cobounded
  given: {a : α} (ha : a != 0)
  proof: Dilation.comap_cobounded (Dilation.mulRight a ha)

中文:
引理 comap_mul_right_cobounded
  条件: {a : α} (ha : a != 0)
  证明: Dilation.comap_cobounded (Dilation.mulRight a ha)

Depends on / 依赖: Dilation, Dilation.comap_cobounded, Dilation.mulRight, comap_cobounded, mulRight
-/
lemma comap_mul_right_cobounded {a : α} (ha : a != 0) :
    comap (· * a) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (Dilation.mulRight a ha)

end Filter

end NonUnitalNormedRing
