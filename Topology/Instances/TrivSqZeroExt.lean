/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Topology on `TrivSqZeroExt R M`

The type `TrivSqZeroExt R M` inherits the topology from `R × M`.

Note that this is not the topology induced by the seminorm on the dual numbers suggested by
[this Math.SE answer](https://math.stackexchange.com/a/1056378/1896), which instead induces
the topology pulled back through the projection map `TrivSqZeroExt.fst : tsze R M → R`.
Obviously, that topology is not Hausdorff and using it would result in `exp` converging to more than
one value.

## Main results

* `TrivSqZeroExt.topologicalRing`: the ring operations are continuous

-/

@[expose] public section

open Topology

variable {α S R M : Type*}

local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Topology

variable [TopologicalSpace R] [TopologicalSpace M]

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (tsze R M)
  body: TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (tsze R M)
  定义体: TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, induced
-/
instance instTopologicalSpace : TopologicalSpace (tsze R M) :=
  TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: R] [T2Space M] : T2Space (tsze R M)
  body: Prod.t2Space

中文:
实例 [T2空间
  签名: R] [T2空间 M] : T2空间 (tsze R M)
  定义体: Prod.t2Space

Depends on / 依赖: Prod.t2Space, t2Space
-/
instance [T2Space R] [T2Space M] : T2Space (tsze R M) :=
  Prod.t2Space

/--
theorem `nhds_def` / 定理 `nhds_def`

English:
theorem nhds_def
  given: (x : tsze R M)
  statement: 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.snd
  proof: nhds_prod_eq

中文:
定理 nhds_def
  条件: (x : tsze R M)
  结论: 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.snd
  证明: nhds_prod_eq

Depends on / 依赖: nhds_prod_eq
-/
theorem nhds_def (x : tsze R M) : 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.snd := nhds_prod_eq

/--
theorem `nhds_inl` / 定理 `nhds_inl`

English:
theorem nhds_inl
  given: [Zero M] (x : R)
  statement: 𝓝 (inl x : tsze R M) = 𝓝 x ×ˢ 𝓝 0
  proof: nhds_def _

中文:
定理 nhds_inl
  条件: [零 M] (x : R)
  结论: 𝓝 (inl x : tsze R M) = 𝓝 x ×ˢ 𝓝 0
  证明: nhds_def _

Depends on / 依赖: nhds_def
-/
theorem nhds_inl [Zero M] (x : R) : 𝓝 (inl x : tsze R M) = 𝓝 x ×ˢ 𝓝 0 :=
  nhds_def _

/--
theorem `nhds_inr` / 定理 `nhds_inr`

English:
theorem nhds_inr
  given: [Zero R] (m : M)
  statement: 𝓝 (inr m : tsze R M) = 𝓝 0 ×ˢ 𝓝 m
  proof: nhds_def _

nonrec theorem continuous_fst : Continuous (fst : tsze R M -> R) :=
  continuous_fst

nonrec theorem continuous_snd : Continuous (snd : tsze R M -> M) :=
  continuous_snd

中文:
定理 nhds_inr
  条件: [零 R] (m : M)
  结论: 𝓝 (inr m : tsze R M) = 𝓝 0 ×ˢ 𝓝 m
  证明: nhds_def _

nonrec theorem continuous_fst : Continuous (fst : tsze R M -> R) :=
  continuous_fst

nonrec theorem continuous_snd : Continuous (snd : tsze R M -> M) :=
  continuous_snd

Depends on / 依赖: nhds_def
-/
theorem nhds_inr [Zero R] (m : M) : 𝓝 (inr m : tsze R M) = 𝓝 0 ×ˢ 𝓝 m :=
  nhds_def _

nonrec theorem continuous_fst : Continuous (fst : tsze R M -> R) :=
  continuous_fst

nonrec theorem continuous_snd : Continuous (snd : tsze R M -> M) :=
  continuous_snd

/--
theorem `continuous_inl` / 定理 `continuous_inl`

English:
theorem continuous_inl
  given: [Zero M]
  statement: Continuous (inl : R -> tsze R M)
  proof: continuous_id.prodMk continuous_const

中文:
定理 continuous_inl
  条件: [零 M]
  结论: 连续 (inl : R -> tsze R M)
  证明: continuous_id.prodMk continuous_const

Depends on / 依赖: continuous_const, continuous_id, continuous_id.prodMk, prodMk
-/
theorem continuous_inl [Zero M] : Continuous (inl : R -> tsze R M) :=
  continuous_id.prodMk continuous_const

/--
theorem `continuous_inr` / 定理 `continuous_inr`

English:
theorem continuous_inr
  given: [Zero R]
  statement: Continuous (inr : M -> tsze R M)
  proof: continuous_const.prodMk continuous_id

中文:
定理 continuous_inr
  条件: [零 R]
  结论: 连续 (inr : M -> tsze R M)
  证明: continuous_const.prodMk continuous_id

Depends on / 依赖: continuous_const, continuous_const.prodMk, continuous_id, prodMk
-/
theorem continuous_inr [Zero R] : Continuous (inr : M -> tsze R M) :=
  continuous_const.prodMk continuous_id

/--
theorem `IsEmbedding.inl` / 定理 `IsEmbedding.inl`

English:
theorem IsEmbedding.inl
  given: [Zero M]
  statement: IsEmbedding (inl : R -> tsze R M)
  proof: .of_comp continuous_inl continuous_fst .id

中文:
定理 是嵌入.inl
  条件: [零 M]
  结论: 是嵌入 (inl : R -> tsze R M)
  证明: .of_comp continuous_inl continuous_fst .id

Depends on / 依赖: continuous_fst, continuous_inl, of_comp
-/
theorem IsEmbedding.inl [Zero M] : IsEmbedding (inl : R -> tsze R M) :=
  .of_comp continuous_inl continuous_fst .id

/--
theorem `IsEmbedding.inr` / 定理 `IsEmbedding.inr`

English:
theorem IsEmbedding.inr
  given: [Zero R]
  statement: IsEmbedding (inr : M -> tsze R M)
  proof: .of_comp continuous_inr continuous_snd .id

中文:
定理 是嵌入.inr
  条件: [零 R]
  结论: 是嵌入 (inr : M -> tsze R M)
  证明: .of_comp continuous_inr continuous_snd .id

Depends on / 依赖: continuous_inr, continuous_snd, of_comp
-/
theorem IsEmbedding.inr [Zero R] : IsEmbedding (inr : M -> tsze R M) :=
  .of_comp continuous_inr continuous_snd .id

variable (R M)

/-- `TrivSqZeroExt.fst` as a continuous linear map. -/
@[simps]
/--
Definition of `fstCLM` / `fstCLM` 的定义

English:
definition fstCLM
  signature: [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: { ContinuousLinearMap.fst R R M with toFun := fst }

中文:
定义 fstCLM
  签名: [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { ContinuousLinearMap.fst R R M with toFun := fst }

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst
-/
def fstCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : StrongDual R (tsze R M) :=
  { ContinuousLinearMap.fst R R M with toFun := fst }

/-- `TrivSqZeroExt.snd` as a continuous linear map. -/
@[simps]
/--
Definition of `sndCLM` / `sndCLM` 的定义

English:
definition sndCLM
  signature: [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: { ContinuousLinearMap.snd R R M with toFun := snd }

中文:
定义 sndCLM
  签名: [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { ContinuousLinearMap.snd R R M with toFun := snd }

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.snd
-/
def sndCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M ->L[R] M :=
  { ContinuousLinearMap.snd R R M with toFun := snd }

/-- `TrivSqZeroExt.inl` as a continuous linear map. -/
@[simps]
/--
Definition of `inlCLM` / `inlCLM` 的定义

English:
definition inlCLM
  signature: [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: { ContinuousLinearMap.inl R R M with toFun := inl }

中文:
定义 inlCLM
  签名: [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { ContinuousLinearMap.inl R R M with toFun := inl }

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.inl
-/
def inlCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : R ->L[R] tsze R M :=
  { ContinuousLinearMap.inl R R M with toFun := inl }

/-- `TrivSqZeroExt.inr` as a continuous linear map. -/
@[simps]
/--
Definition of `inrCLM` / `inrCLM` 的定义

English:
definition inrCLM
  signature: [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: { ContinuousLinearMap.inr R R M with toFun := inr }

中文:
定义 inrCLM
  签名: [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { ContinuousLinearMap.inr R R M with toFun := inr }

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.inr
-/
def inrCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : M ->L[R] tsze R M :=
  { ContinuousLinearMap.inr R R M with toFun := inr }

variable {R M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [Add M] [ContinuousAdd R] [ContinuousAdd M] : ContinuousAdd (tsze R M)
  body: Prod.continuousAdd

中文:
实例 [加法
  签名: R] [加法 M] [连续加法 R] [连续加法 M] : 连续加法 (tsze R M)
  定义体: Prod.continuousAdd

Depends on / 依赖: Prod.continuousAdd, continuousAdd
-/
instance [Add R] [Add M] [ContinuousAdd R] [ContinuousAdd M] : ContinuousAdd (tsze R M) :=
  Prod.continuousAdd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousMul R] [ContinuousSMul R M]
  body: ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩

中文:
实例 [乘法
  签名: R] [加法 M] [标量乘法 R M] [标量乘法 Rᵐᵒᵖ M] [连续乘法 R] [连续标量乘法 R M]
  定义体: ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩

Depends on / 依赖: MulOpposite, MulOpposite.continuous_op.comp, continuous_fst, continuous_fst.comp, continuous_op, continuous_snd, continuous_snd.comp, prodMk
-/
instance [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousMul R] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] [ContinuousAdd M] : ContinuousMul (tsze R M) :=
⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Neg
  signature: R] [Neg M] [ContinuousNeg R] [ContinuousNeg M] : ContinuousNeg (tsze R M)
  body: Prod.continuousNeg

中文:
实例 [取负
  签名: R] [取负 M] [连续取负 R] [连续取负 M] : 连续取负 (tsze R M)
  定义体: Prod.continuousNeg

Depends on / 依赖: Prod.continuousNeg, continuousNeg
-/
instance [Neg R] [Neg M] [ContinuousNeg R] [ContinuousNeg M] : ContinuousNeg (tsze R M) :=
  Prod.continuousNeg

/--
theorem `topologicalSemiring` / 定理 `topologicalSemiring`

English:
theorem topologicalSemiring
  statement: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  proof: { }

中文:
定理 topologicalSemiring
  结论: [半环 R] [加法交换幺半群 M] [模 R M] [模 Rᵐᵒᵖ M]
  证明: { }
-/
theorem topologicalSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsTopologicalSemiring R] [ContinuousAdd M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    IsTopologicalSemiring (tsze R M) := { }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsTopologicalRing R]

中文:
实例 [环
  签名: R] [加法交换群 M] [模 R M] [模 Rᵐᵒᵖ M] [是拓扑环 R]
-/
instance [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsTopologicalRing R]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    IsTopologicalRing (tsze R M) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S R] [SMul S M] [ContinuousConstSMul S R] [ContinuousConstSMul S M] :
  body: Prod.continuousConstSMul

中文:
实例 [标量乘法
  签名: S R] [标量乘法 S M] [连续常数标量乘法 S R] [连续常数标量乘法 S M] :
  定义体: Prod.continuousConstSMul

Depends on / 依赖: Prod.continuousConstSMul, continuousConstSMul
-/
instance [SMul S R] [SMul S M] [ContinuousConstSMul S R] [ContinuousConstSMul S M] :
    ContinuousConstSMul S (tsze R M) :=
  Prod.continuousConstSMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: S] [SMul S R] [SMul S M] [ContinuousSMul S R] [ContinuousSMul S M] :
  body: Prod.continuousSMul

中文:
实例 [拓扑空间
  签名: S] [标量乘法 S R] [标量乘法 S M] [连续标量乘法 S R] [连续标量乘法 S M] :
  定义体: Prod.continuousSMul

Depends on / 依赖: Prod.continuousSMul, continuousSMul
-/
instance [TopologicalSpace S] [SMul S R] [SMul S M] [ContinuousSMul S R] [ContinuousSMul S M] :
    ContinuousSMul S (tsze R M) :=
  Prod.continuousSMul

variable (M)

/--
theorem `hasSum_inl` / 定理 `hasSum_inl`

English:
theorem hasSum_inl
  given: [AddCommMonoid R] [AddCommMonoid M] {f : α -> R} {a : R} (h : HasSum f a)
  proof: h.map (⟨⟨inl, inl_zero _⟩, inl_add _⟩ : R ->+ tsze R M) continuous_inl

中文:
定理 hasSum_inl
  条件: [加法交换幺半群 R] [加法交换幺半群 M] {f : α -> R} {a : R} (h : HasSum f a)
  证明: h.map (⟨⟨inl, inl_zero _⟩, inl_add _⟩ : R ->+ tsze R M) continuous_inl

Depends on / 依赖: continuous_inl, h.map, inl_add, inl_zero
-/
theorem hasSum_inl [AddCommMonoid R] [AddCommMonoid M] {f : α -> R} {a : R} (h : HasSum f a) :
    HasSum (fun x => inl (f x)) (inl a : tsze R M) :=
  h.map (⟨⟨inl, inl_zero _⟩, inl_add _⟩ : R ->+ tsze R M) continuous_inl

/--
theorem `hasSum_inr` / 定理 `hasSum_inr`

English:
theorem hasSum_inr
  given: [AddCommMonoid R] [AddCommMonoid M] {f : α -> M} {a : M} (h : HasSum f a)
  proof: h.map (⟨⟨inr, inr_zero _⟩, inr_add _⟩ : M ->+ tsze R M) continuous_inr

中文:
定理 hasSum_inr
  条件: [加法交换幺半群 R] [加法交换幺半群 M] {f : α -> M} {a : M} (h : HasSum f a)
  证明: h.map (⟨⟨inr, inr_zero _⟩, inr_add _⟩ : M ->+ tsze R M) continuous_inr

Depends on / 依赖: continuous_inr, h.map, inr_add, inr_zero
-/
theorem hasSum_inr [AddCommMonoid R] [AddCommMonoid M] {f : α -> M} {a : M} (h : HasSum f a) :
    HasSum (fun x => inr (f x)) (inr a : tsze R M) :=
  h.map (⟨⟨inr, inr_zero _⟩, inr_add _⟩ : M ->+ tsze R M) continuous_inr

/--
theorem `hasSum_fst` / 定理 `hasSum_fst`

English:
theorem hasSum_fst
  statement: [AddCommMonoid R] [AddCommMonoid M] {f : α -> tsze R M} {a : tsze R M}
  proof: h.map (⟨⟨fst, fst_zero⟩, fst_add⟩ : tsze R M ->+ R) continuous_fst

中文:
定理 hasSum_fst
  结论: [加法交换幺半群 R] [加法交换幺半群 M] {f : α -> tsze R M} {a : tsze R M}
  证明: h.map (⟨⟨fst, fst_zero⟩, fst_add⟩ : tsze R M ->+ R) continuous_fst

Depends on / 依赖: continuous_fst, fst_add, fst_zero, h.map
-/
theorem hasSum_fst [AddCommMonoid R] [AddCommMonoid M] {f : α -> tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x => fst (f x)) (fst a) :=
  h.map (⟨⟨fst, fst_zero⟩, fst_add⟩ : tsze R M ->+ R) continuous_fst

/--
theorem `hasSum_snd` / 定理 `hasSum_snd`

English:
theorem hasSum_snd
  statement: [AddCommMonoid R] [AddCommMonoid M] {f : α -> tsze R M} {a : tsze R M}
  proof: h.map (⟨⟨snd, snd_zero⟩, snd_add⟩ : tsze R M ->+ M) continuous_snd

中文:
定理 hasSum_snd
  结论: [加法交换幺半群 R] [加法交换幺半群 M] {f : α -> tsze R M} {a : tsze R M}
  证明: h.map (⟨⟨snd, snd_zero⟩, snd_add⟩ : tsze R M ->+ M) continuous_snd

Depends on / 依赖: continuous_snd, h.map, snd_add, snd_zero
-/
theorem hasSum_snd [AddCommMonoid R] [AddCommMonoid M] {f : α -> tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x => snd (f x)) (snd a) :=
  h.map (⟨⟨snd, snd_zero⟩, snd_add⟩ : tsze R M ->+ M) continuous_snd

end Topology

section Uniformity
variable [UniformSpace R] [UniformSpace M]

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (tsze R M) where
  body: instTopologicalSpace
  __ := instUniformSpaceProd

中文:
实例 instUniformSpace
  签名: : 一致空间 (tsze R M) where
  定义体: instTopologicalSpace
  __ := instUniformSpaceProd

Depends on / 依赖: instTopologicalSpace
-/
instance instUniformSpace : UniformSpace (tsze R M) where
  toTopologicalSpace := instTopologicalSpace
  __ := instUniformSpaceProd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: R] [CompleteSpace M] : CompleteSpace (tsze R M)
  body: inferInstanceAs CompleteSpace (R × M)

中文:
实例 [完备空间
  签名: R] [完备空间 M] : 完备空间 (tsze R M)
  定义体: inferInstanceAs CompleteSpace (R × M)

Depends on / 依赖: CompleteSpace
-/
instance [CompleteSpace R] [CompleteSpace M] : CompleteSpace (tsze R M) :=
inferInstanceAs CompleteSpace (R × M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: R] [AddGroup M] [IsUniformAddGroup R] [IsUniformAddGroup M] :
  body: inferInstanceAs IsUniformAddGroup (R × M)

中文:
实例 [加法群
  签名: R] [加法群 M] [是UniformAdd群 R] [是UniformAdd群 M] :
  定义体: inferInstanceAs IsUniformAddGroup (R × M)

Depends on / 依赖: IsUniformAddGroup
-/
instance [AddGroup R] [AddGroup M] [IsUniformAddGroup R] [IsUniformAddGroup M] :
    IsUniformAddGroup (tsze R M) :=
inferInstanceAs IsUniformAddGroup (R × M)

open Uniformity

/--
theorem `uniformity_def` / 定理 `uniformity_def`

English:
theorem uniformity_def
  proof: rfl

nonrec theorem uniformContinuous_fst : UniformContinuous (fst : tsze R M -> R) :=
  uniformContinuous_fst

nonrec theorem uniformContinuous_snd : UniformContinuous (snd : tsze R M -> M) :=
  uniformContinuous_snd

中文:
定理 uniformity_def
  证明: rfl

nonrec theorem uniformContinuous_fst : UniformContinuous (fst : tsze R M -> R) :=
  uniformContinuous_fst

nonrec theorem uniformContinuous_snd : UniformContinuous (snd : tsze R M -> M) :=
  uniformContinuous_snd
-/
theorem uniformity_def :
    𝓤 (tsze R M) =
      ((𝓤 R).comap fun p => (p.1.fst, p.2.fst)) ⊓ ((𝓤 M).comap fun p => (p.1.snd, p.2.snd)) :=
  rfl

nonrec theorem uniformContinuous_fst : UniformContinuous (fst : tsze R M -> R) :=
  uniformContinuous_fst

nonrec theorem uniformContinuous_snd : UniformContinuous (snd : tsze R M -> M) :=
  uniformContinuous_snd

/--
theorem `uniformContinuous_inl` / 定理 `uniformContinuous_inl`

English:
theorem uniformContinuous_inl
  given: [Zero M]
  statement: UniformContinuous (inl : R -> tsze R M)
  proof: uniformContinuous_id.prodMk uniformContinuous_const

中文:
定理 uniformContinuous_inl
  条件: [零 M]
  结论: 一致连续 (inl : R -> tsze R M)
  证明: uniformContinuous_id.prodMk uniformContinuous_const

Depends on / 依赖: prodMk, uniformContinuous_const, uniformContinuous_id, uniformContinuous_id.prodMk
-/
theorem uniformContinuous_inl [Zero M] : UniformContinuous (inl : R -> tsze R M) :=
  uniformContinuous_id.prodMk uniformContinuous_const

/--
theorem `uniformContinuous_inr` / 定理 `uniformContinuous_inr`

English:
theorem uniformContinuous_inr
  given: [Zero R]
  statement: UniformContinuous (inr : M -> tsze R M)
  proof: uniformContinuous_const.prodMk uniformContinuous_id

中文:
定理 uniformContinuous_inr
  条件: [零 R]
  结论: 一致连续 (inr : M -> tsze R M)
  证明: uniformContinuous_const.prodMk uniformContinuous_id

Depends on / 依赖: prodMk, uniformContinuous_const, uniformContinuous_const.prodMk, uniformContinuous_id
-/
theorem uniformContinuous_inr [Zero R] : UniformContinuous (inr : M -> tsze R M) :=
  uniformContinuous_const.prodMk uniformContinuous_id

end Uniformity

end TrivSqZeroExt
