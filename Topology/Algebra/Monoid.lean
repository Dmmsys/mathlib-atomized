/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Mitchell Lee
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Theory of topological monoids

In this file we define mixin classes `ContinuousMul` and `ContinuousAdd`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

@[expose] public section

universe u v

open Set Filter TopologicalSpace Topology
open scoped Topology Pointwise

variable {ι α M N X : Type*} [TopologicalSpace X]

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_one` / 定理 `continuous_one`

English:
theorem continuous_one
  given: [TopologicalSpace M] [One M]
  statement: Continuous (1 : X -> M)
  proof: @continuous_const _ _ _ _ 1

中文:
定理 continuous_one
  条件: [TopologicalSpace M] [One M]
  结论: Continuous (1 : X -> M)
  证明: @continuous_const _ _ _ _ 1

Depends on / 依赖: continuous_const
-/
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X -> M) :=
  @continuous_const _ _ _ _ 1

namespace MulOpposite

/-- If multiplication is separately continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is separately continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [Mul α] [SeparatelyContinuousMul α] :
  body: continuous_op.comp (continuous_unop.const_mul (unop _))
  continuous_const_mul := continuous_op.comp (continuous_unop.mul_const (unop _))

中文:
实例 [TopologicalSpace
  签名: α] [Mul α] [SeparatelyContinuousMul α] :
  定义体: continuous_op.comp (continuous_unop.const_mul (unop _))
  continuous_const_mul := continuous_op.comp (continuous_unop.mul_const (unop _))

Depends on / 依赖: const_mul, continuous_op, continuous_op.comp, continuous_unop, continuous_unop.const_mul
-/
instance [TopologicalSpace α] [Mul α] [SeparatelyContinuousMul α] :
    SeparatelyContinuousMul αᵐᵒᵖ where
  continuous_mul_const := continuous_op.comp (continuous_unop.const_mul (unop _))
  continuous_const_mul := continuous_op.comp (continuous_unop.mul_const (unop _))

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ
  body: ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

中文:
实例 [TopologicalSpace
  签名: α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ
  定义体: ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

Depends on / 依赖: continuous_op, continuous_op.comp, continuous_unop, continuous_unop.fst, continuous_unop.snd
-/
instance [TopologicalSpace α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ :=
  ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end MulOpposite

section SeparatelyContinuousMul

variable [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeparatelyContinuousMul Mᵒᵈ
  body: ‹SeparatelyContinuousMul M›

@[to_additive]

中文:
实例 :
  签名: SeparatelyContinuousMul Mᵒᵈ
  定义体: ‹SeparatelyContinuousMul M›

@[to_additive]

Depends on / 依赖: SeparatelyContinuousMul
-/
instance : SeparatelyContinuousMul Mᵒᵈ :=
  ‹SeparatelyContinuousMul M›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeparatelyContinuousMul (ULift.{u} M)
  body: ⟨continuous_uliftUp.comp (by fun_prop), continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]

中文:
实例 :
  签名: SeparatelyContinuousMul (ULift.{u} M)
  定义体: ⟨continuous_uliftUp.comp (by fun_prop), continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]

Depends on / 依赖: continuous_uliftUp, continuous_uliftUp.comp, fun_prop
-/
instance : SeparatelyContinuousMul (ULift.{u} M) :=
  ⟨continuous_uliftUp.comp (by fun_prop), continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]
/--
Instance `SeparatelyContinuousMul.to_continuousSMul` / 实例 `SeparatelyContinuousMul.to_continuousSMul`

English:
instance SeparatelyContinuousMul.to_continuousSMul
  signature: : ContinuousConstSMul M M
  body: ⟨fun _ => continuous_const_mul⟩

@[to_additive]

中文:
实例 SeparatelyContinuousMul.to_continuousSMul
  签名: : ContinuousConstSMul M M
  定义体: ⟨fun _ => continuous_const_mul⟩

@[to_additive]

Depends on / 依赖: continuous_const_mul
-/
instance SeparatelyContinuousMul.to_continuousSMul : ContinuousConstSMul M M :=
  ⟨fun _ => continuous_const_mul⟩

@[to_additive]
/--
Instance `SeparatelyContinuousMul.to_continuousSMul_op` / 实例 `SeparatelyContinuousMul.to_continuousSMul_op`

English:
instance SeparatelyContinuousMul.to_continuousSMul_op
  signature: : ContinuousConstSMul Mᵐᵒᵖ M
  body: ⟨fun _ => continuous_mul_const⟩

中文:
实例 SeparatelyContinuousMul.to_continuousSMul_op
  签名: : ContinuousConstSMul Mᵐᵒᵖ M
  定义体: ⟨fun _ => continuous_mul_const⟩

Depends on / 依赖: continuous_mul_const
-/
instance SeparatelyContinuousMul.to_continuousSMul_op : ContinuousConstSMul Mᵐᵒᵖ M :=
  ⟨fun _ => continuous_mul_const⟩

end SeparatelyContinuousMul

section ContinuousMul

variable [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMul Mᵒᵈ
  body: ‹ContinuousMul M›

@[to_additive]

中文:
实例 :
  签名: ContinuousMul Mᵒᵈ
  定义体: ‹ContinuousMul M›

@[to_additive]

Depends on / 依赖: ContinuousMul
-/
instance : ContinuousMul Mᵒᵈ :=
  ‹ContinuousMul M›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMul (ULift.{u} M)
  body: ⟨continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]

中文:
实例 :
  签名: ContinuousMul (ULift.{u} M)
  定义体: ⟨continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]

Depends on / 依赖: continuous_uliftUp, continuous_uliftUp.comp, fun_prop
-/
instance : ContinuousMul (ULift.{u} M) := ⟨continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]
/--
Instance `ContinuousMul.to_continuousSMul` / 实例 `ContinuousMul.to_continuousSMul`

English:
instance ContinuousMul.to_continuousSMul
  signature: : ContinuousSMul M M
  body: ⟨continuous_mul⟩

@[to_additive]

中文:
实例 ContinuousMul.to_continuousSMul
  签名: : ContinuousSMul M M
  定义体: ⟨continuous_mul⟩

@[to_additive]

Depends on / 依赖: continuous_mul
-/
instance ContinuousMul.to_continuousSMul : ContinuousSMul M M :=
  ⟨continuous_mul⟩

@[to_additive]
/--
Instance `ContinuousMul.to_continuousSMul_op` / 实例 `ContinuousMul.to_continuousSMul_op`

English:
instance ContinuousMul.to_continuousSMul_op
  signature: : ContinuousSMul Mᵐᵒᵖ M
  body: ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) by
    fun_prop⟩

@[to_additive]

中文:
实例 ContinuousMul.to_continuousSMul_op
  签名: : ContinuousSMul Mᵐᵒᵖ M
  定义体: ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) by
    fun_prop⟩

@[to_additive]

Depends on / 依赖: Continuous, MulOpposite, MulOpposite.unop, Prod.map, Prod.swap, fun_prop
-/
instance ContinuousMul.to_continuousSMul_op : ContinuousSMul Mᵐᵒᵖ M :=
  ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) by
    fun_prop⟩

@[to_additive]
/--
theorem `ContinuousMul.induced` / 定理 `ContinuousMul.induced`

English:
theorem ContinuousMul.induced
  statement: {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Mul α]
  proof: by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_mul]
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_add_left := continuous_const_add
@[deprecated (since := "2026-02-20")] alias continuous_add_right := continuous_add_const
@[t

中文:
定理 ContinuousMul.induced
  结论: {α : 类型} {β : 类型} {F : 类型} [FunLike F α β] [Mul α]
  证明: by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_mul]
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_add_left := continuous_const_add
@[deprecated (since := "2026-02-20")] alias continuous_add_right := continuous_add_const
@[t

Depends on / 依赖: Function, Function.comp_def, comp_def, continuous_induced_rng, fun_prop, induced, map_mul
-/
theorem ContinuousMul.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Mul α]
    [Mul β] [MulHomClass F α β] [tβ : TopologicalSpace β] [ContinuousMul β] (f : F) :
    @ContinuousMul α (tβ.induced f) _ := by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_mul]
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_add_left := continuous_const_add
@[deprecated (since := "2026-02-20")] alias continuous_add_right := continuous_add_const
@[to_additive existing, deprecated (since := "2026-02-20")]
alias continuous_mul_left := continuous_const_mul
@[to_additive existing, deprecated (since := "2026-02-20")]
alias continuous_mul_right := continuous_mul_const

@[to_additive]
/--
theorem `tendsto_mul` / 定理 `tendsto_mul`

English:
theorem tendsto_mul
  given: {a b : M}
  statement: Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b))
  proof: continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)

@[to_additive]

中文:
定理 tendsto_mul
  条件: {a b : M}
  结论: Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b))
  证明: continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)

@[to_additive]

Depends on / 依赖: ContinuousMul, ContinuousMul.continuous_mul, continuous_iff_continuousAt, continuous_iff_continuousAt.mp, continuous_mul
-/
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)

@[to_additive]
/--
theorem `le_nhds_mul` / 定理 `le_nhds_mul`

English:
theorem le_nhds_mul
  given: (a b : M)
  statement: 𝓝 a * 𝓝 b <= 𝓝 (a * b)
  proof: by
  rw [← map₂_mul]; rw [← map_uncurry_prod]; rw [← nhds_prod_eq]
  exact continuous_mul.tendsto _

@[to_additive (attr := simp)]

中文:
定理 le_nhds_mul
  条件: (a b : M)
  结论: 𝓝 a * 𝓝 b <= 𝓝 (a * b)
  证明: by
  rw [← map₂_mul]; rw [← map_uncurry_prod]; rw [← nhds_prod_eq]
  exact continuous_mul.tendsto _

@[to_additive (attr := simp)]

Depends on / 依赖: continuous_mul, continuous_mul.tendsto, map_uncurry_prod, nhds_prod_eq, tendsto
-/
theorem le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b <= 𝓝 (a * b) := by
  rw [← map₂_mul]; rw [← map_uncurry_prod]; rw [← nhds_prod_eq]
  exact continuous_mul.tendsto _

@[to_additive (attr := simp)]
/--
theorem `nhds_one_mul_nhds` / 定理 `nhds_one_mul_nhds`

English:
theorem nhds_one_mul_nhds
  given: {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M)
  proof: ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm
le_mul_of_one_le_left' pure_le_nhds 1

@[to_additive (attr := simp)]

中文:
定理 nhds_one_mul_nhds
  条件: {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M)
  证明: ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm
le_mul_of_one_le_left' pure_le_nhds 1

@[to_additive (attr := simp)]

Depends on / 依赖: antisymm, congr_arg, le_mul_of_one_le_left, le_nhds_mul, one_mul, pure_le_nhds, trans_eq
-/
theorem nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm
le_mul_of_one_le_left' pure_le_nhds 1

@[to_additive (attr := simp)]
/--
theorem `nhds_mul_nhds_one` / 定理 `nhds_mul_nhds_one`

English:
theorem nhds_mul_nhds_one
  given: {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M)
  proof: ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm
le_mul_of_one_le_right' pure_le_nhds 1

中文:
定理 nhds_mul_nhds_one
  条件: {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M)
  证明: ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm
le_mul_of_one_le_right' pure_le_nhds 1

Depends on / 依赖: antisymm, congr_arg, le_mul_of_one_le_right, le_nhds_mul, mul_one, pure_le_nhds, trans_eq
-/
theorem nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 a * 𝓝 1 = 𝓝 a :=
((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm
le_mul_of_one_le_right' pure_le_nhds 1

/-- This lemma exists to ensure that we can still do the simplification `pure_le_nhds_iff`
after simplifying with `pure_one`. -/
@[to_additive (attr := simp) /-- This lemma exists to ensure that we can still do the simplification
`pure_le_nhds_iff` after simplifying with `pure_zero`. -/]
/--
theorem `one_le_nhds_iff` / 定理 `one_le_nhds_iff`

English:
theorem one_le_nhds_iff
  given: [T1Space X] [One X] {b : X}
  statement: 1 <= 𝓝 b ↔ 1 = b
  proof: pure_le_nhds_iff

中文:
定理 one_le_nhds_iff
  条件: [T1Space X] [One X] {b : X}
  结论: 1 <= 𝓝 b ↔ 1 = b
  证明: pure_le_nhds_iff

Depends on / 依赖: pure_le_nhds_iff
-/
theorem one_le_nhds_iff [T1Space X] [One X] {b : X} : 1 <= 𝓝 b ↔ 1 = b :=
  pure_le_nhds_iff

section tendsto_nhds

variable {𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [Mul 𝕜] [TopologicalSpace 𝕜] [SeparatelyContinuousMul 𝕜]
  {l : Filter α} {f : α -> 𝕜} {b c : 𝕜} (hb : 0 < b)
include hb

/--
theorem `Filter.TendstoNhdsWithinIoi.const_mul` / 定理 `Filter.TendstoNhdsWithinIoi.const_mul`

English:
theorem Filter.TendstoNhdsWithinIoi.const_mul
  given: [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c))
  proof: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

中文:
定理 Filter.TendstoNhdsWithinIoi.const_mul
  条件: [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c))
  证明: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

Depends on / 依赖: Set.mem_Ioi, const_mul, mem_Ioi, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mp, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
    Tendsto (fun a => b * f a) l (𝓝[>] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

/--
theorem `Filter.TendstoNhdsWithinIio.const_mul` / 定理 `Filter.TendstoNhdsWithinIio.const_mul`

English:
theorem Filter.TendstoNhdsWithinIio.const_mul
  given: [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c))
  proof: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

中文:
定理 Filter.TendstoNhdsWithinIio.const_mul
  条件: [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c))
  证明: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

Depends on / 依赖: Set.mem_Iio, const_mul, mem_Iio, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mp, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
    Tendsto (fun a => b * f a) l (𝓝[<] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

/--
theorem `Filter.TendstoNhdsWithinIoi.mul_const` / 定理 `Filter.TendstoNhdsWithinIoi.mul_const`

English:
theorem Filter.TendstoNhdsWithinIoi.mul_const
  given: [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c))
  proof: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

中文:
定理 Filter.TendstoNhdsWithinIoi.mul_const
  条件: [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c))
  证明: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

Depends on / 依赖: Set.mem_Ioi, mem_Ioi, mul_const, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mp, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
    Tendsto (fun a => f a * b) l (𝓝[>] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

/--
theorem `Filter.TendstoNhdsWithinIio.mul_const` / 定理 `Filter.TendstoNhdsWithinIio.mul_const`

English:
theorem Filter.TendstoNhdsWithinIio.mul_const
  given: [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c))
  proof: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

中文:
定理 Filter.TendstoNhdsWithinIio.mul_const
  条件: [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c))
  证明: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

Depends on / 依赖: Set.mem_Iio, mem_Iio, mul_const, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mp, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
    Tendsto (fun a => f a * b) l (𝓝[<] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b)
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

end tendsto_nhds

@[to_additive]
/--
theorem `Specializes.mul` / 定理 `Specializes.mul`

English:
theorem Specializes.mul
  given: {a b c d : M} (hab : a ⤳ b) (hcd : c ⤳ d)
  statement: (a * c) ⤳ (b * d)
  proof: hab.smul hcd

@[to_additive]

中文:
定理 Specializes.mul
  条件: {a b c d : M} (hab : a ⤳ b) (hcd : c ⤳ d)
  结论: (a * c) ⤳ (b * d)
  证明: hab.smul hcd

@[to_additive]
-/
protected theorem Specializes.mul {a b c d : M} (hab : a ⤳ b) (hcd : c ⤳ d) : (a * c) ⤳ (b * d) :=
  hab.smul hcd

@[to_additive]
/--
theorem `Inseparable.mul` / 定理 `Inseparable.mul`

English:
theorem Inseparable.mul
  given: {a b c d : M} (hab : Inseparable a b) (hcd : Inseparable c d)
  proof: hab.smul hcd

@[to_additive]

中文:
定理 Inseparable.mul
  条件: {a b c d : M} (hab : Inseparable a b) (hcd : Inseparable c d)
  证明: hab.smul hcd

@[to_additive]
-/
protected theorem Inseparable.mul {a b c d : M} (hab : Inseparable a b) (hcd : Inseparable c d) :
    Inseparable (a * c) (b * d) :=
  hab.smul hcd

@[to_additive]
/--
theorem `Specializes.pow` / 定理 `Specializes.pow`

English:
theorem Specializes.pow
  statement: {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
  proof: Nat.recOn n (by simp only [pow_zero, specializes_rfl]) fun _ ihn => by
    simpa only [pow_succ] using ihn.mul h

@[to_additive]

中文:
定理 Specializes.pow
  结论: {M : 类型} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
  证明: Nat.recOn n (by simp only [pow_zero, specializes_rfl]) fun _ ihn => by
    simpa only [pow_succ] using ihn.mul h

@[to_additive]
-/
protected theorem Specializes.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {a b : M} (h : a ⤳ b) (n : Nat) : (a ^ n) ⤳ (b ^ n) :=
  Nat.recOn n (by simp only [pow_zero, specializes_rfl]) fun _ ihn => by
    simpa only [pow_succ] using ihn.mul h

@[to_additive]
/--
theorem `Inseparable.pow` / 定理 `Inseparable.pow`

English:
theorem Inseparable.pow
  statement: {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
  proof: (h.specializes.pow n).antisymm (h.specializes'.pow n)

中文:
定理 Inseparable.pow
  结论: {M : 类型} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
  证明: (h.specializes.pow n).antisymm (h.specializes'.pow n)
-/
protected theorem Inseparable.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {a b : M} (h : Inseparable a b) (n : Nat) : Inseparable (a ^ n) (b ^ n) :=
  (h.specializes.pow n).antisymm (h.specializes'.pow n)

/-- Construct a unit from limits of units and their inverses. -/
@[to_additive (attr := simps)
  /-- Construct an additive unit from limits of additive units and their negatives. -/]
/--
Definition of `Filter.Tendsto.units` / `Filter.Tendsto.units` 的定义

English:
definition Filter.Tendsto.units
  signature: [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2Space N]
  body: r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁

@[to_additive]

中文:
定义 Filter.Tendsto.units
  签名: [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2Space N]
  定义体: r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁

@[to_additive]
-/
def Filter.Tendsto.units [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2Space N]
    {f : ι -> Nˣ} {r₁ r₂ : N} {l : Filter ι} [l.NeBot] (h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁))
    (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ where
  val := r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁

@[to_additive]
/--
Instance `Prod.continuousMul` / 实例 `Prod.continuousMul`

English:
instance Prod.continuousMul
  signature: [TopologicalSpace N] [Mul N] [ContinuousMul N]
  body: ⟨by apply Continuous.prodMk <;> fun_prop⟩

@[to_additive]

中文:
实例 Prod.continuousMul
  签名: [TopologicalSpace N] [Mul N] [ContinuousMul N]
  定义体: ⟨by apply Continuous.prodMk <;> fun_prop⟩

@[to_additive]

Depends on / 依赖: Continuous, Continuous.prodMk, fun_prop, prodMk
-/
instance Prod.continuousMul [TopologicalSpace N] [Mul N] [ContinuousMul N] :
    ContinuousMul (M × N) :=
  ⟨by apply Continuous.prodMk <;> fun_prop⟩

@[to_additive]
/--
Instance `Prod.separatelyContinuousMul` / 实例 `Prod.separatelyContinuousMul`

English:
instance Prod.separatelyContinuousMul
  signature: {M N : Type*}
  body: by apply Continuous.prodMk <;> fun_prop
  continuous_mul_const {_} := by apply Continuous.prodMk <;> fun_prop

@[to_additive]

中文:
实例 Prod.separatelyContinuousMul
  签名: {M N : 类型}
  定义体: by apply Continuous.prodMk <;> fun_prop
  continuous_mul_const {_} := by apply Continuous.prodMk <;> fun_prop

@[to_additive]

Depends on / 依赖: Continuous, Continuous.prodMk, continuous_mul_const, fun_prop, prodMk
-/
instance Prod.separatelyContinuousMul {M N : Type*}
    [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M]
    [TopologicalSpace N] [Mul N] [SeparatelyContinuousMul N] :
    SeparatelyContinuousMul (M × N) where
  continuous_const_mul {_} := by apply Continuous.prodMk <;> fun_prop
  continuous_mul_const {_} := by apply Continuous.prodMk <;> fun_prop

@[to_additive]
/--
Instance `Pi.continuousMul` / 实例 `Pi.continuousMul`

English:
instance Pi.continuousMul
  signature: {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Mul (C i)]
  body: continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'

@[to_additive]

中文:
实例 Pi.continuousMul
  签名: {C : ι -> 类型} [对任意 i, TopologicalSpace (C i)] [对任意 i, Mul (C i)]
  定义体: continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'

@[to_additive]

Depends on / 依赖: continuous_apply, continuous_pi
-/
instance Pi.continuousMul {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Mul (C i)]
    [forall i, ContinuousMul (C i)] : ContinuousMul (forall i, C i) where
  continuous_mul :=
    continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'

@[to_additive]
/--
Instance `Pi.separatelyContinuousMul` / 实例 `Pi.separatelyContinuousMul`

English:
instance Pi.separatelyContinuousMul
  signature: {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Mul (C i)]
  body: continuous_pi fun i => (continuous_apply i).mul_const _
  continuous_const_mul {_} := continuous_pi fun i => (continuous_apply i).const_mul _

中文:
实例 Pi.separatelyContinuousMul
  签名: {C : ι -> 类型} [对任意 i, TopologicalSpace (C i)] [对任意 i, Mul (C i)]
  定义体: continuous_pi fun i => (continuous_apply i).mul_const _
  continuous_const_mul {_} := continuous_pi fun i => (continuous_apply i).const_mul _

Depends on / 依赖: continuous_apply, continuous_pi, mul_const
-/
instance Pi.separatelyContinuousMul {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Mul (C i)]
    [forall i, SeparatelyContinuousMul (C i)] : SeparatelyContinuousMul (forall i, C i) where
  continuous_mul_const {_} := continuous_pi fun i => (continuous_apply i).mul_const _
  continuous_const_mul {_} := continuous_pi fun i => (continuous_apply i).const_mul _

/-- A version of `Pi.continuousMul` for non-dependent functions. It is needed because sometimes
Lean 3 fails to use `Pi.continuousMul` for non-dependent functions. -/
@[to_additive /-- A version of `Pi.continuousAdd` for non-dependent functions. It is needed
because sometimes Lean fails to use `Pi.continuousAdd` for non-dependent functions. -/]
/--
Instance `Pi.continuousMul'` / 实例 `Pi.continuousMul'`

English:
instance Pi.continuousMul'
  signature: : ContinuousMul (ι -> M)
  body: Pi.continuousMul

@[to_additive]

中文:
实例 Pi.continuousMul'
  签名: : ContinuousMul (ι -> M)
  定义体: Pi.continuousMul

@[to_additive]

Depends on / 依赖: Pi.continuousMul, continuousMul
-/
instance Pi.continuousMul' : ContinuousMul (ι -> M) :=
  Pi.continuousMul

@[to_additive]
instance (priority := 100) continuousMul_of_discreteTopology [TopologicalSpace N] [Mul N]
    [DiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousMul_of_indiscreteTopology [TopologicalSpace N] [Mul N]
    [IndiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_indiscreteTopology⟩

open Filter

open Function

@[to_additive]
/--
theorem `ContinuousMul.of_nhds_one` / 定理 `ContinuousMul.of_nhds_one`

English:
theorem ContinuousMul.of_nhds_one
  statement: {M : Type u} [Monoid M] [TopologicalSpace M]
  proof: ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key : (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) := by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀

中文:
定理 ContinuousMul.of_nhds_one
  结论: {M : 类型u} [Monoid M] [TopologicalSpace M]
  证明: ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key : (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) := by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀

Depends on / 依赖: continuous_iff_continuousAt, mul_assoc, nhds_prod_eq, uncurry
-/
theorem ContinuousMul.of_nhds_one {M : Type u} [Monoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1 ×ˢ 𝓝 1) <| 𝓝 1)
    (hleft : forall x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : forall x₀ : M, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : ContinuousMul M :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key : (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) := by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x := by
      ext x
      simp [mul_assoc]
    calc
      map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ˢ 𝓝 y₀) := by
        rw [nhds_prod_eq]
      _ = map (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ˢ 𝓝 1) := by
        unfold uncurry
        rw [hleft x₀]; rw [hright y₀]; rw [prod_map_map_eq]; rw [Filter.map_map]; rw [Function.comp_def]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ˢ 𝓝 1)) := by
        rw [key]; rw [← Filter.map_map]
      _ <= map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) := map_mono hmul
      _ = 𝓝 (x₀ * y₀) := by
        rw [← Filter.map_map]; rw [← hright]; rw [hleft y₀]; rw [Filter.map_map]; rw [key₂]; rw [← hleft]⟩

@[to_additive]
/--
theorem `continuousMul_of_comm_of_nhds_one` / 定理 `continuousMul_of_comm_of_nhds_one`

English:
theorem continuousMul_of_comm_of_nhds_one
  statement: (M : Type u) [CommMonoid M] [TopologicalSpace M]
  proof: by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]

中文:
定理 continuousMul_of_comm_of_nhds_one
  结论: (M : 类型u) [CommMonoid M] [TopologicalSpace M]
  证明: by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]

Depends on / 依赖: ContinuousMul, ContinuousMul.of_nhds_one, mul_comm, of_nhds_one, simp_rw
-/
theorem continuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hleft : forall x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : ContinuousMul M := by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]

end ContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type*) [TopologicalSpace M₂] [T2Space M₂]

@[to_additive]
/--
theorem `isClosed_setOfPred_map_one` / 定理 `isClosed_setOfPred_map_one`

English:
theorem isClosed_setOfPred_map_one
  given: [One M₁] [One M₂]
  statement: IsClosed { f : M₁ -> M₂ | f 1 = 1 }
  proof: isClosed_eq (continuous_apply 1) continuous_const

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_one := isClosed_setOfPred_map_one

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_zero := isClosed_setOfPred_map_zero

@[to_additive]

中文:
定理 isClosed_setOfPred_map_one
  条件: [One M₁] [One M₂]
  结论: IsClosed { f : M₁ -> M₂ | f 1 = 1 }
  证明: isClosed_eq (continuous_apply 1) continuous_const

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_one := isClosed_setOfPred_map_one

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_zero := isClosed_setOfPred_map_zero

@[to_additive]

Depends on / 依赖: continuous_apply, continuous_const, isClosed_eq
-/
theorem isClosed_setOfPred_map_one [One M₁] [One M₂] : IsClosed { f : M₁ -> M₂ | f 1 = 1 } :=
  isClosed_eq (continuous_apply 1) continuous_const

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_one := isClosed_setOfPred_map_one

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_zero := isClosed_setOfPred_map_zero

@[to_additive]
/--
theorem `isClosed_setOfPred_map_mul` / 定理 `isClosed_setOfPred_map_mul`

English:
theorem isClosed_setOfPred_map_mul
  given: [Mul M₁] [Mul M₂] [ContinuousMul M₂]
  proof: by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (continuous_apply _) (by fun_prop)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_mul := isClosed_setOfPred_map_mul
@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map

中文:
定理 isClosed_setOfPred_map_mul
  条件: [Mul M₁] [Mul M₂] [ContinuousMul M₂]
  证明: by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (continuous_apply _) (by fun_prop)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_mul := isClosed_setOfPred_map_mul
@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map

Depends on / 依赖: continuous_apply, fun_prop, isClosed_eq, isClosed_iInter, ofPred_forall
-/
theorem isClosed_setOfPred_map_mul [Mul M₁] [Mul M₂] [ContinuousMul M₂] :
    IsClosed { f : M₁ -> M₂ | forall x y, f (x * y) = f x * f y } := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (continuous_apply _) (by fun_prop)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_mul := isClosed_setOfPred_map_mul
@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_add := isClosed_setOfPred_map_add

section Semigroup

variable {M₁ M₂} [Mul M₁] [Mul M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MulHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled semigroup homomorphism `M₁ →ₙ* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →ₙ* M₂` (or another type of bundled
homomorphisms that has a `MulHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Construct a bundled additive semigroup homomorphism `M₁ →ₙ+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →ₙ+ M₂` (or another
type of bundled homomorphisms that has an `AddHomClass` instance) to `M₁ → M₂`. -/]
/--
Definition of `mulHomOfMemClosureRangeCoe` / `mulHomOfMemClosureRangeCoe` 的定义

English:
definition mulHomOfMemClosureRangeCoe
  signature: (f : M₁ -> M₂)
  body: f
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf

中文:
定义 mulHomOfMemClosureRangeCoe
  签名: (f : M₁ -> M₂)
  定义体: f
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf
-/
def mulHomOfMemClosureRangeCoe (f : M₁ -> M₂)
    (hf : f in closure (range fun (f : F) (x : M₁) => f x)) : M₁ ->ₙ* M₂ where
  toFun := f
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf

/-- Construct a bundled semigroup homomorphism from a pointwise limit of semigroup homomorphisms. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Construct a bundled additive semigroup homomorphism from a pointwise limit of additive
semigroup homomorphisms -/]
/--
Definition of `mulHomOfTendsto` / `mulHomOfTendsto` 的定义

English:
definition mulHomOfTendsto
  signature: (f : M₁ -> M₂) (g : α -> F) [l.NeBot]
  body: mulHomOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => mem_range_self _

中文:
定义 mulHomOfTendsto
  签名: (f : M₁ -> M₂) (g : α -> F) [l.NeBot]
  定义体: mulHomOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => mem_range_self _

Depends on / 依赖: Eventually, Eventually.of_forall, mem_closure_of_tendsto, mem_range_self, mulHomOfMemClosureRangeCoe, of_forall
-/
def mulHomOfTendsto (f : M₁ -> M₂) (g : α -> F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ ->ₙ* M₂ :=
mulHomOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => mem_range_self _

variable (M₁ M₂)

@[to_additive]
/--
theorem `MulHom.isClosed_range_coe` / 定理 `MulHom.isClosed_range_coe`

English:
theorem MulHom.isClosed_range_coe
  statement: IsClosed (Set.range ((↑) : (M₁ ->ₙ* M₂) -> M₁ -> M₂))
  proof: isClosed_of_closure_subset fun f hf => ⟨mulHomOfMemClosureRangeCoe f hf, rfl⟩

中文:
定理 MulHom.isClosed_range_coe
  结论: IsClosed (Set.range ((↑) : (M₁ ->ₙ* M₂) -> M₁ -> M₂))
  证明: isClosed_of_closure_subset fun f hf => ⟨mulHomOfMemClosureRangeCoe f hf, rfl⟩

Depends on / 依赖: isClosed_of_closure_subset, mulHomOfMemClosureRangeCoe
-/
theorem MulHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ ->ₙ* M₂) -> M₁ -> M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨mulHomOfMemClosureRangeCoe f hf, rfl⟩

end Semigroup

section Monoid

variable {M₁ M₂} [MulOneClass M₁] [MulOneClass M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `MonoidHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another
type of bundled homomorphisms that has an `AddMonoidHomClass` instance) to `M₁ → M₂`. -/]
/--
Definition of `monoidHomOfMemClosureRangeCoe` / `monoidHomOfMemClosureRangeCoe` 的定义

English:
definition monoidHomOfMemClosureRangeCoe
  signature: (f : M₁ -> M₂)
  body: f
  map_one' := (isClosed_setOfPred_map_one M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf

中文:
定义 monoidHomOfMemClosureRangeCoe
  签名: (f : M₁ -> M₂)
  定义体: f
  map_one' := (isClosed_setOfPred_map_one M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf
-/
def monoidHomOfMemClosureRangeCoe (f : M₁ -> M₂)
    (hf : f in closure (range fun (f : F) (x : M₁) => f x)) : M₁ ->* M₂ where
  toFun := f
  map_one' := (isClosed_setOfPred_map_one M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Construct a bundled additive monoid homomorphism from a pointwise limit of additive
monoid homomorphisms -/]
/--
Definition of `monoidHomOfTendsto` / `monoidHomOfTendsto` 的定义

English:
definition monoidHomOfTendsto
  signature: (f : M₁ -> M₂) (g : α -> F) [l.NeBot]
  body: monoidHomOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => mem_range_self _

中文:
定义 monoidHomOfTendsto
  签名: (f : M₁ -> M₂) (g : α -> F) [l.NeBot]
  定义体: monoidHomOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => mem_range_self _

Depends on / 依赖: Eventually, Eventually.of_forall, mem_closure_of_tendsto, mem_range_self, monoidHomOfMemClosureRangeCoe, of_forall
-/
def monoidHomOfTendsto (f : M₁ -> M₂) (g : α -> F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ ->* M₂ :=
monoidHomOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => mem_range_self _

variable (M₁ M₂)

@[to_additive]
/--
theorem `MonoidHom.isClosed_range_coe` / 定理 `MonoidHom.isClosed_range_coe`

English:
theorem MonoidHom.isClosed_range_coe
  statement: IsClosed (Set.range ((↑) : (M₁ ->* M₂) -> M₁ -> M₂))
  proof: isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩

中文:
定理 MonoidHom.isClosed_range_coe
  结论: IsClosed (Set.range ((↑) : (M₁ ->* M₂) -> M₁ -> M₂))
  证明: isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩

Depends on / 依赖: isClosed_of_closure_subset, monoidHomOfMemClosureRangeCoe
-/
theorem MonoidHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ ->* M₂) -> M₁ -> M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩

end Monoid

end PointwiseLimits

@[to_additive]
/--
theorem `Topology.IsInducing.continuousMul` / 定理 `Topology.IsInducing.continuousMul`

English:
theorem Topology.IsInducing.continuousMul
  statement: {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
  proof: ⟨(hf.continuousSMul hf.continuous (map_mul f _ _)).1⟩

@[to_additive]

中文:
定理 Topology.IsInducing.continuousMul
  结论: {M N F : 类型} [Mul M] [Mul N] [FunLike F M N]
  证明: ⟨(hf.continuousSMul hf.continuous (map_mul f _ _)).1⟩

@[to_additive]

Depends on / 依赖: continuous, continuousSMul, hf.continuous, hf.continuousSMul, map_mul
-/
theorem Topology.IsInducing.continuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [ContinuousMul N] (f : F)
    (hf : IsInducing f) : ContinuousMul M :=
  ⟨(hf.continuousSMul hf.continuous (map_mul f _ _)).1⟩

@[to_additive]
/--
theorem `continuousMul_induced` / 定理 `continuousMul_induced`

English:
theorem continuousMul_induced
  statement: {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
  proof: letI := induced f ‹_›
  IsInducing.continuousMul f ⟨rfl⟩

@[to_additive]

中文:
定理 continuousMul_induced
  结论: {M N F : 类型} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
  证明: letI := induced f ‹_›
  IsInducing.continuousMul f ⟨rfl⟩

@[to_additive]

Depends on / 依赖: IsInducing, IsInducing.continuousMul, continuousMul, induced
-/
theorem continuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [TopologicalSpace N] [ContinuousMul N] (f : F) : @ContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.continuousMul f ⟨rfl⟩

@[to_additive]
/--
Instance `Subsemigroup.continuousMul` / 实例 `Subsemigroup.continuousMul`

English:
instance Subsemigroup.continuousMul
  signature: [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
  body: IsInducing.continuousMul ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]

中文:
实例 Subsemigroup.continuousMul
  签名: [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
  定义体: IsInducing.continuousMul ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]

Depends on / 依赖: IsInducing, IsInducing.continuousMul, MulHom, continuousMul, map_mul
-/
instance Subsemigroup.continuousMul [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
    (S : Subsemigroup M) : ContinuousMul S :=
  IsInducing.continuousMul ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]
/--
Instance `Submonoid.continuousMul` / 实例 `Submonoid.continuousMul`

English:
instance Submonoid.continuousMul
  signature: [TopologicalSpace M] [Monoid M] [ContinuousMul M]
  body: S.toSubsemigroup.continuousMul

中文:
实例 Submonoid.continuousMul
  签名: [TopologicalSpace M] [Monoid M] [ContinuousMul M]
  定义体: S.toSubsemigroup.continuousMul

Depends on / 依赖: S.toSubsemigroup.continuousMul, continuousMul, toSubsemigroup
-/
instance Submonoid.continuousMul [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    (S : Submonoid M) : ContinuousMul S :=
  S.toSubsemigroup.continuousMul

open MulOpposite in
@[to_additive]
/--
theorem `Topology.IsInducing.separatelyContinuousMul` / 定理 `Topology.IsInducing.separatelyContinuousMul`

English:
theorem Topology.IsInducing.separatelyContinuousMul
  statement: {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
  proof: (hf.continuousConstSMul f (map_mul f _ _)).1 _
  continuous_mul_const {m} :=
    have := ((opHomeomorph.isInducing.comp hf).comp (opHomeomorph.symm.isInducing)
.continuousConstSMul (fun x => op (f (unop x))) (by simp)).1 (op m)
continuous_unop.comp this.comp continuous_op

@[to_additive]

中文:
定理 Topology.IsInducing.separatelyContinuousMul
  结论: {M N F : 类型} [Mul M] [Mul N] [FunLike F M N]
  证明: (hf.continuousConstSMul f (map_mul f _ _)).1 _
  continuous_mul_const {m} :=
    have := ((opHomeomorph.isInducing.comp hf).comp (opHomeomorph.symm.isInducing)
.continuousConstSMul (fun x => op (f (unop x))) (by simp)).1 (op m)
continuous_unop.comp this.comp continuous_op

@[to_additive]

Depends on / 依赖: continuousConstSMul, hf.continuousConstSMul, map_mul
-/
theorem Topology.IsInducing.separatelyContinuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [SeparatelyContinuousMul N]
    (f : F) (hf : IsInducing f) : SeparatelyContinuousMul M where
  continuous_const_mul := (hf.continuousConstSMul f (map_mul f _ _)).1 _
  continuous_mul_const {m} :=
    have := ((opHomeomorph.isInducing.comp hf).comp (opHomeomorph.symm.isInducing)
.continuousConstSMul (fun x => op (f (unop x))) (by simp)).1 (op m)
continuous_unop.comp this.comp continuous_op

@[to_additive]
/--
theorem `separatelyContinuousMul_induced` / 定理 `separatelyContinuousMul_induced`

English:
theorem separatelyContinuousMul_induced
  statement: {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
  proof: letI := induced f ‹_›
  IsInducing.separatelyContinuousMul f ⟨rfl⟩

@[to_additive]

中文:
定理 separatelyContinuousMul_induced
  结论: {M N F : 类型} [Mul M] [Mul N] [FunLike F M N]
  证明: letI := induced f ‹_›
  IsInducing.separatelyContinuousMul f ⟨rfl⟩

@[to_additive]

Depends on / 依赖: IsInducing, IsInducing.separatelyContinuousMul, induced, separatelyContinuousMul
-/
theorem separatelyContinuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace N] [SeparatelyContinuousMul N] (f : F) :
    @SeparatelyContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.separatelyContinuousMul f ⟨rfl⟩

@[to_additive]
/--
Instance `Subsemigroup.separatelyContinuousMul` / 实例 `Subsemigroup.separatelyContinuousMul`

English:
instance Subsemigroup.separatelyContinuousMul
  signature: [TopologicalSpace M] [Semigroup M]
  body: IsInducing.separatelyContinuousMul
    ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]

中文:
实例 Subsemigroup.separatelyContinuousMul
  签名: [TopologicalSpace M] [Semigroup M]
  定义体: IsInducing.separatelyContinuousMul
    ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]

Depends on / 依赖: IsInducing, IsInducing.separatelyContinuousMul, MulHom, map_mul, separatelyContinuousMul
-/
instance Subsemigroup.separatelyContinuousMul [TopologicalSpace M] [Semigroup M]
    [SeparatelyContinuousMul M] (S : Subsemigroup M) : SeparatelyContinuousMul S :=
  IsInducing.separatelyContinuousMul
    ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]
/--
Instance `Submonoid.separatelyContinuousMul` / 实例 `Submonoid.separatelyContinuousMul`

English:
instance Submonoid.separatelyContinuousMul
  signature: [TopologicalSpace M] [Monoid M]
  body: S.toSubsemigroup.separatelyContinuousMul

中文:
实例 Submonoid.separatelyContinuousMul
  签名: [TopologicalSpace M] [Monoid M]
  定义体: S.toSubsemigroup.separatelyContinuousMul

Depends on / 依赖: S.toSubsemigroup.separatelyContinuousMul, separatelyContinuousMul, toSubsemigroup
-/
instance Submonoid.separatelyContinuousMul [TopologicalSpace M] [Monoid M]
    [SeparatelyContinuousMul M] (S : Submonoid M) : SeparatelyContinuousMul S :=
  S.toSubsemigroup.separatelyContinuousMul
section MulZeroClass

open Filter

variable {α β : Type*}
variable [TopologicalSpace M] [MulZeroClass M] [ContinuousMul M]

/--
theorem `exists_mem_nhds_zero_mul_subset` / 定理 `exists_mem_nhds_zero_mul_subset`

English:
theorem exists_mem_nhds_zero_mul_subset
  proof: by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V inter W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_m

中文:
定理 exists_mem_nhds_zero_mul_subset
  证明: by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V inter W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_m

Depends on / 依赖: V.inter_subset_left, V.inter_subset_right, V_in, W_in, hK.induction_on, induction_on, inter_mem, inter_subset_left, inter_subset_right, mem_map, mem_prod_iff, mul_subset_mul_left, mul_subset_mul_right, nhds_prod_eq, tendsto_mul, union_mul, union_subset
-/
theorem exists_mem_nhds_zero_mul_subset
    {K U : Set M} (hK : IsCompact K) (hU : U in 𝓝 0) : exists V in 𝓝 0, K * V subseteq U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V inter W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U in 𝓝 (x * 0) by simpa using hU)
    rw [nhds_prod_eq]; rw [mem_map]; rw [mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff]; rw [image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

/--
theorem `tendsto_mul_nhds_zero_prod_of_disjoint_cocompact` / 定理 `tendsto_mul_nhds_zero_prod_of_disjoint_cocompact`

English:
theorem tendsto_mul_nhds_zero_prod_of_disjoint_cocompact
  statement: {l : Filter M}
  proof: calc
  map (fun x : M × M => x.1 * x.2) (𝓝 0 ×ˢ l)
  _ <= map (fun x : M × M => x.1 * x.2) (𝓝ˢ ({0} ×ˢ Set.univ)) :=
map_mono nhds_prod_le_of_disjoint_cocompact 0 hl
  _ <= 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨hx, _⟩ => mul_eq_zero_of_left hx _

中文:
定理 tendsto_mul_nhds_zero_prod_of_disjoint_cocompact
  结论: {l : Filter M}
  证明: calc
  map (fun x : M × M => x.1 * x.2) (𝓝 0 ×ˢ l)
  _ <= map (fun x : M × M => x.1 * x.2) (𝓝ˢ ({0} ×ˢ Set.univ)) :=
map_mono nhds_prod_le_of_disjoint_cocompact 0 hl
  _ <= 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨hx, _⟩ => mul_eq_zero_of_left hx _
-/
theorem tendsto_mul_nhds_zero_prod_of_disjoint_cocompact {l : Filter M}
    (hl : Disjoint l (cocompact M)) :
    Tendsto (fun x : M × M => x.1 * x.2) (𝓝 0 ×ˢ l) (𝓝 0) := calc
  map (fun x : M × M => x.1 * x.2) (𝓝 0 ×ˢ l)
  _ <= map (fun x : M × M => x.1 * x.2) (𝓝ˢ ({0} ×ˢ Set.univ)) :=
map_mono nhds_prod_le_of_disjoint_cocompact 0 hl
  _ <= 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨hx, _⟩ => mul_eq_zero_of_left hx _

/--
theorem `tendsto_mul_prod_nhds_zero_of_disjoint_cocompact` / 定理 `tendsto_mul_prod_nhds_zero_of_disjoint_cocompact`

English:
theorem tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
  statement: {l : Filter M}
  proof: calc
  map (fun x : M × M => x.1 * x.2) (l ×ˢ 𝓝 0)
  _ <= map (fun x : M × M => x.1 * x.2) (𝓝ˢ (Set.univ ×ˢ {0})) :=
map_mono prod_nhds_le_of_disjoint_cocompact 0 hl
  _ <= 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨_, hx⟩ => mul_eq_zero_of_right _ hx

中文:
定理 tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
  结论: {l : Filter M}
  证明: calc
  map (fun x : M × M => x.1 * x.2) (l ×ˢ 𝓝 0)
  _ <= map (fun x : M × M => x.1 * x.2) (𝓝ˢ (Set.univ ×ˢ {0})) :=
map_mono prod_nhds_le_of_disjoint_cocompact 0 hl
  _ <= 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨_, hx⟩ => mul_eq_zero_of_right _ hx
-/
theorem tendsto_mul_prod_nhds_zero_of_disjoint_cocompact {l : Filter M}
    (hl : Disjoint l (cocompact M)) :
    Tendsto (fun x : M × M => x.1 * x.2) (l ×ˢ 𝓝 0) (𝓝 0) := calc
  map (fun x : M × M => x.1 * x.2) (l ×ˢ 𝓝 0)
  _ <= map (fun x : M × M => x.1 * x.2) (𝓝ˢ (Set.univ ×ˢ {0})) :=
map_mono prod_nhds_le_of_disjoint_cocompact 0 hl
  _ <= 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨_, hx⟩ => mul_eq_zero_of_right _ hx

/--
theorem `tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact` / 定理 `tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact`

English:
theorem tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact
  statement: {l : Filter (M × M)}
  proof: by
  have := calc
    (𝓝 0).coprod (𝓝 0) ⊓ l
    _ <= (𝓝 0).coprod (𝓝 0) ⊓ map Prod.fst l ×ˢ map Prod.snd l :=
      inf_le_inf_left _ le_prod_map_fst_snd
    _ <= 𝓝 0 ×ˢ map Prod.snd l ⊔ map Prod.fst l ×ˢ 𝓝 0 :=
      coprod_inf_prod_le _ _ _ _
  apply (Tendsto.sup _ _).mono_left this
  · apply ten

中文:
定理 tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact
  结论: {l : Filter (M × M)}
  证明: by
  have := calc
    (𝓝 0).coprod (𝓝 0) ⊓ l
    _ <= (𝓝 0).coprod (𝓝 0) ⊓ map Prod.fst l ×ˢ map Prod.snd l :=
      inf_le_inf_left _ le_prod_map_fst_snd
    _ <= 𝓝 0 ×ˢ map Prod.snd l ⊔ map Prod.fst l ×ˢ 𝓝 0 :=
      coprod_inf_prod_le _ _ _ _
  apply (Tendsto.sup _ _).mono_left this
  · apply ten

Depends on / 依赖: Prod.fst, Prod.snd, Tendsto, Tendsto.sup, continuous_fst, continuous_snd, coprod, coprod_inf_prod_le, disjoint_map_cocompact, inf_le_inf_left, le_prod_map_fst_snd, mono_left, tendsto_mul_nhds_zero_prod_of_disjoint_cocompact, tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
-/
theorem tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact {l : Filter (M × M)}
    (hl : Disjoint l (cocompact (M × M))) :
    Tendsto (fun x : M × M => x.1 * x.2) ((𝓝 0).coprod (𝓝 0) ⊓ l) (𝓝 0) := by
  have := calc
    (𝓝 0).coprod (𝓝 0) ⊓ l
    _ <= (𝓝 0).coprod (𝓝 0) ⊓ map Prod.fst l ×ˢ map Prod.snd l :=
      inf_le_inf_left _ le_prod_map_fst_snd
    _ <= 𝓝 0 ×ˢ map Prod.snd l ⊔ map Prod.fst l ×ˢ 𝓝 0 :=
      coprod_inf_prod_le _ _ _ _
  apply (Tendsto.sup _ _).mono_left this
  · apply tendsto_mul_nhds_zero_prod_of_disjoint_cocompact
    exact disjoint_map_cocompact continuous_snd hl
  · apply tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
    exact disjoint_map_cocompact continuous_fst hl

/--
theorem `tendsto_mul_nhds_zero_of_disjoint_cocompact` / 定理 `tendsto_mul_nhds_zero_of_disjoint_cocompact`

English:
theorem tendsto_mul_nhds_zero_of_disjoint_cocompact
  statement: {l : Filter (M × M)}
  proof: by
  simpa [inf_eq_right.mpr h'l] using tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact hl

中文:
定理 tendsto_mul_nhds_zero_of_disjoint_cocompact
  结论: {l : Filter (M × M)}
  证明: by
  simpa [inf_eq_right.mpr h'l] using tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact hl

Depends on / 依赖: inf_eq_right, inf_eq_right.mpr, tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact
-/
theorem tendsto_mul_nhds_zero_of_disjoint_cocompact {l : Filter (M × M)}
    (hl : Disjoint l (cocompact (M × M))) (h'l : l <= (𝓝 0).coprod (𝓝 0)) :
    Tendsto (fun x : M × M => x.1 * x.2) l (𝓝 0) := by
  simpa [inf_eq_right.mpr h'l] using tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact hl

/--
theorem `Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right` / 定理 `Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right`

English:
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right
  statement: {f g : α -> M} {l : Filter α}
  proof: .comp (hf.prodMk tendsto_map) tendsto_mul_nhds_zero_prod_of_disjoint_cocompact hg

中文:
定理 Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right
  结论: {f g : α -> M} {l : Filter α}
  证明: .comp (hf.prodMk tendsto_map) tendsto_mul_nhds_zero_prod_of_disjoint_cocompact hg

Depends on / 依赖: hf.prodMk, prodMk, tendsto_map, tendsto_mul_nhds_zero_prod_of_disjoint_cocompact
-/
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right {f g : α -> M} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : Disjoint (map g l) (cocompact M)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
.comp (hf.prodMk tendsto_map) tendsto_mul_nhds_zero_prod_of_disjoint_cocompact hg

/--
theorem `Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left` / 定理 `Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left`

English:
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left
  statement: {f g : α -> M} {l : Filter α}
  proof: .comp (tendsto_map.prodMk hg) tendsto_mul_prod_nhds_zero_of_disjoint_cocompact hf

中文:
定理 Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left
  结论: {f g : α -> M} {l : Filter α}
  证明: .comp (tendsto_map.prodMk hg) tendsto_mul_prod_nhds_zero_of_disjoint_cocompact hf

Depends on / 依赖: prodMk, tendsto_map, tendsto_map.prodMk, tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
-/
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left {f g : α -> M} {l : Filter α}
    (hf : Disjoint (map f l) (cocompact M)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
.comp (tendsto_map.prodMk hg) tendsto_mul_prod_nhds_zero_of_disjoint_cocompact hf

/--
theorem `tendsto_mul_cocompact_nhds_zero` / 定理 `tendsto_mul_cocompact_nhds_zero`

English:
theorem tendsto_mul_cocompact_nhds_zero
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  set l : Filter (M × M) := map (Prod.map f g) (cocompact (α × β)) with l_def
  set K : Set (M × M) := (insert 0 (range f)) ×ˢ (insert 0 (range g))
  have K_compact : IsCompact K := .prod (hf.isCompact_insert_range_of_cocompact f_cont)
    (hg.isCompact_insert_range_of_cocompact g_cont)
have K_me

中文:
定理 tendsto_mul_cocompact_nhds_zero
  结论: [TopologicalSpace α] [TopologicalSpace β]
  证明: by
  set l : Filter (M × M) := map (Prod.map f g) (cocompact (α × β)) with l_def
  set K : Set (M × M) := (insert 0 (range f)) ×ˢ (insert 0 (range g))
  have K_compact : IsCompact K := .prod (hf.isCompact_insert_range_of_cocompact f_cont)
    (hg.isCompact_insert_range_of_cocompact g_cont)
have K_me

Depends on / 依赖: Disjoint, Filter, IsCompact, K_compact, K_mem_l, Prod.map, cocompact, disjoint_co, eventually_map, eventually_map.mpr, f_cont, g_cont, hf.isCompact_insert_range_of_cocompact, hg.isCompact_insert_range_of_cocompact, insert, isCompact_insert_range_of_cocompact, l_compact, l_def, mem_insert_of_mem, mem_range_self
-/
theorem tendsto_mul_cocompact_nhds_zero [TopologicalSpace α] [TopologicalSpace β]
    {f : α -> M} {g : β -> M} (f_cont : Continuous f) (g_cont : Continuous g)
    (hf : Tendsto f (cocompact α) (𝓝 0)) (hg : Tendsto g (cocompact β) (𝓝 0)) :
    Tendsto (fun i : α × β => f i.1 * g i.2) (cocompact (α × β)) (𝓝 0) := by
  set l : Filter (M × M) := map (Prod.map f g) (cocompact (α × β)) with l_def
  set K : Set (M × M) := (insert 0 (range f)) ×ˢ (insert 0 (range g))
  have K_compact : IsCompact K := .prod (hf.isCompact_insert_range_of_cocompact f_cont)
    (hg.isCompact_insert_range_of_cocompact g_cont)
have K_mem_l : K in l := eventually_map.mpr .of_forall fun ⟨x, y⟩ =>
    ⟨mem_insert_of_mem _ (mem_range_self _), mem_insert_of_mem _ (mem_range_self _)⟩
  have l_compact : Disjoint l (cocompact (M × M)) := by
    rw [disjoint_cocompact_right]
    exact ⟨K, K_mem_l, K_compact⟩
  have l_le_coprod : l <= (𝓝 0).coprod (𝓝 0) := by
    rw [l_def]; rw [← coprod_cocompact]
    exact hf.prodMap_coprod hg
.comp tendsto_map exact tendsto_mul_nhds_zero_of_disjoint_cocompact l_compact l_le_coprod

/--
theorem `tendsto_mul_cofinite_nhds_zero` / 定理 `tendsto_mul_cofinite_nhds_zero`

English:
theorem tendsto_mul_cofinite_nhds_zero
  statement: {f : α -> M} {g : β -> M}
  proof: by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := discreteTopology_bot α
  let : TopologicalSpace β := ⊥
  have : DiscreteTopology β := discreteTopology_bot β
  rw [← cocompact_eq_cofinite] at *
  exact tendsto_mul_cocompact_nhds_zero
    continuous_of_discreteTopology continuous_of_

中文:
定理 tendsto_mul_cofinite_nhds_zero
  结论: {f : α -> M} {g : β -> M}
  证明: by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := discreteTopology_bot α
  let : TopologicalSpace β := ⊥
  have : DiscreteTopology β := discreteTopology_bot β
  rw [← cocompact_eq_cofinite] at *
  exact tendsto_mul_cocompact_nhds_zero
    continuous_of_discreteTopology continuous_of_

Depends on / 依赖: DiscreteTopology, TopologicalSpace, cocompact_eq_cofinite, continuous_of_discreteTopology, discreteTopology_bot, tendsto_mul_cocompact_nhds_zero
-/
theorem tendsto_mul_cofinite_nhds_zero {f : α -> M} {g : β -> M}
    (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun i : α × β => f i.1 * g i.2) cofinite (𝓝 0) := by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := discreteTopology_bot α
  let : TopologicalSpace β := ⊥
  have : DiscreteTopology β := discreteTopology_bot β
  rw [← cocompact_eq_cofinite] at *
  exact tendsto_mul_cocompact_nhds_zero
    continuous_of_discreteTopology continuous_of_discreteTopology hf hg

end MulZeroClass

section GroupWithZero

/--
lemma `GroupWithZero.isOpen_singleton_zero` / 引理 `GroupWithZero.isOpen_singleton_zero`

English:
lemma GroupWithZero.isOpen_singleton_zero
  statement: [GroupWithZero M] [TopologicalSpace M]
  proof: by
  obtain ⟨U, hU, h0U, h1U⟩ := t1Space_iff_exists_open.mp ‹_› zero_ne_one
  obtain ⟨W, hW, hW'⟩ := exists_mem_nhds_zero_mul_subset isCompact_univ (hU.mem_nhds h0U)
  by_cases H : exists x != 0, x in W
  · obtain ⟨x, hx, hxW⟩ := H
    cases h1U (hW' (by simpa [hx] using Set.mul_mem_mul (Set.mem_uni

中文:
引理 GroupWithZero.isOpen_singleton_zero
  结论: [GroupWithZero M] [TopologicalSpace M]
  证明: by
  obtain ⟨U, hU, h0U, h1U⟩ := t1Space_iff_exists_open.mp ‹_› zero_ne_one
  obtain ⟨W, hW, hW'⟩ := exists_mem_nhds_zero_mul_subset isCompact_univ (hU.mem_nhds h0U)
  by_cases H : exists x != 0, x in W
  · obtain ⟨x, hx, hxW⟩ := H
    cases h1U (hW' (by simpa [hx] using Set.mul_mem_mul (Set.mem_uni

Depends on / 依赖: Set.mem_univ, Set.mul_mem_mul, exists_mem_nhds_zero_mul_subset, hU.mem_nhds, isCompact_univ, isOpen_iff_mem_nhds, mem_nhds, mem_of_mem_nhds, mem_univ, mul_mem_mul, not_imp_not, subset_antisymm, t1Space_iff_exists_open, t1Space_iff_exists_open.mp, zero_ne_one
-/
lemma GroupWithZero.isOpen_singleton_zero [GroupWithZero M] [TopologicalSpace M]
    [ContinuousMul M] [CompactSpace M] [T1Space M] :
    IsOpen {(0 : M)} := by
  obtain ⟨U, hU, h0U, h1U⟩ := t1Space_iff_exists_open.mp ‹_› zero_ne_one
  obtain ⟨W, hW, hW'⟩ := exists_mem_nhds_zero_mul_subset isCompact_univ (hU.mem_nhds h0U)
  by_cases H : exists x != 0, x in W
  · obtain ⟨x, hx, hxW⟩ := H
    cases h1U (hW' (by simpa [hx] using Set.mul_mem_mul (Set.mem_univ x⁻¹) hxW))
  · obtain rfl : W = {0} := subset_antisymm
      (by simpa [not_imp_not] using H) (by simpa using mem_of_mem_nhds hW)
    simpa [isOpen_iff_mem_nhds]

end GroupWithZero

section MulOneClass

variable [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

@[to_additive exists_open_nhds_zero_half]
/--
theorem `exists_open_nhds_one_split` / 定理 `exists_open_nhds_one_split`

English:
theorem exists_open_nhds_one_split
  given: {s : Set M} (hs : s in 𝓝 (1 : M))
  proof: by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s in 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using! hs)
  simpa only [prod_subset_iff] using! exists_nhds_square this

@[to_additive exists_nhds_zero_half]

中文:
定理 exists_open_nhds_one_split
  条件: {s : Set M} (hs : s in 𝓝 (1 : M))
  证明: by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s in 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using! hs)
  simpa only [prod_subset_iff] using! exists_nhds_square this

@[to_additive exists_nhds_zero_half]

Depends on / 依赖: exists_nhds_square, one_mul, prod_subset_iff, tendsto_mul
-/
theorem exists_open_nhds_one_split {s : Set M} (hs : s in 𝓝 (1 : M)) :
    exists V : Set M, IsOpen V ∧ (1 : M) in V ∧ forall v in V, forall w in V, v * w in s := by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s in 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using! hs)
  simpa only [prod_subset_iff] using! exists_nhds_square this

@[to_additive exists_nhds_zero_half]
/--
theorem `exists_nhds_one_split` / 定理 `exists_nhds_one_split`

English:
theorem exists_nhds_one_split
  given: {s : Set M} (hs : s in 𝓝 (1 : M))
  proof: let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

中文:
定理 exists_nhds_one_split
  条件: {s : Set M} (hs : s in 𝓝 (1 : M))
  证明: let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, exists_open_nhds_one_split, mem_nhds
-/
theorem exists_nhds_one_split {s : Set M} (hs : s in 𝓝 (1 : M)) :
    exists V in 𝓝 (1 : M), forall v in V, forall w in V, v * w in s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `V * V ⊆ U`. -/
@[to_additive /-- Given an open neighborhood `U` of `0` there is an open neighborhood `V` of `0`
  such that `V + V ⊆ U`. -/]
/--
theorem `exists_open_nhds_one_mul_subset` / 定理 `exists_open_nhds_one_mul_subset`

English:
theorem exists_open_nhds_one_mul_subset
  given: {U : Set M} (hU : U in 𝓝 (1 : M))
  proof: by
  simpa only [mul_subset_iff] using exists_open_nhds_one_split hU

@[to_additive]

中文:
定理 exists_open_nhds_one_mul_subset
  条件: {U : Set M} (hU : U in 𝓝 (1 : M))
  证明: by
  simpa only [mul_subset_iff] using exists_open_nhds_one_split hU

@[to_additive]

Depends on / 依赖: exists_open_nhds_one_split, mul_subset_iff
-/
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U in 𝓝 (1 : M)) :
    exists V : Set M, IsOpen V ∧ (1 : M) in V ∧ V * V subseteq U := by
  simpa only [mul_subset_iff] using exists_open_nhds_one_split hU

@[to_additive]
/--
theorem `Filter.HasBasis.mul_self` / 定理 `Filter.HasBasis.mul_self`

English:
theorem Filter.HasBasis.mul_self
  given: {p : ι -> Prop} {s : ι -> Set M} (h : (𝓝 1).HasBasis p s)
  proof: by
  rw [← nhds_mul_nhds_one]; rw [← map₂_mul]; rw [← map_uncurry_prod]
  simpa only [← image_mul_prod] using! h.prod_self.map _

中文:
定理 Filter.HasBasis.mul_self
  条件: {p : ι -> 命题} {s : ι -> Set M} (h : (𝓝 1).HasBasis p s)
  证明: by
  rw [← nhds_mul_nhds_one]; rw [← map₂_mul]; rw [← map_uncurry_prod]
  simpa only [← image_mul_prod] using! h.prod_self.map _

Depends on / 依赖: h.prod_self.map, image_mul_prod, map_uncurry_prod, nhds_mul_nhds_one, prod_self
-/
theorem Filter.HasBasis.mul_self {p : ι -> Prop} {s : ι -> Set M} (h : (𝓝 1).HasBasis p s) :
    (𝓝 1).HasBasis p fun i => s i * s i := by
  rw [← nhds_mul_nhds_one]; rw [← map₂_mul]; rw [← map_uncurry_prod]
  simpa only [← image_mul_prod] using! h.prod_self.map _

end MulOneClass

section ContinuousMul

section Semigroup

variable [TopologicalSpace M] [Semigroup M] [SeparatelyContinuousMul M]

@[to_additive]
/--
theorem `Subsemigroup.top_closure_mul_self_subset` / 定理 `Subsemigroup.top_closure_mul_self_subset`

English:
theorem Subsemigroup.top_closure_mul_self_subset
  given: (s : Subsemigroup M)
  proof: image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const
      hx hy fun _ ha _ hb => s.mul_mem ha hb

中文:
定理 Subsemigroup.top_closure_mul_self_subset
  条件: (s : Subsemigroup M)
  证明: image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const
      hx hy fun _ ha _ hb => s.mul_mem ha hb

Depends on / 依赖: continuous_const_mul, continuous_mul_const, image2_subset_iff, mul_mem, s.mul_mem
-/
theorem Subsemigroup.top_closure_mul_self_subset (s : Subsemigroup M) :
    _root_.closure (s : Set M) * _root_.closure s subseteq _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const
      hx hy fun _ ha _ hb => s.mul_mem ha hb

/-- The (topological-space) closure of a subsemigroup of a space `M` with `ContinuousMul` is
itself a subsemigroup. -/
@[to_additive /-- The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid. -/]
/--
Definition of `Subsemigroup.topologicalClosure` / `Subsemigroup.topologicalClosure` 的定义

English:
definition Subsemigroup.topologicalClosure
  signature: (s : Subsemigroup M)
  body: _root_.closure (s : Set M)
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]

中文:
定义 Subsemigroup.topologicalClosure
  签名: (s : Subsemigroup M)
  定义体: _root_.closure (s : Set M)
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]

Depends on / 依赖: _root_, _root_.closure, closure
-/
def Subsemigroup.topologicalClosure (s : Subsemigroup M) : Subsemigroup M where
  carrier := _root_.closure (s : Set M)
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]
/--
theorem `Subsemigroup.coe_topologicalClosure` / 定理 `Subsemigroup.coe_topologicalClosure`

English:
theorem Subsemigroup.coe_topologicalClosure
  given: (s : Subsemigroup M)
  proof: rfl

@[to_additive]

中文:
定理 Subsemigroup.coe_topologicalClosure
  条件: (s : Subsemigroup M)
  证明: rfl

@[to_additive]
-/
theorem Subsemigroup.coe_topologicalClosure (s : Subsemigroup M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
/--
theorem `Subsemigroup.le_topologicalClosure` / 定理 `Subsemigroup.le_topologicalClosure`

English:
theorem Subsemigroup.le_topologicalClosure
  given: (s : Subsemigroup M)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

@[to_additive]

中文:
定理 Subsemigroup.le_topologicalClosure
  条件: (s : Subsemigroup M)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

@[to_additive]

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem Subsemigroup.le_topologicalClosure (s : Subsemigroup M) : s <= s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
/--
theorem `Subsemigroup.isClosed_topologicalClosure` / 定理 `Subsemigroup.isClosed_topologicalClosure`

English:
theorem Subsemigroup.isClosed_topologicalClosure
  given: (s : Subsemigroup M)
  proof: isClosed_closure

@[to_additive]

中文:
定理 Subsemigroup.isClosed_topologicalClosure
  条件: (s : Subsemigroup M)
  证明: isClosed_closure

@[to_additive]

Depends on / 依赖: isClosed_closure
-/
theorem Subsemigroup.isClosed_topologicalClosure (s : Subsemigroup M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

@[to_additive]
/--
theorem `Subsemigroup.topologicalClosure_minimal` / 定理 `Subsemigroup.topologicalClosure_minimal`

English:
theorem Subsemigroup.topologicalClosure_minimal
  statement: (s : Subsemigroup M) {t : Subsemigroup M}
  proof: closure_minimal h ht

@[to_additive (attr := gcongr)]

中文:
定理 Subsemigroup.topologicalClosure_minimal
  结论: (s : Subsemigroup M) {t : Subsemigroup M}
  证明: closure_minimal h ht

@[to_additive (attr := gcongr)]

Depends on / 依赖: closure_minimal
-/
theorem Subsemigroup.topologicalClosure_minimal (s : Subsemigroup M) {t : Subsemigroup M}
    (h : s <= t) (ht : IsClosed (t : Set M)) : s.topologicalClosure <= t := closure_minimal h ht

@[to_additive (attr := gcongr)]
/--
theorem `Subsemigroup.topologicalClosure_mono` / 定理 `Subsemigroup.topologicalClosure_mono`

English:
theorem Subsemigroup.topologicalClosure_mono
  given: {s t : Subsemigroup M} (h : s <= t)
  proof: _root_.closure_mono h

中文:
定理 Subsemigroup.topologicalClosure_mono
  条件: {s t : Subsemigroup M} (h : s <= t)
  证明: _root_.closure_mono h

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem Subsemigroup.topologicalClosure_mono {s t : Subsemigroup M} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

/-- If a subsemigroup of a topological semigroup is commutative, then so is its topological
closure.

See note [reducible non-instances] -/
@[to_additive /-- If a submonoid of an additive topological monoid is commutative, then so is its
topological closure.

See note [reducible non-instances] -/]
/--
Definition of `Subsemigroup.commSemigroupTopologicalClosure` / `Subsemigroup.commSemigroupTopologicalClosure` 的定义

English:
abbreviation Subsemigroup.commSemigroupTopologicalClosure
  signature: [T2Space M] (s : Subsemigroup M)
  body: { MulMemClass.toSemigroup s.topologicalClosure with
    mul_comm :=
      have : forall x in s, forall y in s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
Subtype.ext by
        refine eqOn_closure₂' this ?_ ?_ ?_ ?_ x hx y hy
   

中文:
缩写 Subsemigroup.commSemigroupTopologicalClosure
  签名: [T2Space M] (s : Subsemigroup M)
  定义体: { MulMemClass.toSemigroup s.topologicalClosure with
    mul_comm :=
      have : forall x in s, forall y in s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
Subtype.ext by
        refine eqOn_closure₂' this ?_ ?_ ?_ ?_ x hx y hy
   

Depends on / 依赖: MulMemClass, MulMemClass.toSemigroup, Subtype, Subtype.ext, Subtype.val, all_goals, congr_arg, fun_prop, mul_comm, s.topologicalClosure, toSemigroup, topologicalClosure
-/
abbrev Subsemigroup.commSemigroupTopologicalClosure [T2Space M] (s : Subsemigroup M)
    (hs : forall x y : s, x * y = y * x) : CommSemigroup s.topologicalClosure :=
  { MulMemClass.toSemigroup s.topologicalClosure with
    mul_comm :=
      have : forall x in s, forall y in s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
Subtype.ext by
        refine eqOn_closure₂' this ?_ ?_ ?_ ?_ x hx y hy
        all_goals fun_prop }

@[to_additive]
/--
theorem `IsCompact.mul` / 定理 `IsCompact.mul`

English:
theorem IsCompact.mul
  statement: [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
  proof: by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul

中文:
定理 IsCompact.mul
  结论: [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
  证明: by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul

Depends on / 依赖: continuous_mul, hs.prod, image_mul_prod
-/
theorem IsCompact.mul [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul

end Semigroup

variable [TopologicalSpace M] [Monoid M]

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul M]

@[to_additive]
/--
theorem `Submonoid.top_closure_mul_self_subset` / 定理 `Submonoid.top_closure_mul_self_subset`

English:
theorem Submonoid.top_closure_mul_self_subset
  given: (s : Submonoid M)
  proof: image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const hx hy
      fun _ ha _ hb => s.mul_mem ha hb

@[to_additive]

中文:
定理 Submonoid.top_closure_mul_self_subset
  条件: (s : Submonoid M)
  证明: image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const hx hy
      fun _ ha _ hb => s.mul_mem ha hb

@[to_additive]

Depends on / 依赖: continuous_const_mul, continuous_mul_const, image2_subset_iff, mul_mem, s.mul_mem
-/
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s subseteq _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const hx hy
      fun _ ha _ hb => s.mul_mem ha hb

@[to_additive]
/--
theorem `Submonoid.top_closure_mul_self_eq` / 定理 `Submonoid.top_closure_mul_self_eq`

English:
theorem Submonoid.top_closure_mul_self_eq
  given: (s : Submonoid M)
  proof: Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, hx, 1, _root_.subset_closure s.one_mem, mul_one _⟩

中文:
定理 Submonoid.top_closure_mul_self_eq
  条件: (s : Submonoid M)
  证明: Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, hx, 1, _root_.subset_closure s.one_mem, mul_one _⟩

Depends on / 依赖: Subset, Subset.antisymm, _root_, _root_.subset_closure, antisymm, mul_one, one_mem, s.one_mem, s.top_closure_mul_self_subset, subset_closure, top_closure_mul_self_subset
-/
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s = _root_.closure s :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, hx, 1, _root_.subset_closure s.one_mem, mul_one _⟩

/-- The (topological-space) closure of a submonoid of a space `M` with `ContinuousMul` is
itself a submonoid. -/
@[to_additive /-- The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid. -/]
/--
Definition of `Submonoid.topologicalClosure` / `Submonoid.topologicalClosure` 的定义

English:
definition Submonoid.topologicalClosure
  signature: (s : Submonoid M)
  body: _root_.closure (s : Set M)
  one_mem' := _root_.subset_closure s.one_mem
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]

中文:
定义 Submonoid.topologicalClosure
  签名: (s : Submonoid M)
  定义体: _root_.closure (s : Set M)
  one_mem' := _root_.subset_closure s.one_mem
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]

Depends on / 依赖: _root_, _root_.closure, closure
-/
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M where
  carrier := _root_.closure (s : Set M)
  one_mem' := _root_.subset_closure s.one_mem
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]
/--
theorem `Submonoid.coe_topologicalClosure` / 定理 `Submonoid.coe_topologicalClosure`

English:
theorem Submonoid.coe_topologicalClosure
  given: (s : Submonoid M)
  proof: rfl

@[to_additive]

中文:
定理 Submonoid.coe_topologicalClosure
  条件: (s : Submonoid M)
  证明: rfl

@[to_additive]
-/
theorem Submonoid.coe_topologicalClosure (s : Submonoid M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
/--
theorem `Submonoid.le_topologicalClosure` / 定理 `Submonoid.le_topologicalClosure`

English:
theorem Submonoid.le_topologicalClosure
  given: (s : Submonoid M)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

@[to_additive]

中文:
定理 Submonoid.le_topologicalClosure
  条件: (s : Submonoid M)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

@[to_additive]

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem Submonoid.le_topologicalClosure (s : Submonoid M) : s <= s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
/--
theorem `Submonoid.isClosed_topologicalClosure` / 定理 `Submonoid.isClosed_topologicalClosure`

English:
theorem Submonoid.isClosed_topologicalClosure
  given: (s : Submonoid M)
  proof: isClosed_closure

@[to_additive]

中文:
定理 Submonoid.isClosed_topologicalClosure
  条件: (s : Submonoid M)
  证明: isClosed_closure

@[to_additive]

Depends on / 依赖: isClosed_closure
-/
theorem Submonoid.isClosed_topologicalClosure (s : Submonoid M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

@[to_additive]
/--
theorem `Submonoid.topologicalClosure_minimal` / 定理 `Submonoid.topologicalClosure_minimal`

English:
theorem Submonoid.topologicalClosure_minimal
  statement: (s : Submonoid M) {t : Submonoid M} (h : s <= t)
  proof: closure_minimal h ht

@[to_additive (attr := gcongr)]

中文:
定理 Submonoid.topologicalClosure_minimal
  结论: (s : Submonoid M) {t : Submonoid M} (h : s <= t)
  证明: closure_minimal h ht

@[to_additive (attr := gcongr)]

Depends on / 依赖: closure_minimal
-/
theorem Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (h : s <= t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure <= t := closure_minimal h ht

@[to_additive (attr := gcongr)]
/--
theorem `Submonoid.topologicalClosure_mono` / 定理 `Submonoid.topologicalClosure_mono`

English:
theorem Submonoid.topologicalClosure_mono
  given: {s t : Submonoid M} (h : s <= t)
  proof: _root_.closure_mono h

中文:
定理 Submonoid.topologicalClosure_mono
  条件: {s t : Submonoid M} (h : s <= t)
  证明: _root_.closure_mono h

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem Submonoid.topologicalClosure_mono {s t : Submonoid M} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive /-- If a submonoid of an additive topological monoid is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/]
/--
Definition of `Submonoid.commMonoidTopologicalClosure` / `Submonoid.commMonoidTopologicalClosure` 的定义

English:
abbreviation Submonoid.commMonoidTopologicalClosure
  signature: [T2Space M] (s : Submonoid M)
  body: { s.topologicalClosure.toMonoid, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

中文:
缩写 Submonoid.commMonoidTopologicalClosure
  签名: [T2Space M] (s : Submonoid M)
  定义体: { s.topologicalClosure.toMonoid, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

Depends on / 依赖: commSemigroupTopologicalClosure, s.toSubsemigroup.commSemigroupTopologicalClosure, s.topologicalClosure.toMonoid, toMonoid, toSubsemigroup, topologicalClosure
-/
abbrev Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M)
    (hs : forall x y : s, x * y = y * x) : CommMonoid s.topologicalClosure :=
  { s.topologicalClosure.toMonoid, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

/--
theorem `Filter.tendsto_cocompact_mul_left` / 定理 `Filter.tendsto_cocompact_mul_left`

English:
theorem Filter.tendsto_cocompact_mul_left
  given: {a b : M} (ha : b * a = 1)
  proof: by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_const_mul b))
  convert! Filter.tendsto_id
  ext x
  simp [← mul_assoc, ha]

中文:
定理 Filter.tendsto_cocompact_mul_left
  条件: {a b : M} (ha : b * a = 1)
  证明: by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_const_mul b))
  convert! Filter.tendsto_id
  ext x
  simp [← mul_assoc, ha]

Depends on / 依赖: Filter, Filter.Tendsto.of_tendsto_comp, Filter.comap_cocompact_le, Filter.tendsto_id, Tendsto, comap_cocompact_le, continuous_const_mul, convert, mul_assoc, of_tendsto_comp, tendsto_id
-/
theorem Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
    Filter.Tendsto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_const_mul b))
  convert! Filter.tendsto_id
  ext x
  simp [← mul_assoc, ha]

/--
theorem `Filter.tendsto_cocompact_mul_right` / 定理 `Filter.tendsto_cocompact_mul_right`

English:
theorem Filter.tendsto_cocompact_mul_right
  given: {a b : M} (ha : a * b = 1)
  proof: by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_const b))
  simp only [comp_mul_right, ha, mul_one]
  exact Filter.tendsto_id

中文:
定理 Filter.tendsto_cocompact_mul_right
  条件: {a b : M} (ha : a * b = 1)
  证明: by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_const b))
  simp only [comp_mul_right, ha, mul_one]
  exact Filter.tendsto_id

Depends on / 依赖: Filter, Filter.Tendsto.of_tendsto_comp, Filter.comap_cocompact_le, Filter.tendsto_id, Tendsto, comap_cocompact_le, comp_mul_right, continuous_mul_const, mul_one, of_tendsto_comp, tendsto_id
-/
theorem Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
    Filter.Tendsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_const b))
  simp only [comp_mul_right, ha, mul_one]
  exact Filter.tendsto_id

end SeparatelyContinuousMul

variable [ContinuousMul M]

@[to_additive exists_nhds_zero_quarter]
/--
theorem `exists_nhds_one_split4` / 定理 `exists_nhds_one_split4`

English:
theorem exists_nhds_one_split4
  given: {u : Set M} (hu : u in 𝓝 (1 : M))
  proof: by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

@[to_additive]

中文:
定理 exists_nhds_one_split4
  条件: {u : Set M} (hu : u in 𝓝 (1 : M))
  证明: by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

@[to_additive]

Depends on / 依赖: exists_nhds_one_split, mul_assoc, s_in, t_in, v_in, w_in
-/
theorem exists_nhds_one_split4 {u : Set M} (hu : u in 𝓝 (1 : M)) :
    exists V in 𝓝 (1 : M), forall {v w s t}, v in V -> w in V -> s in V -> t in V -> v * w * s * t in u := by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

@[to_additive]
/--
theorem `tendsto_list_prod` / 定理 `tendsto_list_prod`

English:
theorem tendsto_list_prod
  given: {f : ι -> α -> M} {x : Filter α} {a : ι -> M}

中文:
定理 tendsto_list_prod
  条件: {f : ι -> α -> M} {x : Filter α} {a : ι -> M}
-/
theorem tendsto_list_prod {f : ι -> α -> M} {x : Filter α} {a : ι -> M} :
    forall l : List ι,
      (forall i in l, Tendsto (f i) x (𝓝 (a i))) ->
        Tendsto (fun b => (l.map fun c => f c b).prod) x (𝓝 (l.map a).prod)
  | [], _ => by simp [tendsto_const_nhds]
  | f::l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact
      (h f List.mem_cons_self).mul
        (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_mem _ hc))

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_list_prod` / 定理 `continuous_list_prod`

English:
theorem continuous_list_prod
  given: {f : ι -> X -> M} (l : List ι) (h : forall i in l, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x

@[to_additive]

中文:
定理 continuous_list_prod
  条件: {f : ι -> X -> M} (l : List ι) (h : 对任意 i in l, Continuous (f i))
  证明: continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x

@[to_additive]

Depends on / 依赖: continuous_iff_continuousAt, tendsto_list_prod
-/
theorem continuous_list_prod {f : ι -> X -> M} (l : List ι) (h : forall i in l, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).prod :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x

@[to_additive]
/--
theorem `continuousOn_list_prod` / 定理 `continuousOn_list_prod`

English:
theorem continuousOn_list_prod
  statement: {f : ι -> X -> M} (l : List ι) {t : Set X}
  proof: by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx]
  refine tendsto_list_prod _ fun i hi => ?_
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx] at h
  exact h

@[to_additive (attr := continuity)]

中文:
定理 continuousOn_list_prod
  结论: {f : ι -> X -> M} (l : List ι) {t : Set X}
  证明: by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx]
  refine tendsto_list_prod _ fun i hi => ?_
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx] at h
  exact h

@[to_additive (attr := continuity)]

Depends on / 依赖: continuousWithinAt_iff_continuousAt_domRestrict, specialize, tendsto_list_prod
-/
theorem continuousOn_list_prod {f : ι -> X -> M} (l : List ι) {t : Set X}
    (h : forall i in l, ContinuousOn (f i) t) :
    ContinuousOn (fun a => (l.map fun i => f i a).prod) t := by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx]
  refine tendsto_list_prod _ fun i hi => ?_
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx] at h
  exact h

@[to_additive (attr := continuity)]
/--
theorem `continuous_pow` / 定理 `continuous_pow`

English:
theorem continuous_pow
  statement: forall n : Nat, Continuous fun a : M => a ^ n

中文:
定理 continuous_pow
  结论: 对任意 n : 自然数, Continuous fun a : M => a ^ n
-/
theorem continuous_pow : forall n : Nat, Continuous fun a : M => a ^ n
  | 0 => by simpa using continuous_const
  | k + 1 => by
    simp only [pow_succ']
    exact continuous_id.mul (continuous_pow _)

/--
Instance `AddMonoid.continuousConstSMul_nat` / 实例 `AddMonoid.continuousConstSMul_nat`

English:
instance AddMonoid.continuousConstSMul_nat
  signature: {A} [AddMonoid A] [TopologicalSpace A]
  body: ⟨continuous_nsmul⟩

中文:
实例 AddMonoid.continuousConstSMul_nat
  签名: {A} [AddMonoid A] [TopologicalSpace A]
  定义体: ⟨continuous_nsmul⟩

Depends on / 依赖: continuous_nsmul
-/
instance AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousConstSMul Nat A :=
  ⟨continuous_nsmul⟩

/--
Instance `AddMonoid.continuousSMul_nat` / 实例 `AddMonoid.continuousSMul_nat`

English:
instance AddMonoid.continuousSMul_nat
  signature: {A} [AddMonoid A] [TopologicalSpace A]
  body: ⟨continuous_prod_of_discrete_left.mpr continuous_nsmul⟩

中文:
实例 AddMonoid.continuousSMul_nat
  签名: {A} [AddMonoid A] [TopologicalSpace A]
  定义体: ⟨continuous_prod_of_discrete_left.mpr continuous_nsmul⟩

Depends on / 依赖: continuous_nsmul, continuous_prod_of_discrete_left, continuous_prod_of_discrete_left.mpr
-/
instance AddMonoid.continuousSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousSMul Nat A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_nsmul⟩

-- We register `Continuous.pow` as a `continuity` lemma with low penalty (so
-- `continuity` will try it before other `continuity` lemmas). This is a
-- workaround for goals of the form `Continuous fun x => x ^ 2`, where
-- `continuity` applies `Continuous.mul` since the goal is defeq to
-- `Continuous fun x => x * x`.
--
-- To properly fix this, we should make sure that `continuity` applies its
-- lemmas with reducible transparency, preventing the unfolding of `^`. But this
-- is quite an invasive change.
@[to_fun (attr := to_additive (attr := aesop safe -100 (rule_sets := [Continuous]), fun_prop))]
/--
theorem `Continuous.pow` / 定理 `Continuous.pow`

English:
theorem Continuous.pow
  given: {f : X -> M} (h : Continuous f) (n : Nat)
  statement: Continuous (f ^ n)
  proof: (continuous_pow n).comp h

@[to_additive]

中文:
定理 Continuous.pow
  条件: {f : X -> M} (h : Continuous f) (n : 自然数)
  结论: Continuous (f ^ n)
  证明: (continuous_pow n).comp h

@[to_additive]

Depends on / 依赖: continuous_pow
-/
theorem Continuous.pow {f : X -> M} (h : Continuous f) (n : Nat) : Continuous (f ^ n) :=
  (continuous_pow n).comp h

@[to_additive]
/--
theorem `continuousOn_pow` / 定理 `continuousOn_pow`

English:
theorem continuousOn_pow
  given: {s : Set M} (n : Nat)
  statement: ContinuousOn (fun (x : M) => x ^ n) s
  proof: (continuous_pow n).continuousOn

@[to_additive]

中文:
定理 continuousOn_pow
  条件: {s : Set M} (n : 自然数)
  结论: ContinuousOn (fun (x : M) => x ^ n) s
  证明: (continuous_pow n).continuousOn

@[to_additive]

Depends on / 依赖: continuousOn, continuous_pow
-/
theorem continuousOn_pow {s : Set M} (n : Nat) : ContinuousOn (fun (x : M) => x ^ n) s :=
  (continuous_pow n).continuousOn

@[to_additive]
/--
theorem `continuousAt_pow` / 定理 `continuousAt_pow`

English:
theorem continuousAt_pow
  given: (x : M) (n : Nat)
  statement: ContinuousAt (fun (x : M) => x ^ n) x
  proof: (continuous_pow n).continuousAt

@[to_additive]

中文:
定理 continuousAt_pow
  条件: (x : M) (n : 自然数)
  结论: ContinuousAt (fun (x : M) => x ^ n) x
  证明: (continuous_pow n).continuousAt

@[to_additive]

Depends on / 依赖: continuousAt, continuous_pow
-/
theorem continuousAt_pow (x : M) (n : Nat) : ContinuousAt (fun (x : M) => x ^ n) x :=
  (continuous_pow n).continuousAt

@[to_additive]
/--
theorem `Filter.Tendsto.pow` / 定理 `Filter.Tendsto.pow`

English:
theorem Filter.Tendsto.pow
  given: {l : Filter α} {f : α -> M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : Nat)
  proof: (continuousAt_pow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 Filter.Tendsto.pow
  条件: {l : Filter α} {f : α -> M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : 自然数)
  证明: (continuousAt_pow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: continuousAt_pow, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : Nat) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuousAt_pow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousWithinAt.pow` / 定理 `ContinuousWithinAt.pow`

English:
theorem ContinuousWithinAt.pow
  statement: {f : X -> M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
  proof: Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousWithinAt.pow
  结论: {f : X -> M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
  证明: Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.pow, Tendsto
-/
theorem ContinuousWithinAt.pow {f : X -> M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
    (n : Nat) : ContinuousWithinAt (f ^ n) s x :=
  Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousAt.pow` / 定理 `ContinuousAt.pow`

English:
theorem ContinuousAt.pow
  given: {f : X -> M} {x : X} (hf : ContinuousAt f x) (n : Nat)
  proof: Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousAt.pow
  条件: {f : X -> M} {x : X} (hf : ContinuousAt f x) (n : 自然数)
  证明: Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.pow, Tendsto
-/
theorem ContinuousAt.pow {f : X -> M} {x : X} (hf : ContinuousAt f x) (n : Nat) :
    ContinuousAt (f ^ n) x :=
  Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousOn.pow` / 定理 `ContinuousOn.pow`

English:
theorem ContinuousOn.pow
  given: {f : X -> M} {s : Set X} (hf : ContinuousOn f s) (n : Nat)
  proof: fun x hx => (hf x hx).pow n

中文:
定理 ContinuousOn.pow
  条件: {f : X -> M} {s : Set X} (hf : ContinuousOn f s) (n : 自然数)
  证明: fun x hx => (hf x hx).pow n
-/
theorem ContinuousOn.pow {f : X -> M} {s : Set X} (hf : ContinuousOn f s) (n : Nat) :
    ContinuousOn (f ^ n) s := fun x hx => (hf x hx).pow n

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instance applies when `R = A`, or when `[Algebra R A]` is available. -/
@[to_additive /-- If `R` acts on `A` via `A`, then continuous addition implies
continuous affine addition by constants. -/]
instance (priority := 100) IsScalarTower.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [SeparatelyContinuousMul A] :
    ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp +singlePass only [← smul_one_mul q (_ : A)]
    fun_prop

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instance applies when `R = Aᵐᵒᵖ`. -/
@[to_additive /-- If the action of `R` on `A` commutes with left-addition, then
continuous addition implies continuous affine addition by constants.

Notably, this instance applies when `R = Aᵃᵒᵖ`. -/]
instance (priority := 100) SMulCommClass.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [SMulCommClass R A A] [TopologicalSpace A] [SeparatelyContinuousMul A] :
    ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp +singlePass only [← mul_smul_one q (_ : A)]
    fun_prop

end ContinuousMul

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoid α] [ContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `Topology.Algebra.Group`,
because the predicate `ContinuousInv` has not yet been defined. -/
@[to_additive /-- If addition on an additive monoid is continuous, then addition on the additive
units of the monoid, with respect to the induced topology, is continuous.

Negation is also continuous, but we register this in a later file, `Topology.Algebra.Group`, because
the predicate `ContinuousNeg` has not yet been defined. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMul αˣ
  body: isInducing_embedProduct.continuousMul (embedProduct α)

中文:
实例 :
  签名: ContinuousMul αˣ
  定义体: isInducing_embedProduct.continuousMul (embedProduct α)

Depends on / 依赖: continuousMul, embedProduct, isInducing_embedProduct, isInducing_embedProduct.continuousMul
-/
instance : ContinuousMul αˣ := isInducing_embedProduct.continuousMul (embedProduct α)

end Units

@[to_additive (attr := fun_prop)]
/--
theorem `Continuous.units_map` / 定理 `Continuous.units_map`

English:
theorem Continuous.units_map
  statement: [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
  proof: Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

中文:
定理 Continuous.units_map
  结论: [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
  证明: Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

Depends on / 依赖: Units.continuous_coe_inv, Units.continuous_iff, Units.continuous_val, continuous_coe_inv, continuous_iff, continuous_val, hf.comp
-/
theorem Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M ->* N) (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

section

variable [TopologicalSpace M] [CommMonoid M]

@[to_additive]
/--
theorem `Submonoid.mem_nhds_one` / 定理 `Submonoid.mem_nhds_one`

English:
theorem Submonoid.mem_nhds_one
  given: (S : Submonoid M) (oS : IsOpen (S : Set M))
  proof: IsOpen.mem_nhds oS S.one_mem

中文:
定理 Submonoid.mem_nhds_one
  条件: (S : Submonoid M) (oS : IsOpen (S : Set M))
  证明: IsOpen.mem_nhds oS S.one_mem

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, S.one_mem, mem_nhds, one_mem
-/
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) :
    (S : Set M) in 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem

variable [ContinuousMul M]

@[to_additive]
/--
theorem `tendsto_multiset_prod` / 定理 `tendsto_multiset_prod`

English:
theorem tendsto_multiset_prod
  given: {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Multiset ι)
  proof: by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l

@[to_additive]

中文:
定理 tendsto_multiset_prod
  条件: {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Multiset ι)
  证明: by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l

@[to_additive]

Depends on / 依赖: tendsto_list_prod
-/
theorem tendsto_multiset_prod {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Multiset ι) :
    (forall i in s, Tendsto (f i) x (𝓝 (a i))) ->
      Tendsto (fun b => (s.map fun c => f c b).prod) x (𝓝 (s.map a).prod) := by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l

@[to_additive]
/--
theorem `tendsto_finsetProd` / 定理 `tendsto_finsetProd`

English:
theorem tendsto_finsetProd
  given: {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Finset ι)
  proof: tendsto_multiset_prod _

@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias tendsto_finset_prod := tendsto_finsetProd

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 tendsto_finsetProd
  条件: {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Finset ι)
  证明: tendsto_multiset_prod _

@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias tendsto_finset_prod := tendsto_finsetProd

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: tendsto_multiset_prod
-/
theorem tendsto_finsetProd {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Finset ι) :
    (forall i in s, Tendsto (f i) x (𝓝 (a i))) ->
      Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
  tendsto_multiset_prod _

@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias tendsto_finset_prod := tendsto_finsetProd

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_multiset_prod` / 定理 `continuous_multiset_prod`

English:
theorem continuous_multiset_prod
  given: {f : ι -> X -> M} (s : Multiset ι)
  proof: by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l

@[to_additive]

中文:
定理 continuous_multiset_prod
  条件: {f : ι -> X -> M} (s : Multiset ι)
  证明: by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l

@[to_additive]

Depends on / 依赖: continuous_list_prod
-/
theorem continuous_multiset_prod {f : ι -> X -> M} (s : Multiset ι) :
    (forall i in s, Continuous (f i)) -> Continuous fun a => (s.map fun i => f i a).prod := by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l

@[to_additive]
/--
theorem `continuousOn_multiset_prod` / 定理 `continuousOn_multiset_prod`

English:
theorem continuousOn_multiset_prod
  given: {f : ι -> X -> M} (s : Multiset ι) {t : Set X}
  proof: by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 continuousOn_multiset_prod
  条件: {f : ι -> X -> M} (s : Multiset ι) {t : Set X}
  证明: by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: continuousOn_list_prod
-/
theorem continuousOn_multiset_prod {f : ι -> X -> M} (s : Multiset ι) {t : Set X} :
    (forall i in s, ContinuousOn (f i) t) -> ContinuousOn (fun a => (s.map fun i => f i a).prod) t := by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_finsetProd` / 定理 `continuous_finsetProd`

English:
theorem continuous_finsetProd
  given: {f : ι -> X -> M} (s : Finset ι)
  proof: continuous_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuous_finset_sum := continuous_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuous_finset_prod := continuous_finsetProd

@[to_additive]

中文:
定理 continuous_finsetProd
  条件: {f : ι -> X -> M} (s : Finset ι)
  证明: continuous_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuous_finset_sum := continuous_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuous_finset_prod := continuous_finsetProd

@[to_additive]

Depends on / 依赖: continuous_multiset_prod
-/
theorem continuous_finsetProd {f : ι -> X -> M} (s : Finset ι) :
    (forall i in s, Continuous (f i)) -> Continuous fun a => ∏ i in s, f i a :=
  continuous_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuous_finset_sum := continuous_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuous_finset_prod := continuous_finsetProd

@[to_additive]
/--
theorem `continuousOn_finsetProd` / 定理 `continuousOn_finsetProd`

English:
theorem continuousOn_finsetProd
  given: {f : ι -> X -> M} (s : Finset ι) {t : Set X}
  proof: continuousOn_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuousOn_finset_sum := continuousOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuousOn_finset_prod := continuousOn_finsetProd

@[to_additive]

中文:
定理 continuousOn_finsetProd
  条件: {f : ι -> X -> M} (s : Finset ι) {t : Set X}
  证明: continuousOn_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuousOn_finset_sum := continuousOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuousOn_finset_prod := continuousOn_finsetProd

@[to_additive]

Depends on / 依赖: continuousOn_multiset_prod
-/
theorem continuousOn_finsetProd {f : ι -> X -> M} (s : Finset ι) {t : Set X} :
    (forall i in s, ContinuousOn (f i) t) -> ContinuousOn (fun a => ∏ i in s, f i a) t :=
  continuousOn_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuousOn_finset_sum := continuousOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuousOn_finset_prod := continuousOn_finsetProd

@[to_additive]
/--
theorem `eventuallyEq_prod` / 定理 `eventuallyEq_prod`

English:
theorem eventuallyEq_prod
  statement: {X M : Type*} [CommMonoid M] {s : Finset ι} {l : Filter X}
  proof: by
  replace hs : forallᶠ x in l, forall i in s, f i x = g i x := by rwa [eventually_all_finset]
  filter_upwards [hs] with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]

中文:
定理 eventuallyEq_prod
  结论: {X M : 类型} [CommMonoid M] {s : Finset ι} {l : Filter X}
  证明: by
  replace hs : forallᶠ x in l, forall i in s, f i x = g i x := by rwa [eventually_all_finset]
  filter_upwards [hs] with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]

Depends on / 依赖: Finset, Finset.prod_apply, Finset.prod_congr, eventually_all_finset, filter_upwards, prod_apply, prod_congr, replace
-/
theorem eventuallyEq_prod {X M : Type*} [CommMonoid M] {s : Finset ι} {l : Filter X}
    {f g : ι -> X -> M} (hs : forall i in s, f i =ᶠ[l] g i) : ∏ i in s, f i =ᶠ[l] ∏ i in s, g i := by
  replace hs : forallᶠ x in l, forall i in s, f i x = g i x := by rwa [eventually_all_finset]
  filter_upwards [hs] with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]

open Function

@[to_additive]
/--
theorem `LocallyFinite.exists_finset_mulSupport` / 定理 `LocallyFinite.exists_finset_mulSupport`

English:
theorem LocallyFinite.exists_finset_mulSupport
  statement: {M : Type*} [One M] {f : ι -> X -> M}
  proof: by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine ⟨hUf.toFinset, mem_of_superset hxU fun y hy i hi => ?_⟩
  rw [hUf.coe_toFinset]
  exact ⟨y, hi, hy⟩

@[to_additive]

中文:
定理 LocallyFinite.exists_finset_mulSupport
  结论: {M : 类型} [One M] {f : ι -> X -> M}
  证明: by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine ⟨hUf.toFinset, mem_of_superset hxU fun y hy i hi => ?_⟩
  rw [hUf.coe_toFinset]
  exact ⟨y, hi, hy⟩

@[to_additive]

Depends on / 依赖: coe_toFinset, hUf.coe_toFinset, hUf.toFinset, mem_of_superset, toFinset
-/
theorem LocallyFinite.exists_finset_mulSupport {M : Type*} [One M] {f : ι -> X -> M}
    (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) :
    exists I : Finset ι, forallᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) subseteq I := by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine ⟨hUf.toFinset, mem_of_superset hxU fun y hy i hi => ?_⟩
  rw [hUf.coe_toFinset]
  exact ⟨y, hi, hy⟩

@[to_additive]
/--
theorem `finprod_eventually_eq_prod` / 定理 `finprod_eventually_eq_prod`

English:
theorem finprod_eventually_eq_prod
  statement: {M : Type*} [CommMonoid M] {f : ι -> X -> M}
  proof: let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun _ hy => finprod_eq_prod_of_mulSupport_subset _ fun _ hi => hy hi⟩

@[to_additive]

中文:
定理 finprod_eventually_eq_prod
  结论: {M : 类型} [CommMonoid M] {f : ι -> X -> M}
  证明: let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun _ hy => finprod_eq_prod_of_mulSupport_subset _ fun _ hi => hy hi⟩

@[to_additive]

Depends on / 依赖: exists_finset_mulSupport, finprod_eq_prod_of_mulSupport_subset, hI.mono, hf.exists_finset_mulSupport
-/
theorem finprod_eventually_eq_prod {M : Type*} [CommMonoid M] {f : ι -> X -> M}
    (hf : LocallyFinite fun i => mulSupport (f i)) (x : X) :
    exists s : Finset ι, forallᶠ y in 𝓝 x, ∏ᶠ i, f i y = ∏ i in s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun _ hy => finprod_eq_prod_of_mulSupport_subset _ fun _ hi => hy hi⟩

@[to_additive]
/--
theorem `continuous_finprod` / 定理 `continuous_finprod`

English:
theorem continuous_finprod
  statement: {f : ι -> X -> M} (hc : forall i, Continuous (f i))
  proof: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine ContinuousAt.congr ?_ (EventuallyEq.symm hs)
  exact tendsto_finsetProd _ fun i _ => (hc i).continuousAt

@[to_additive]

中文:
定理 continuous_finprod
  结论: {f : ι -> X -> M} (hc : 对任意 i, Continuous (f i))
  证明: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine ContinuousAt.congr ?_ (EventuallyEq.symm hs)
  exact tendsto_finsetProd _ fun i _ => (hc i).continuousAt

@[to_additive]

Depends on / 依赖: ContinuousAt, ContinuousAt.congr, EventuallyEq, EventuallyEq.symm, continuousAt, continuous_iff_continuousAt, finprod_eventually_eq_prod, tendsto_finsetProd
-/
theorem continuous_finprod {f : ι -> X -> M} (hc : forall i, Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine ContinuousAt.congr ?_ (EventuallyEq.symm hs)
  exact tendsto_finsetProd _ fun i _ => (hc i).continuousAt

@[to_additive]
/--
theorem `continuous_finprod_cond` / 定理 `continuous_finprod_cond`

English:
theorem continuous_finprod_cond
  statement: {f : ι -> X -> M} {p : ι -> Prop} (hc : forall i, p i -> Continuous (f i))
  proof: by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

中文:
定理 continuous_finprod_cond
  结论: {f : ι -> X -> M} {p : ι -> 命题} (hc : 对任意 i, p i -> Continuous (f i))
  证明: by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, comp_injective, continuous_finprod, finprod_subtype_eq_finprod_cond, hf.comp_injective
-/
theorem continuous_finprod_cond {f : ι -> X -> M} {p : ι -> Prop} (hc : forall i, p i -> Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Continuous fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M) where
  body: @continuous_mul M _ _ _

中文:
实例 [TopologicalSpace
  签名: M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M) where
  定义体: @continuous_mul M _ _ _

Depends on / 依赖: continuous_mul
-/
instance [TopologicalSpace M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M) where
  continuous_add := @continuous_mul M _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M) where
  body: @continuous_add M _ _ _

中文:
实例 [TopologicalSpace
  签名: M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M) where
  定义体: @continuous_add M _ _ _

Depends on / 依赖: continuous_add
-/
instance [TopologicalSpace M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M) where
  continuous_mul := @continuous_add M _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: M] [Mul M] [SeparatelyContinuousMul M] :
  body: @continuous_const_mul M _ _ _
  continuous_add_const := @continuous_mul_const M _ _ _

中文:
实例 [TopologicalSpace
  签名: M] [Mul M] [SeparatelyContinuousMul M] :
  定义体: @continuous_const_mul M _ _ _
  continuous_add_const := @continuous_mul_const M _ _ _

Depends on / 依赖: continuous_const_mul
-/
instance [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M] :
    SeparatelyContinuousAdd (Additive M) where
  continuous_const_add := @continuous_const_mul M _ _ _
  continuous_add_const := @continuous_mul_const M _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: M] [Add M] [SeparatelyContinuousAdd M] :
  body: @continuous_const_add M _ _ _
  continuous_mul_const := @continuous_add_const M _ _ _

中文:
实例 [TopologicalSpace
  签名: M] [Add M] [SeparatelyContinuousAdd M] :
  定义体: @continuous_const_add M _ _ _
  continuous_mul_const := @continuous_add_const M _ _ _

Depends on / 依赖: continuous_const_add
-/
instance [TopologicalSpace M] [Add M] [SeparatelyContinuousAdd M] :
    SeparatelyContinuousMul (Multiplicative M) where
  continuous_const_mul := @continuous_const_add M _ _ _
  continuous_mul_const := @continuous_add_const M _ _ _

section LatticeOps

variable {ι' : Sort*} [Mul M]

@[to_additive]
/--
theorem `continuousMul_sInf` / 定理 `continuousMul_sInf`

English:
theorem continuousMul_sInf
  statement: {ts : Set (TopologicalSpace M)}
  proof: letI := sInf ts
  { continuous_mul :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }

@[to_additive]

中文:
定理 continuousMul_sInf
  结论: {ts : Set (TopologicalSpace M)}
  证明: letI := sInf ts
  { continuous_mul :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }

@[to_additive]

Depends on / 依赖: ContinuousMul, ContinuousMul.continuous_mul, continuous_mul, continuous_sInf_rng
-/
theorem continuousMul_sInf {ts : Set (TopologicalSpace M)}
    (h : forall t in ts, @ContinuousMul M t _) : @ContinuousMul M (sInf ts) _ :=
  letI := sInf ts
  { continuous_mul :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }

@[to_additive]
/--
theorem `continuousMul_iInf` / 定理 `continuousMul_iInf`

English:
theorem continuousMul_iInf
  statement: {ts : ι' -> TopologicalSpace M}
  proof: by
  rw [← sInf_range]
  exact continuousMul_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

中文:
定理 continuousMul_iInf
  结论: {ts : ι' -> TopologicalSpace M}
  证明: by
  rw [← sInf_range]
  exact continuousMul_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

Depends on / 依赖: Set.forall_mem_range.mpr, continuousMul_sInf, forall_mem_range, sInf_range
-/
theorem continuousMul_iInf {ts : ι' -> TopologicalSpace M}
    (h' : forall i, @ContinuousMul M (ts i) _) : @ContinuousMul M (⨅ i, ts i) _ := by
  rw [← sInf_range]
  exact continuousMul_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/--
theorem `continuousMul_inf` / 定理 `continuousMul_inf`

English:
theorem continuousMul_inf
  statement: {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
  proof: by
  rw [inf_eq_iInf]
  refine continuousMul_iInf fun b => ?_
  cases b <;> assumption

中文:
定理 continuousMul_inf
  结论: {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
  证明: by
  rw [inf_eq_iInf]
  refine continuousMul_iInf fun b => ?_
  cases b <;> assumption

Depends on / 依赖: continuousMul_iInf, inf_eq_iInf
-/
theorem continuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
    (h₂ : @ContinuousMul M t₂ _) : @ContinuousMul M (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousMul_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

namespace ContinuousMap

variable [Mul X] [SeparatelyContinuousMul X]

/-- The continuous map `fun y => y * x` -/
@[to_additive /-- The continuous map `fun y => y + x` -/]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (x : X)
  body: mk _ (continuous_mul_const x)

@[to_additive (attr := simp)]

中文:
定义 mulRight
  签名: (x : X)
  定义体: mk _ (continuous_mul_const x)

@[to_additive (attr := simp)]
-/
protected def mulRight (x : X) : C(X, X) :=
  mk _ (continuous_mul_const x)

@[to_additive (attr := simp)]
/--
theorem `coe_mulRight` / 定理 `coe_mulRight`

English:
theorem coe_mulRight
  given: (x : X)
  statement: ⇑(ContinuousMap.mulRight x) = fun y => y * x
  proof: rfl

@[to_additive]

中文:
定理 coe_mulRight
  条件: (x : X)
  结论: ⇑(ContinuousMap.mulRight x) = fun y => y * x
  证明: rfl

@[to_additive]
-/
theorem coe_mulRight (x : X) : ⇑(ContinuousMap.mulRight x) = fun y => y * x :=
  rfl

@[to_additive]
/--
lemma `mulRight_mul` / 引理 `mulRight_mul`

English:
lemma mulRight_mul
  statement: {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
  proof: by
  ext; simp [mul_assoc]

中文:
引理 mulRight_mul
  结论: {X : 类型} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
  证明: by
  ext; simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mulRight_mul {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
    (x y : X) : ContinuousMap.mulRight (x * y) =
    (ContinuousMap.mulRight y).comp (ContinuousMap.mulRight x) := by
  ext; simp [mul_assoc]

/-- The continuous map `fun y => x * y` -/
@[to_additive /-- The continuous map `fun y => x + y` -/]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (x : X)
  body: mk _ (continuous_const_mul x)

@[to_additive (attr := simp)]

中文:
定义 mulLeft
  签名: (x : X)
  定义体: mk _ (continuous_const_mul x)

@[to_additive (attr := simp)]
-/
protected def mulLeft (x : X) : C(X, X) :=
  mk _ (continuous_const_mul x)

@[to_additive (attr := simp)]
/--
theorem `coe_mulLeft` / 定理 `coe_mulLeft`

English:
theorem coe_mulLeft
  given: (x : X)
  statement: ⇑(ContinuousMap.mulLeft x) = fun y => x * y
  proof: rfl

@[to_additive]

中文:
定理 coe_mulLeft
  条件: (x : X)
  结论: ⇑(ContinuousMap.mulLeft x) = fun y => x * y
  证明: rfl

@[to_additive]
-/
theorem coe_mulLeft (x : X) : ⇑(ContinuousMap.mulLeft x) = fun y => x * y :=
  rfl

@[to_additive]
/--
lemma `mulLeft_mul` / 引理 `mulLeft_mul`

English:
lemma mulLeft_mul
  statement: {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
  proof: by
  ext; simp [mul_assoc]

中文:
引理 mulLeft_mul
  结论: {X : 类型} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
  证明: by
  ext; simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mulLeft_mul {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
    (x y : X) : ContinuousMap.mulLeft (x * y) =
    (ContinuousMap.mulLeft x).comp (ContinuousMap.mulLeft y) := by
  ext; simp [mul_assoc]

end ContinuousMap
