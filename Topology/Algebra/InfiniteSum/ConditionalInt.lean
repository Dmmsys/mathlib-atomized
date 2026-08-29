/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Defs


/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used, for
example in the definition of the Eisenstein series `E2`.
In particular we define `symmetricIcc`, `symmetricIco`, `symmetricIoc` and `symmetricIoo` as
`SummationFilter`s corresponding to the intervals `Icc -N N`, `Ico -N N`, `Ioc -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

@[expose] public section

open Finset Topology Function Filter SummationFilter

namespace SummationFilter

section IntervalFilters

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G]

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
@[simps]
/--
Definition of `symmetricIcc` / `symmetricIcc` 的定义

English:
definition symmetricIcc
  signature: : SummationFilter G where
  body: atTop.map (fun g => Icc (-g) g)

中文:
定义 symmetricIcc
  签名: : SummationFilter G where
  定义体: atTop.map (fun g => Icc (-g) g)

Depends on / 依赖: atTop.map
-/
def symmetricIcc : SummationFilter G where
  filter := atTop.map (fun g => Icc (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioo (-N) N`· Note that for `G = ℤ` this coincides with
`symmetricIcc` so one should use that. See `symmetricIcc_eq_symmetricIoo_int`. -/
@[simps]
/--
Definition of `symmetricIoo` / `symmetricIoo` 的定义

English:
definition symmetricIoo
  signature: : SummationFilter G where
  body: atTop.map (fun g => Ioo (-g) g)

中文:
定义 symmetricIoo
  签名: : SummationFilter G where
  定义体: atTop.map (fun g => Ioo (-g) g)

Depends on / 依赖: atTop.map
-/
def symmetricIoo : SummationFilter G where
  filter := atTop.map (fun g => Ioo (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ico (-N) N`· -/
@[simps]
/--
Definition of `symmetricIco` / `symmetricIco` 的定义

English:
definition symmetricIco
  signature: : SummationFilter G where
  body: atTop.map (fun N => Ico (-N) N)

中文:
定义 symmetricIco
  签名: : SummationFilter G where
  定义体: atTop.map (fun N => Ico (-N) N)

Depends on / 依赖: atTop.map
-/
def symmetricIco : SummationFilter G where
  filter := atTop.map (fun N => Ico (-N) N)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioc (-N) N`· -/
@[simps]
/--
Definition of `symmetricIoc` / `symmetricIoc` 的定义

English:
definition symmetricIoc
  signature: : SummationFilter G where
  body: atTop.map (fun N => Ioc (-N) N)

中文:
定义 symmetricIoc
  签名: : SummationFilter G where
  定义体: atTop.map (fun N => Ioc (-N) N)

Depends on / 依赖: atTop.map
-/
def symmetricIoc : SummationFilter G where
  filter := atTop.map (fun N => Ioc (-N) N)

variable [(atTop : Filter G).NeBot]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIcc G).NeBot
  body: by simp [symmetricIcc, Filter.NeBot.map]

中文:
实例 :
  签名: (symmetricIcc G).NeBot
  定义体: by simp [symmetricIcc, Filter.NeBot.map]

Depends on / 依赖: Filter, Filter.NeBot.map, symmetricIcc
-/
instance : (symmetricIcc G).NeBot where
  ne_bot := by simp [symmetricIcc, Filter.NeBot.map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIco G).NeBot
  body: by simp [symmetricIco, Filter.NeBot.map]

中文:
实例 :
  签名: (symmetricIco G).NeBot
  定义体: by simp [symmetricIco, Filter.NeBot.map]

Depends on / 依赖: Filter, Filter.NeBot.map, symmetricIco
-/
instance : (symmetricIco G).NeBot where
  ne_bot := by simp [symmetricIco, Filter.NeBot.map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIoc G).NeBot
  body: by simp [symmetricIoc, Filter.NeBot.map]

中文:
实例 :
  签名: (symmetricIoc G).NeBot
  定义体: by simp [symmetricIoc, Filter.NeBot.map]

Depends on / 依赖: Filter, Filter.NeBot.map, symmetricIoc
-/
instance : (symmetricIoc G).NeBot where
  ne_bot := by simp [symmetricIoc, Filter.NeBot.map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIoo G).NeBot
  body: by simp [symmetricIoo, Filter.NeBot.map]

中文:
实例 :
  签名: (symmetricIoo G).NeBot
  定义体: by simp [symmetricIoo, Filter.NeBot.map]

Depends on / 依赖: Filter, Filter.NeBot.map, symmetricIoo
-/
instance : (symmetricIoo G).NeBot where
  ne_bot := by simp [symmetricIoo, Filter.NeBot.map]

section LeAtTop

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

/--
lemma `symmetricIcc_le_Conditional` / 引理 `symmetricIcc_le_Conditional`

English:
lemma symmetricIcc_le_Conditional
  proof: Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)

中文:
引理 symmetricIcc_le_Conditional
  证明: Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)

Depends on / 依赖: Filter, Filter.map_mono, map_mono, prodMk, tendsto_id, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.prodMk
-/
lemma symmetricIcc_le_Conditional :
    (symmetricIcc G).filter <= (conditional G).filter :=
  Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIcc G).LeAtTop
  body: le_trans symmetricIcc_le_Conditional (conditional G).le_atTop

中文:
实例 :
  签名: (symmetricIcc G).LeAtTop
  定义体: le_trans symmetricIcc_le_Conditional (conditional G).le_atTop

Depends on / 依赖: conditional, le_atTop, le_trans, symmetricIcc_le_Conditional
-/
instance : (symmetricIcc G).LeAtTop where
  le_atTop := le_trans symmetricIcc_le_Conditional (conditional G).le_atTop

variable [NoTopOrder G] [NoBotOrder G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIco G).LeAtTop
  body: by
    rw [symmetricIco]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ico_neg_atTop_atTop

中文:
实例 :
  签名: (symmetricIco G).LeAtTop
  定义体: by
    rw [symmetricIco]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ico_neg_atTop_atTop

Depends on / 依赖: map_le_iff_le_comap, symmetricIco, tendsto_Ico_neg_atTop_atTop, tendsto_iff_comap
-/
instance : (symmetricIco G).LeAtTop where
  le_atTop := by
    rw [symmetricIco]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ico_neg_atTop_atTop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIoc G).LeAtTop
  body: by
    rw [symmetricIoc]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ioc_neg_atTop_atTop

中文:
实例 :
  签名: (symmetricIoc G).LeAtTop
  定义体: by
    rw [symmetricIoc]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ioc_neg_atTop_atTop

Depends on / 依赖: map_le_iff_le_comap, symmetricIoc, tendsto_Ioc_neg_atTop_atTop, tendsto_iff_comap
-/
instance : (symmetricIoc G).LeAtTop where
  le_atTop := by
    rw [symmetricIoc]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ioc_neg_atTop_atTop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (symmetricIoo G).LeAtTop
  body: by
    rw [symmetricIoo]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ioo_neg_atTop_atTop

中文:
实例 :
  签名: (symmetricIoo G).LeAtTop
  定义体: by
    rw [symmetricIoo]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ioo_neg_atTop_atTop

Depends on / 依赖: map_le_iff_le_comap, symmetricIoo, tendsto_Ioo_neg_atTop_atTop, tendsto_iff_comap
-/
instance : (symmetricIoo G).LeAtTop where
  le_atTop := by
    rw [symmetricIoo]; rw [map_le_iff_le_comap]; rw [← @tendsto_iff_comap]
    exact tendsto_Ioo_neg_atTop_atTop

end LeAtTop

end IntervalFilters
section Int

variable {α : Type*} {f : Int -> α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

/--
lemma `symmetricIcc_eq_map_Icc_nat` / 引理 `symmetricIcc_eq_map_Icc_nat`

English:
lemma symmetricIcc_eq_map_Icc_nat
  proof: by
  simp [← Nat.map_cast_int_atTop, Function.comp_def]

中文:
引理 symmetricIcc_eq_map_Icc_nat
  证明: by
  simp [← Nat.map_cast_int_atTop, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Nat.map_cast_int_atTop, comp_def, map_cast_int_atTop
-/
lemma symmetricIcc_eq_map_Icc_nat :
    (symmetricIcc Int).filter = atTop.map (fun N : Nat => Icc (-(N : Int)) N) := by
  simp [← Nat.map_cast_int_atTop, Function.comp_def]

/--
lemma `symmetricIcc_eq_symmetricIoo_int` / 引理 `symmetricIcc_eq_symmetricIoo_int`

English:
lemma symmetricIcc_eq_symmetricIoo_int
  statement: symmetricIcc Int = symmetricIoo Int
  proof: by
  simp only [symmetricIcc, symmetricIoo, mk.injEq]
  ext s
  simp only [← Nat.map_cast_int_atTop, Filter.map_map, Filter.mem_map, mem_atTop_sets,
    Set.mem_preimage, comp_apply]
  refine ⟨fun ⟨a, ha⟩ => ⟨a + 1, fun b hb => ?_⟩, fun ⟨a, ha⟩ => ⟨a - 1, fun b hb => ?_⟩⟩ <;>
  [convert! ha (b - 1) 

中文:
引理 symmetricIcc_eq_symmetricIoo_int
  结论: symmetricIcc 整数 = symmetricIoo 整数
  证明: by
  simp only [symmetricIcc, symmetricIoo, mk.injEq]
  ext s
  simp only [← Nat.map_cast_int_atTop, Filter.map_map, Filter.mem_map, mem_atTop_sets,
    Set.mem_preimage, comp_apply]
  refine ⟨fun ⟨a, ha⟩ => ⟨a + 1, fun b hb => ?_⟩, fun ⟨a, ha⟩ => ⟨a - 1, fun b hb => ?_⟩⟩ <;>
  [convert! ha (b - 1) 

Depends on / 依赖: Filter, Filter.map_map, Filter.mem_map, Finset, Finset.ext_iff, Nat.map_cast_int_atTop, Set.mem_preimage, comp_apply, convert, ext_iff, map_cast_int_atTop, map_map, mem_atTop_sets, mem_map, mem_preimage, mk.injEq, symmetricIcc, symmetricIoo
-/
lemma symmetricIcc_eq_symmetricIoo_int : symmetricIcc Int = symmetricIoo Int := by
  simp only [symmetricIcc, symmetricIoo, mk.injEq]
  ext s
  simp only [← Nat.map_cast_int_atTop, Filter.map_map, Filter.mem_map, mem_atTop_sets,
    Set.mem_preimage, comp_apply]
  refine ⟨fun ⟨a, ha⟩ => ⟨a + 1, fun b hb => ?_⟩, fun ⟨a, ha⟩ => ⟨a - 1, fun b hb => ?_⟩⟩ <;>
  [convert! ha (b - 1) (by grind) using 1; convert! ha (b + 1) (by grind) using 1] <;>
  simp [Finset.ext_iff] <;> grind

@[to_additive]
/--
lemma `_root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc` / 引理 `_root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc`

English:
lemma _root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc
  statement: {a : α}
  proof: by
  simp only [HasProd, tendsto_map'_iff, symmetricIcc_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, symmetricIco] at *
  apply tendsto_of_div_tendsto_one _ hf
  simpa [Pi.div_def, fun N : Nat => prod_Icc_eq_prod_Ico_mul f (show (-N : Int) <= N by lia)]
    using hf2

@[to_additive]

中文:
引理 _root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc
  结论: {a : α}
  证明: by
  simp only [HasProd, tendsto_map'_iff, symmetricIcc_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, symmetricIco] at *
  apply tendsto_of_div_tendsto_one _ hf
  simpa [Pi.div_def, fun N : Nat => prod_Icc_eq_prod_Ico_mul f (show (-N : Int) <= N by lia)]
    using hf2

@[to_additive]

Depends on / 依赖: HasProd, Nat.map_cast_int_atTop, Pi.div_def, _iff, div_def, map_cast_int_atTop, prod_Icc_eq_prod_Ico_mul, symmetricIcc_eq_map_Icc_nat, symmetricIco, tendsto_map, tendsto_of_div_tendsto_one
-/
lemma _root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc {a : α}
    (hf : HasProd f a (symmetricIcc Int)) (hf2 : Tendsto (fun N : Nat => (f N)⁻¹) atTop (𝓝 1)) :
    HasProd f a (symmetricIco Int) := by
  simp only [HasProd, tendsto_map'_iff, symmetricIcc_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, symmetricIco] at *
  apply tendsto_of_div_tendsto_one _ hf
  simpa [Pi.div_def, fun N : Nat => prod_Icc_eq_prod_Ico_mul f (show (-N : Int) <= N by lia)]
    using hf2

@[to_additive]
/--
lemma `multipliable_symmetricIco_of_multipliable_symmetricIcc` / 引理 `multipliable_symmetricIco_of_multipliable_symmetricIcc`

English:
lemma multipliable_symmetricIco_of_multipliable_symmetricIcc
  proof: (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).multipliable

@[to_additive]

中文:
引理 multipliable_symmetricIco_of_multipliable_symmetricIcc
  证明: (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hasProd_symmetricIco_of_hasProd_symmetricIcc, hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc, multipliable
-/
lemma multipliable_symmetricIco_of_multipliable_symmetricIcc
    (hf : Multipliable f (symmetricIcc Int)) (hf2 : Tendsto (fun N : Nat => (f N)⁻¹) atTop (𝓝 1)) :
    Multipliable f (symmetricIco Int) :=
  (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).multipliable

@[to_additive]
/--
lemma `tprod_symmetricIcc_eq_tprod_symmetricIco` / 引理 `tprod_symmetricIcc_eq_tprod_symmetricIco`

English:
lemma tprod_symmetricIcc_eq_tprod_symmetricIco
  statement: [T2Space α]
  proof: (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).tprod_eq

@[to_additive]

中文:
引理 tprod_symmetricIcc_eq_tprod_symmetricIco
  结论: [T2Space α]
  证明: (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).tprod_eq

@[to_additive]

Depends on / 依赖: hasProd, hasProd_symmetricIco_of_hasProd_symmetricIcc, hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc, tprod_eq
-/
lemma tprod_symmetricIcc_eq_tprod_symmetricIco [T2Space α]
    (hf : Multipliable f (symmetricIcc Int)) (hf2 : Tendsto (fun N : Nat => (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[symmetricIco Int] b, f b = ∏'[symmetricIcc Int] b, f b :=
  (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).tprod_eq

@[to_additive]
/--
lemma `hasProd_symmetricIcc_iff` / 引理 `hasProd_symmetricIcc_iff`

English:
lemma hasProd_symmetricIcc_iff
  statement: {α : Type*} [CommMonoid α] [TopologicalSpace α]
  proof: by
  simp [HasProd, symmetricIcc, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]

中文:
引理 hasProd_symmetricIcc_iff
  结论: {α : 类型} [CommMonoid α] [TopologicalSpace α]
  证明: by
  simp [HasProd, symmetricIcc, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]

Depends on / 依赖: HasProd, Nat.map_cast_int_atTop, comp_def, map_cast_int_atTop, symmetricIcc
-/
lemma hasProd_symmetricIcc_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : Int -> α} {a : α} : HasProd f a (symmetricIcc Int) ↔
    Tendsto (fun N : Nat => ∏ n in Icc (-(N : Int)) N, f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIcc, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
/--
lemma `hasProd_symmetricIco_int_iff` / 引理 `hasProd_symmetricIco_int_iff`

English:
lemma hasProd_symmetricIco_int_iff
  statement: {α : Type*} [CommMonoid α] [TopologicalSpace α]
  proof: by
  simp [HasProd, symmetricIco, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]

中文:
引理 hasProd_symmetricIco_int_iff
  结论: {α : 类型} [CommMonoid α] [TopologicalSpace α]
  证明: by
  simp [HasProd, symmetricIco, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]

Depends on / 依赖: HasProd, Nat.map_cast_int_atTop, comp_def, map_cast_int_atTop, symmetricIco
-/
lemma hasProd_symmetricIco_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : Int -> α} {a : α} : HasProd f a (symmetricIco Int) ↔
    Tendsto (fun N : Nat => ∏ n in Ico (-(N : Int)) (N : Int), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIco, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
/--
lemma `hasProd_symmetricIoc_int_iff` / 引理 `hasProd_symmetricIoc_int_iff`

English:
lemma hasProd_symmetricIoc_int_iff
  statement: {α : Type*} [CommMonoid α] [TopologicalSpace α]
  proof: by
  simp [HasProd, symmetricIoc, ← Nat.map_cast_int_atTop, comp_def]

中文:
引理 hasProd_symmetricIoc_int_iff
  结论: {α : 类型} [CommMonoid α] [TopologicalSpace α]
  证明: by
  simp [HasProd, symmetricIoc, ← Nat.map_cast_int_atTop, comp_def]

Depends on / 依赖: HasProd, Nat.map_cast_int_atTop, comp_def, map_cast_int_atTop, symmetricIoc
-/
lemma hasProd_symmetricIoc_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : Int -> α} {a : α} : HasProd f a (symmetricIoc Int) ↔
    Tendsto (fun N : Nat => ∏ n in Ioc (-(N : Int)) (N : Int), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIoc, ← Nat.map_cast_int_atTop, comp_def]

/--
lemma `_root_.Summable.tendsto_zero_of_even_summable_symmetricIcc` / 引理 `_root_.Summable.tendsto_zero_of_even_summable_symmetricIcc`

English:
lemma _root_.Summable.tendsto_zero_of_even_summable_symmetricIcc
  statement: {F : Type*} [NormedAddCommGroup F]
  proof: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨L, hL⟩ := hf
  rw [HasSum]; rw [symmetricIcc_filter]; rw [tendsto_map'_iff]; rw [Function.comp_def] at hL
  have := hL.sub (hL.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
  simp only [id_eq, Int.reduceNeg, Function.comp_apply, sub_se

中文:
引理 _root_.Summable.tendsto_zero_of_even_summable_symmetricIcc
  结论: {F : 类型} [NormedAddCommGroup F]
  证明: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨L, hL⟩ := hf
  rw [HasSum]; rw [symmetricIcc_filter]; rw [tendsto_map'_iff]; rw [Function.comp_def] at hL
  have := hL.sub (hL.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
  simp only [id_eq, Int.reduceNeg, Function.comp_apply, sub_se

Depends on / 依赖: Finset, Finset.Icc, Function, Function.comp_apply, Function.comp_def, HasSum, Int.reduceNeg, _iff, comp_apply, comp_def, const_mul, eventually_ge_atTop, filter_upwards, hL.comp, hL.sub, id_eq, mul_zero, reduceNeg, sub_eq_add_neg, sub_self
-/
lemma _root_.Summable.tendsto_zero_of_even_summable_symmetricIcc {F : Type*} [NormedAddCommGroup F]
    [NormSMulClass Int F] {f : Int -> F} (hf : Summable f (symmetricIcc Int)) (hs : f.Even) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨L, hL⟩ := hf
  rw [HasSum]; rw [symmetricIcc_filter]; rw [tendsto_map'_iff]; rw [Function.comp_def] at hL
  have := hL.sub (hL.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
  simp only [id_eq, Int.reduceNeg, Function.comp_apply, sub_self, ← sub_eq_add_neg] at this
  rw [tendsto_zero_iff_norm_tendsto_zero] at this
  refine (mul_zero (_ : Real) ▸ this.const_mul 2⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : Finset.Icc (-x) x = Icc (-(x - 1)) (x - 1) union {-x, x} := by
    lift x to Nat using by positivity
    convert! Finset.Icc_succ_succ (x - 1) (x - 1) <;> grind
  rw [this]; rw [Finset.sum_union]; rw [Finset.sum_insert]; rw [Finset.sum_singleton]; rw [hs x]; rw [add_comm]; rw [add_sub_cancel_right]; rw [← two_zsmul]; rw [norm_smul]; rw [Int.norm_eq_abs]; rw [Int.cast_two]; rw [abs_two]; rw [inv_mul_cancel_left₀ two_ne_zero] <;>
  · simp only [disjoint_iff_ne, mem_insert, mem_singleton, mem_Icc]
    omega

end Int

end SummationFilter
