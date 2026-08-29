/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Order.Interval.Set.WithBotTop
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Topology on extended natural numbers
-/

public section

open Filter Set Topology

namespace ENat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Nat∞
  body: Preorder.topology Nat∞

中文:
实例 :
  签名: 拓扑空间 自然数∞
  定义体: Preorder.topology Nat∞

Depends on / 依赖: Preorder, Preorder.topology, topology
-/
instance : TopologicalSpace Nat∞ := Preorder.topology Nat∞

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Nat∞
  body: ⟨rfl⟩

中文:
实例 :
  签名: Order拓扑 自然数∞
  定义体: ⟨rfl⟩
-/
instance : OrderTopology Nat∞ := ⟨rfl⟩

/--
theorem `range_natCast` / 定理 `range_natCast`

English:
theorem range_natCast
  statement: range ((↑) : Nat -> Nat∞) = Iio ⊤
  proof: WithTop.range_coe

中文:
定理 range_natCast
  结论: range ((↑) : 自然数 -> 自然数∞) = 左无界右开区间 ⊤
  证明: WithTop.range_coe
-/
@[simp] theorem range_natCast : range ((↑) : Nat -> Nat∞) = Iio ⊤ :=
  WithTop.range_coe

/--
theorem `isEmbedding_natCast` / 定理 `isEmbedding_natCast`

English:
theorem isEmbedding_natCast
  statement: IsEmbedding ((↑) : Nat -> Nat∞)
  proof: Nat.strictMono_cast.isEmbedding_of_ordConnected range_natCast ▸ ordConnected_Iio

中文:
定理 isEmbedding_natCast
  结论: 是嵌入 ((↑) : 自然数 -> 自然数∞)
  证明: Nat.strictMono_cast.isEmbedding_of_ordConnected range_natCast ▸ ordConnected_Iio

Depends on / 依赖: Nat.strictMono_cast.isEmbedding_of_ordConnected, isEmbedding_of_ordConnected, ordConnected_Iio, range_natCast, strictMono_cast
-/
theorem isEmbedding_natCast : IsEmbedding ((↑) : Nat -> Nat∞) :=
Nat.strictMono_cast.isEmbedding_of_ordConnected range_natCast ▸ ordConnected_Iio

/--
theorem `isOpenEmbedding_natCast` / 定理 `isOpenEmbedding_natCast`

English:
theorem isOpenEmbedding_natCast
  statement: IsOpenEmbedding ((↑) : Nat -> Nat∞)
  proof: ⟨isEmbedding_natCast, range_natCast ▸ isOpen_Iio⟩

中文:
定理 isOpenEmbedding_natCast
  结论: 是开嵌入 ((↑) : 自然数 -> 自然数∞)
  证明: ⟨isEmbedding_natCast, range_natCast ▸ isOpen_Iio⟩

Depends on / 依赖: isEmbedding_natCast, isOpen_Iio, range_natCast
-/
theorem isOpenEmbedding_natCast : IsOpenEmbedding ((↑) : Nat -> Nat∞) :=
  ⟨isEmbedding_natCast, range_natCast ▸ isOpen_Iio⟩

/--
theorem `nhds_natCast` / 定理 `nhds_natCast`

English:
theorem nhds_natCast
  given: (n : Nat)
  statement: 𝓝 (n : Nat∞) = pure (n : Nat∞)
  proof: by
  simp [← isOpenEmbedding_natCast.map_nhds_eq]

@[simp]

中文:
定理 nhds_natCast
  条件: (n : 自然数)
  结论: 𝓝 (n : 自然数∞) = pure (n : 自然数∞)
  证明: by
  simp [← isOpenEmbedding_natCast.map_nhds_eq]

@[simp]

Depends on / 依赖: isOpenEmbedding_natCast, isOpenEmbedding_natCast.map_nhds_eq, map_nhds_eq
-/
theorem nhds_natCast (n : Nat) : 𝓝 (n : Nat∞) = pure (n : Nat∞) := by
  simp [← isOpenEmbedding_natCast.map_nhds_eq]

@[simp]
/--
theorem `nhds_eq_pure` / 定理 `nhds_eq_pure`

English:
theorem nhds_eq_pure
  given: {n : Nat∞} (h : n != ⊤)
  statement: 𝓝 n = pure n
  proof: by
  lift n to Nat using h
  simp [nhds_natCast]

中文:
定理 nhds_eq_pure
  条件: {n : 自然数∞} (h : n != ⊤)
  结论: 𝓝 n = pure n
  证明: by
  lift n to Nat using h
  simp [nhds_natCast]
-/
protected theorem nhds_eq_pure {n : Nat∞} (h : n != ⊤) : 𝓝 n = pure n := by
  lift n to Nat using h
  simp [nhds_natCast]

/--
theorem `isOpen_singleton` / 定理 `isOpen_singleton`

English:
theorem isOpen_singleton
  given: {x : Nat∞} (hx : x != ⊤)
  statement: IsOpen {x}
  proof: by
  rw [isOpen_singleton_iff_nhds_eq_pure]; rw [ENat.nhds_eq_pure hx]

中文:
定理 isOpen_singleton
  条件: {x : 自然数∞} (hx : x != ⊤)
  结论: 是开集 {x}
  证明: by
  rw [isOpen_singleton_iff_nhds_eq_pure]; rw [ENat.nhds_eq_pure hx]

Depends on / 依赖: ENat.nhds_eq_pure, isOpen_singleton_iff_nhds_eq_pure, nhds_eq_pure
-/
theorem isOpen_singleton {x : Nat∞} (hx : x != ⊤) : IsOpen {x} := by
  rw [isOpen_singleton_iff_nhds_eq_pure]; rw [ENat.nhds_eq_pure hx]

/--
theorem `mem_nhds_iff` / 定理 `mem_nhds_iff`

English:
theorem mem_nhds_iff
  given: {x : Nat∞} {s : Set Nat∞} (hx : x != ⊤)
  statement: s in 𝓝 x ↔ x in s
  proof: by
  simp [hx]

中文:
定理 mem_nhds_iff
  条件: {x : 自然数∞} {s : 集合 自然数∞} (hx : x != ⊤)
  结论: s in 𝓝 x ↔ x in s
  证明: by
  simp [hx]
-/
theorem mem_nhds_iff {x : Nat∞} {s : Set Nat∞} (hx : x != ⊤) : s in 𝓝 x ↔ x in s := by
  simp [hx]

/--
theorem `mem_nhds_natCast_iff` / 定理 `mem_nhds_natCast_iff`

English:
theorem mem_nhds_natCast_iff
  given: (n : Nat) {s : Set Nat∞}
  statement: s in 𝓝 (n : Nat∞) ↔ (n : Nat∞) in s
  proof: mem_nhds_iff (natCast_ne_top _)

中文:
定理 mem_nhds_natCast_iff
  条件: (n : 自然数) {s : 集合 自然数∞}
  结论: s in 𝓝 (n : 自然数∞) ↔ (n : 自然数∞) in s
  证明: mem_nhds_iff (natCast_ne_top _)

Depends on / 依赖: mem_nhds_iff, natCast_ne_top
-/
theorem mem_nhds_natCast_iff (n : Nat) {s : Set Nat∞} : s in 𝓝 (n : Nat∞) ↔ (n : Nat∞) in s :=
  mem_nhds_iff (natCast_ne_top _)

/--
theorem `tendsto_nhds_top_iff_natCast_lt` / 定理 `tendsto_nhds_top_iff_natCast_lt`

English:
theorem tendsto_nhds_top_iff_natCast_lt
  given: {α : Type*} {l : Filter α} {f : α -> Nat∞}
  proof: by
  simp_rw [nhds_top_order, lt_top_iff_ne_top, tendsto_iInf, tendsto_principal, ENat.forall_ne_top,
    mem_Ioi]

中文:
定理 tendsto_nhds_top_iff_natCast_lt
  条件: {α : 类型} {l : 滤子 α} {f : α -> 自然数∞}
  证明: by
  simp_rw [nhds_top_order, lt_top_iff_ne_top, tendsto_iInf, tendsto_principal, ENat.forall_ne_top,
    mem_Ioi]

Depends on / 依赖: ENat.forall_ne_top, forall_ne_top, lt_top_iff_ne_top, mem_Ioi, nhds_top_order, simp_rw, tendsto_iInf, tendsto_principal
-/
theorem tendsto_nhds_top_iff_natCast_lt {α : Type*} {l : Filter α} {f : α -> Nat∞} :
    Tendsto f l (𝓝 ⊤) ↔ forall n : Nat, forallᶠ a in l, n < f a := by
  simp_rw [nhds_top_order, lt_top_iff_ne_top, tendsto_iInf, tendsto_principal, ENat.forall_ne_top,
    mem_Ioi]

/--
theorem `tendsto_natCast_nhds_top` / 定理 `tendsto_natCast_nhds_top`

English:
theorem tendsto_natCast_nhds_top
  statement: Tendsto Nat.cast atTop (𝓝 (⊤ : Nat∞))
  proof: by
  rw [tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [eventually_ge_atTop (n + 1)] with a ha using by simpa

中文:
定理 tendsto_natCast_nhds_top
  结论: 收敛 自然数.cast atTop (𝓝 (⊤ : 自然数∞))
  证明: by
  rw [tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [eventually_ge_atTop (n + 1)] with a ha using by simpa

Depends on / 依赖: eventually_ge_atTop, filter_upwards, tendsto_nhds_top_iff_natCast_lt
-/
theorem tendsto_natCast_nhds_top : Tendsto Nat.cast atTop (𝓝 (⊤ : Nat∞)) := by
  rw [tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [eventually_ge_atTop (n + 1)] with a ha using by simpa

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousAdd Nat∞
  body: by
  refine ⟨continuous_iff_continuousAt.mpr fun (a, b) => ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  | (a : Nat), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  | (a : Nat), (b : Nat) => simp [Cont

中文:
实例 :
  签名: 连续加法 自然数∞
  定义体: by
  refine ⟨continuous_iff_continuousAt.mpr fun (a, b) => ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  | (a : Nat), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  | (a : Nat), (b : Nat) => simp [Cont

Depends on / 依赖: ContinuousAt, continuousAt_fst, continuousAt_snd, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, le_add_left, le_add_right, le_rfl, nhds_prod_eq, tendsto_nhds_top_mono
-/
instance : ContinuousAdd Nat∞ := by
  refine ⟨continuous_iff_continuousAt.mpr fun (a, b) => ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  | (a : Nat), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  | (a : Nat), (b : Nat) => simp [ContinuousAt, nhds_prod_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMul Nat∞
  body: have key (a : Nat∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases eq_zero_or_pos a with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [co

中文:
实例 :
  签名: 连续乘法 自然数∞
  定义体: have key (a : Nat∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases eq_zero_or_pos a with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [co

Depends on / 依赖: ContinuousAt, Function, Function.uncurry, Order.one_le_iff_pos, Prod.forall, comp_of_eq, contin, continuousAt_fst, continuousAt_snd, continuous_iff_continuousAt, eq_zero_or_pos, filter_upwards, ha.ne, le_mul_of_one_le_left, lt_mem_nhds, mul_top, nhds_prod_eq, one_le_iff_pos, tendsto_nhds_top_mono, uncurry
-/
instance : ContinuousMul Nat∞ where
  continuous_mul :=
    have key (a : Nat∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases eq_zero_or_pos a with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [continuousAt_fst (lt_mem_nhds ha)] with (x, y) (hx : 0 < x)
        exact le_mul_of_one_le_left' (Order.one_le_iff_pos.2 hx)
continuous_iff_continuousAt.2 Prod.forall.2 fun
      | (a : Nat∞), ⊤ => key a
      | ⊤, (b : Nat∞) =>
((key b).comp_of_eq (continuous_swap.tendsto (⊤, b)) rfl).congr
          .of_forall fun _ => mul_comm ..
      | (a : Nat), (b : Nat) => by
        simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalSemiring Nat∞
  body: inferInstance
  toContinuousMul := inferInstance

中文:
实例 :
  签名: 是TopologicalSemiring 自然数∞
  定义体: inferInstance
  toContinuousMul := inferInstance
-/
instance : IsTopologicalSemiring Nat∞ where
  toContinuousAdd := inferInstance
  toContinuousMul := inferInstance

/--
theorem `continuousAt_sub` / 定理 `continuousAt_sub`

English:
theorem continuousAt_sub
  given: {a b : Nat∞} (h : a != ⊤ ∨ b != ⊤)
  proof: by
  match a, b, h with
  | (a : Nat), (b : Nat), _ => simp [ContinuousAt, nhds_prod_eq]
  | (a : Nat), ⊤, _ =>
    suffices forallᶠ b in 𝓝 ⊤, (a - b : Nat∞) = 0 by
      simpa [ContinuousAt, nhds_prod_eq, tsub_eq_zero_of_le]
    filter_upwards [le_mem_nhds (WithTop.coe_lt_top a)] with b using tsub_

中文:
定理 continuousAt_sub
  条件: {a b : 自然数∞} (h : a != ⊤ ∨ b != ⊤)
  证明: by
  match a, b, h with
  | (a : Nat), (b : Nat), _ => simp [ContinuousAt, nhds_prod_eq]
  | (a : Nat), ⊤, _ =>
    suffices forallᶠ b in 𝓝 ⊤, (a - b : Nat∞) = 0 by
      simpa [ContinuousAt, nhds_prod_eq, tsub_eq_zero_of_le]
    filter_upwards [le_mem_nhds (WithTop.coe_lt_top a)] with b using tsub_
-/
protected theorem continuousAt_sub {a b : Nat∞} (h : a != ⊤ ∨ b != ⊤) :
    ContinuousAt (· - ·).uncurry (a, b) := by
  match a, b, h with
  | (a : Nat), (b : Nat), _ => simp [ContinuousAt, nhds_prod_eq]
  | (a : Nat), ⊤, _ =>
    suffices forallᶠ b in 𝓝 ⊤, (a - b : Nat∞) = 0 by
      simpa [ContinuousAt, nhds_prod_eq, tsub_eq_zero_of_le]
    filter_upwards [le_mem_nhds (WithTop.coe_lt_top a)] with b using tsub_eq_zero_of_le
  | ⊤, (b : Nat), _ =>
    suffices forall n : Nat, forallᶠ a : Nat∞ in 𝓝 ⊤, b + n < a by
      simpa [ContinuousAt, nhds_prod_eq, (· ∘ ·), lt_tsub_iff_left, tendsto_nhds_top_iff_natCast_lt]
exact fun n => lt_mem_nhds WithTop.coe_lt_top (b + n)

end ENat

/--
theorem `Filter.Tendsto.enatSub` / 定理 `Filter.Tendsto.enatSub`

English:
theorem Filter.Tendsto.enatSub
  statement: {α : Type*} {l : Filter α} {f g : α -> Nat∞} {a b : Nat∞}
  proof: (ENat.continuousAt_sub h).tendsto.comp (hf.prodMk_nhds hg)

中文:
定理 滤子.收敛.enatSub
  结论: {α : 类型} {l : 滤子 α} {f g : α -> 自然数∞} {a b : 自然数∞}
  证明: (ENat.continuousAt_sub h).tendsto.comp (hf.prodMk_nhds hg)

Depends on / 依赖: ENat.continuousAt_sub, continuousAt_sub, hf.prodMk_nhds, prodMk_nhds, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.enatSub {α : Type*} {l : Filter α} {f g : α -> Nat∞} {a b : Nat∞}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : a != ⊤ ∨ b != ⊤) :
    Tendsto (fun x => f x - g x) l (𝓝 (a - b)) :=
  (ENat.continuousAt_sub h).tendsto.comp (hf.prodMk_nhds hg)

variable {X : Type*} [TopologicalSpace X] {f g : X -> Nat∞} {s : Set X} {x : X}

nonrec theorem ContinuousWithinAt.enatSub
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) (h : f x != ⊤ ∨ g x != ⊤) :
    ContinuousWithinAt (fun x => f x - g x) s x :=
  hf.enatSub hg h

nonrec theorem ContinuousAt.enatSub
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f x != ⊤ ∨ g x != ⊤) :
    ContinuousAt (fun x => f x - g x) x :=
  hf.enatSub hg h

nonrec theorem ContinuousOn.enatSub
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h : forall x in s, f x != ⊤ ∨ g x != ⊤) :
    ContinuousOn (fun x => f x - g x) s := fun x hx =>
  (hf x hx).enatSub (hg x hx) (h x hx)

nonrec theorem Continuous.enatSub
    (hf : Continuous f) (hg : Continuous g) (h : forall x, f x != ⊤ ∨ g x != ⊤) :
    Continuous (fun x => f x - g x) :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.enatSub hg.continuousAt (h x)
