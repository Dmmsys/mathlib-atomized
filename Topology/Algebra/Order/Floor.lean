/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Filter.AtTopBot.Floor
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Topological facts about `Int.floor`, `Int.ceil` and `Int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_atTop`, `tendsto_floor_atBot`, `tendsto_ceil_atTop`, `tendsto_ceil_atBot`:
  `Int.floor` and `Int.ceil` tend to +-∞ in +-∞.
* `continuousOn_floor`: `Int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuousOn_ceil`: `Int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuousOn_fract`: `Int.fract` is continuous on `Ico n (n + 1)`.
* `ContinuousOn.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `Int.fract` yields another continuous function.
-/

public section


open Filter Function Int Set Topology

namespace FloorSemiring

open scoped Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  [TopologicalSpace K] [OrderTopology K]

/--
theorem `tendsto_mul_pow_div_factorial_sub_atTop` / 定理 `tendsto_mul_pow_div_factorial_sub_atTop`

English:
theorem tendsto_mul_pow_div_factorial_sub_atTop
  given: (a c : K) (d : Nat)
  proof: by
  rw [tendsto_order]
  constructor
  all_goals
    intro ε hε
    filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
    rw [mul_right_comm]; rw [← div_eq_mul_inv] at h
  · rw [div_lt_iff_of_neg hε] at h
    rwa [lt_div_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  · 

中文:
定理 tendsto_mul_pow_div_factorial_sub_atTop
  条件: (a c : K) (d : 自然数)
  证明: by
  rw [tendsto_order]
  constructor
  all_goals
    intro ε hε
    filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
    rw [mul_right_comm]; rw [← div_eq_mul_inv] at h
  · rw [div_lt_iff_of_neg hε] at h
    rwa [lt_div_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  · 

Depends on / 依赖: Nat.cast_pos.mpr, Nat.factorial_pos, all_goals, cast_pos, div_eq_mul_inv, div_lt_iff_of_neg, eventually_mul_pow_lt_factorial_sub, factorial_pos, filter_upwards, mul_right_comm, tendsto_order
-/
theorem tendsto_mul_pow_div_factorial_sub_atTop (a c : K) (d : Nat) :
    Tendsto (fun n => a * c ^ n / (n - d)!) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  all_goals
    intro ε hε
    filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
    rw [mul_right_comm]; rw [← div_eq_mul_inv] at h
  · rw [div_lt_iff_of_neg hε] at h
    rwa [lt_div_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  · rw [div_lt_iff₀ hε] at h
    rwa [div_lt_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]

/--
theorem `tendsto_pow_div_factorial_atTop` / 定理 `tendsto_pow_div_factorial_atTop`

English:
theorem tendsto_pow_div_factorial_atTop
  given: (c : K)
  proof: by
  convert! tendsto_mul_pow_div_factorial_sub_atTop 1 c 0
  rw [one_mul]

中文:
定理 tendsto_pow_div_factorial_atTop
  条件: (c : K)
  证明: by
  convert! tendsto_mul_pow_div_factorial_sub_atTop 1 c 0
  rw [one_mul]

Depends on / 依赖: convert, one_mul, tendsto_mul_pow_div_factorial_sub_atTop
-/
theorem tendsto_pow_div_factorial_atTop (c : K) :
    Tendsto (fun n => c ^ n / n !) atTop (𝓝 0) := by
  convert! tendsto_mul_pow_div_factorial_sub_atTop 1 c 0
  rw [one_mul]

end FloorSemiring

variable {α β γ : Type*} [Ring α] [LinearOrder α] [FloorRing α]

section
variable [IsStrictOrderedRing α]
-- TODO: move to `Mathlib/Order/Filter/AtTopBot/Floor.lean`

/--
theorem `tendsto_floor_atTop` / 定理 `tendsto_floor_atTop`

English:
theorem tendsto_floor_atTop
  statement: Tendsto (floor : α -> Int) atTop atTop
  proof: floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : Int), by rw [floor_intCast]; exact (lt_add_one _).le⟩

中文:
定理 tendsto_floor_atTop
  结论: Tendsto (floor : α -> 整数) atTop atTop
  证明: floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : Int), by rw [floor_intCast]; exact (lt_add_one _).le⟩

Depends on / 依赖: floor_intCast, floor_mono, floor_mono.tendsto_atTop_atTop, lt_add_one, tendsto_atTop_atTop
-/
theorem tendsto_floor_atTop : Tendsto (floor : α -> Int) atTop atTop :=
  floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : Int), by rw [floor_intCast]; exact (lt_add_one _).le⟩

/--
theorem `tendsto_floor_atBot` / 定理 `tendsto_floor_atBot`

English:
theorem tendsto_floor_atBot
  statement: Tendsto (floor : α -> Int) atBot atBot
  proof: floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩

中文:
定理 tendsto_floor_atBot
  结论: Tendsto (floor : α -> 整数) atBot atBot
  证明: floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩

Depends on / 依赖: floor_intCast, floor_mono, floor_mono.tendsto_atBot_atBot, tendsto_atBot_atBot
-/
theorem tendsto_floor_atBot : Tendsto (floor : α -> Int) atBot atBot :=
  floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩

/--
theorem `tendsto_ceil_atTop` / 定理 `tendsto_ceil_atTop`

English:
theorem tendsto_ceil_atTop
  statement: Tendsto (ceil : α -> Int) atTop atTop
  proof: ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩

中文:
定理 tendsto_ceil_atTop
  结论: Tendsto (ceil : α -> 整数) atTop atTop
  证明: ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩

Depends on / 依赖: ceil_intCast, ceil_mono, ceil_mono.tendsto_atTop_atTop, tendsto_atTop_atTop
-/
theorem tendsto_ceil_atTop : Tendsto (ceil : α -> Int) atTop atTop :=
  ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩

/--
theorem `tendsto_ceil_atBot` / 定理 `tendsto_ceil_atBot`

English:
theorem tendsto_ceil_atBot
  statement: Tendsto (ceil : α -> Int) atBot atBot
  proof: ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : Int), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩

中文:
定理 tendsto_ceil_atBot
  结论: Tendsto (ceil : α -> 整数) atBot atBot
  证明: ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : Int), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩

Depends on / 依赖: ceil_intCast, ceil_mono, ceil_mono.tendsto_atBot_atBot, sub_one_lt, tendsto_atBot_atBot
-/
theorem tendsto_ceil_atBot : Tendsto (ceil : α -> Int) atBot atBot :=
  ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : Int), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩

end

variable [TopologicalSpace α]

/--
theorem `continuousOn_floor` / 定理 `continuousOn_floor`

English:
theorem continuousOn_floor
  given: (n : Int)
  proof: (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const

中文:
定理 continuousOn_floor
  条件: (n : 整数)
  证明: (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const

Depends on / 依赖: continuousOn_congr, continuousOn_const, floor_eq_on_Ico
-/
theorem continuousOn_floor (n : Int) :
    ContinuousOn (fun x => floor x : α -> α) (Ico n (n + 1) : Set α) :=
  (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const

/--
theorem `continuousOn_ceil` / 定理 `continuousOn_ceil`

English:
theorem continuousOn_ceil
  given: (n : Int)
  proof: (continuousOn_congr <| ceil_eq_on_Ioc' n).mpr continuousOn_const

中文:
定理 continuousOn_ceil
  条件: (n : 整数)
  证明: (continuousOn_congr <| ceil_eq_on_Ioc' n).mpr continuousOn_const

Depends on / 依赖: ceil_eq_on_Ioc, continuousOn_congr, continuousOn_const
-/
theorem continuousOn_ceil (n : Int) :
    ContinuousOn (fun x => ceil x : α -> α) (Ioc (n - 1) n : Set α) :=
  (continuousOn_congr <| ceil_eq_on_Ioc' n).mpr continuousOn_const

section OrderClosedTopology

variable [IsStrictOrderedRing α] [OrderClosedTopology α]

omit [IsStrictOrderedRing α] in
/--
theorem `tendsto_floor_right_pure_floor` / 定理 `tendsto_floor_right_pure_floor`

English:
theorem tendsto_floor_right_pure_floor
  given: (x : α)
  statement: Tendsto (floor : α -> Int) (𝓝[>=] x) (pure ⌊x⌋)
  proof: tendsto_pure.2 mem_of_superset (Ico_mem_nhdsGE <| lt_floor_add_one x) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨(floor_le x).trans hy.1, hy.2⟩

中文:
定理 tendsto_floor_right_pure_floor
  条件: (x : α)
  结论: Tendsto (floor : α -> 整数) (𝓝[>=] x) (pure ⌊x⌋)
  证明: tendsto_pure.2 mem_of_superset (Ico_mem_nhdsGE <| lt_floor_add_one x) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨(floor_le x).trans hy.1, hy.2⟩

Depends on / 依赖: Ico_mem_nhdsGE, floor_eq_on_Ico, floor_le, lt_floor_add_one, mem_of_superset, tendsto_pure
-/
theorem tendsto_floor_right_pure_floor (x : α) : Tendsto (floor : α -> Int) (𝓝[>=] x) (pure ⌊x⌋) :=
tendsto_pure.2 mem_of_superset (Ico_mem_nhdsGE <| lt_floor_add_one x) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨(floor_le x).trans hy.1, hy.2⟩

/--
theorem `tendsto_floor_right_pure` / 定理 `tendsto_floor_right_pure`

English:
theorem tendsto_floor_right_pure
  given: (n : Int)
  statement: Tendsto (floor : α -> Int) (𝓝[>=] n) (pure n)
  proof: by
  simpa only [floor_intCast] using tendsto_floor_right_pure_floor (n : α)

中文:
定理 tendsto_floor_right_pure
  条件: (n : 整数)
  结论: Tendsto (floor : α -> 整数) (𝓝[>=] n) (pure n)
  证明: by
  simpa only [floor_intCast] using tendsto_floor_right_pure_floor (n : α)

Depends on / 依赖: floor_intCast, tendsto_floor_right_pure_floor
-/
theorem tendsto_floor_right_pure (n : Int) : Tendsto (floor : α -> Int) (𝓝[>=] n) (pure n) := by
  simpa only [floor_intCast] using tendsto_floor_right_pure_floor (n : α)

/--
theorem `tendsto_ceil_left_pure_ceil` / 定理 `tendsto_ceil_left_pure_ceil`

English:
theorem tendsto_ceil_left_pure_ceil
  given: (x : α)
  statement: Tendsto (ceil : α -> Int) (𝓝[<=] x) (pure ⌈x⌉)
  proof: tendsto_pure.2 mem_of_superset
    (Ioc_mem_nhdsLE <| sub_lt_iff_lt_add.2 <| ceil_lt_add_one _) fun _y hy =>
      ceil_eq_on_Ioc _ _ ⟨hy.1, hy.2.trans (le_ceil _)⟩

中文:
定理 tendsto_ceil_left_pure_ceil
  条件: (x : α)
  结论: Tendsto (ceil : α -> 整数) (𝓝[<=] x) (pure ⌈x⌉)
  证明: tendsto_pure.2 mem_of_superset
    (Ioc_mem_nhdsLE <| sub_lt_iff_lt_add.2 <| ceil_lt_add_one _) fun _y hy =>
      ceil_eq_on_Ioc _ _ ⟨hy.1, hy.2.trans (le_ceil _)⟩

Depends on / 依赖: Ioc_mem_nhdsLE, ceil_eq_on_Ioc, ceil_lt_add_one, le_ceil, mem_of_superset, sub_lt_iff_lt_add, tendsto_pure
-/
theorem tendsto_ceil_left_pure_ceil (x : α) : Tendsto (ceil : α -> Int) (𝓝[<=] x) (pure ⌈x⌉) :=
tendsto_pure.2 mem_of_superset
    (Ioc_mem_nhdsLE <| sub_lt_iff_lt_add.2 <| ceil_lt_add_one _) fun _y hy =>
      ceil_eq_on_Ioc _ _ ⟨hy.1, hy.2.trans (le_ceil _)⟩

/--
theorem `tendsto_ceil_left_pure` / 定理 `tendsto_ceil_left_pure`

English:
theorem tendsto_ceil_left_pure
  given: (n : Int)
  statement: Tendsto (ceil : α -> Int) (𝓝[<=] n) (pure n)
  proof: by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)

中文:
定理 tendsto_ceil_left_pure
  条件: (n : 整数)
  结论: Tendsto (ceil : α -> 整数) (𝓝[<=] n) (pure n)
  证明: by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)

Depends on / 依赖: ceil_intCast, tendsto_ceil_left_pure_ceil
-/
theorem tendsto_ceil_left_pure (n : Int) : Tendsto (ceil : α -> Int) (𝓝[<=] n) (pure n) := by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)

/--
theorem `tendsto_floor_left_pure_ceil_sub_one` / 定理 `tendsto_floor_left_pure_ceil_sub_one`

English:
theorem tendsto_floor_left_pure_ceil_sub_one
  given: (x : α)
  proof: have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x <= ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
tendsto_pure.2 mem_of_superset (Ico_mem_nhdsLT h₁) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_

中文:
定理 tendsto_floor_left_pure_ceil_sub_one
  条件: (x : α)
  证明: have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x <= ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
tendsto_pure.2 mem_of_superset (Ico_mem_nhdsLT h₁) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_

Depends on / 依赖: Ico_mem_nhdsLT, cast_one, cast_sub, ceil_lt_add_one, floor_eq_on_Ico, le_ceil, mem_of_superset, sub_add_cancel, sub_lt_iff_lt_add, tendsto_pure, trans_le
-/
theorem tendsto_floor_left_pure_ceil_sub_one (x : α) :
    Tendsto (floor : α -> Int) (𝓝[<] x) (pure (⌈x⌉ - 1)) :=
  have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x <= ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
tendsto_pure.2 mem_of_superset (Ico_mem_nhdsLT h₁) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_le h₂⟩

/--
theorem `tendsto_floor_left_pure_sub_one` / 定理 `tendsto_floor_left_pure_sub_one`

English:
theorem tendsto_floor_left_pure_sub_one
  given: (n : Int)
  proof: by
  simpa only [ceil_intCast] using tendsto_floor_left_pure_ceil_sub_one (n : α)

omit [IsStrictOrderedRing α] in

中文:
定理 tendsto_floor_left_pure_sub_one
  条件: (n : 整数)
  证明: by
  simpa only [ceil_intCast] using tendsto_floor_left_pure_ceil_sub_one (n : α)

omit [IsStrictOrderedRing α] in

Depends on / 依赖: ceil_intCast, tendsto_floor_left_pure_ceil_sub_one
-/
theorem tendsto_floor_left_pure_sub_one (n : Int) :
    Tendsto (floor : α -> Int) (𝓝[<] n) (pure (n - 1)) := by
  simpa only [ceil_intCast] using tendsto_floor_left_pure_ceil_sub_one (n : α)

omit [IsStrictOrderedRing α] in
/--
theorem `tendsto_ceil_right_pure_floor_add_one` / 定理 `tendsto_ceil_right_pure_floor_add_one`

English:
theorem tendsto_ceil_right_pure_floor_add_one
  given: (x : α)
  proof: have : ↑(⌊x⌋ + 1) - 1 <= x := by rw [cast_add, cast_one, add_sub_cancel_right]; exact floor_le _
tendsto_pure.2 mem_of_superset (Ioc_mem_nhdsGT <| lt_succ_floor _) fun _y hy =>
    ceil_eq_on_Ioc _ _ ⟨this.trans_lt hy.1, hy.2⟩

中文:
定理 tendsto_ceil_right_pure_floor_add_one
  条件: (x : α)
  证明: have : ↑(⌊x⌋ + 1) - 1 <= x := by rw [cast_add, cast_one, add_sub_cancel_right]; exact floor_le _
tendsto_pure.2 mem_of_superset (Ioc_mem_nhdsGT <| lt_succ_floor _) fun _y hy =>
    ceil_eq_on_Ioc _ _ ⟨this.trans_lt hy.1, hy.2⟩

Depends on / 依赖: Ioc_mem_nhdsGT, add_sub_cancel_right, cast_add, cast_one, ceil_eq_on_Ioc, floor_le, lt_succ_floor, mem_of_superset, tendsto_pure, this.trans_lt, trans_lt
-/
theorem tendsto_ceil_right_pure_floor_add_one (x : α) :
    Tendsto (ceil : α -> Int) (𝓝[>] x) (pure (⌊x⌋ + 1)) :=
  have : ↑(⌊x⌋ + 1) - 1 <= x := by rw [cast_add, cast_one, add_sub_cancel_right]; exact floor_le _
tendsto_pure.2 mem_of_superset (Ioc_mem_nhdsGT <| lt_succ_floor _) fun _y hy =>
    ceil_eq_on_Ioc _ _ ⟨this.trans_lt hy.1, hy.2⟩

/--
theorem `tendsto_ceil_right_pure_add_one` / 定理 `tendsto_ceil_right_pure_add_one`

English:
theorem tendsto_ceil_right_pure_add_one
  given: (n : Int)
  proof: by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)

中文:
定理 tendsto_ceil_right_pure_add_one
  条件: (n : 整数)
  证明: by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)

Depends on / 依赖: floor_intCast, tendsto_ceil_right_pure_floor_add_one
-/
theorem tendsto_ceil_right_pure_add_one (n : Int) :
    Tendsto (ceil : α -> Int) (𝓝[>] n) (pure (n + 1)) := by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)

/--
theorem `tendsto_floor_right` / 定理 `tendsto_floor_right`

English:
theorem tendsto_floor_right
  given: (n : Int)
  statement: Tendsto (fun x => floor x : α -> α) (𝓝[>=] n) (𝓝[>=] n)
  proof: ((tendsto_pure_pure _ _).comp (tendsto_floor_right_pure n)).mono_right
    pure_le_nhdsWithin le_rfl

中文:
定理 tendsto_floor_right
  条件: (n : 整数)
  结论: Tendsto (fun x => floor x : α -> α) (𝓝[>=] n) (𝓝[>=] n)
  证明: ((tendsto_pure_pure _ _).comp (tendsto_floor_right_pure n)).mono_right
    pure_le_nhdsWithin le_rfl

Depends on / 依赖: le_rfl, mono_right, pure_le_nhdsWithin, tendsto_floor_right_pure, tendsto_pure_pure
-/
theorem tendsto_floor_right (n : Int) : Tendsto (fun x => floor x : α -> α) (𝓝[>=] n) (𝓝[>=] n) :=
((tendsto_pure_pure _ _).comp (tendsto_floor_right_pure n)).mono_right
    pure_le_nhdsWithin le_rfl

/--
theorem `tendsto_floor_right'` / 定理 `tendsto_floor_right'`

English:
theorem tendsto_floor_right'
  given: (n : Int)
  statement: Tendsto (fun x => floor x : α -> α) (𝓝[>=] n) (𝓝 n)
  proof: (tendsto_floor_right n).mono_right inf_le_left

中文:
定理 tendsto_floor_right'
  条件: (n : 整数)
  结论: Tendsto (fun x => floor x : α -> α) (𝓝[>=] n) (𝓝 n)
  证明: (tendsto_floor_right n).mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_floor_right
-/
theorem tendsto_floor_right' (n : Int) : Tendsto (fun x => floor x : α -> α) (𝓝[>=] n) (𝓝 n) :=
  (tendsto_floor_right n).mono_right inf_le_left

/--
theorem `tendsto_ceil_left` / 定理 `tendsto_ceil_left`

English:
theorem tendsto_ceil_left
  given: (n : Int)
  statement: Tendsto (fun x => ceil x : α -> α) (𝓝[<=] n) (𝓝[<=] n)
  proof: ((tendsto_pure_pure _ _).comp (tendsto_ceil_left_pure n)).mono_right
    pure_le_nhdsWithin le_rfl

中文:
定理 tendsto_ceil_left
  条件: (n : 整数)
  结论: Tendsto (fun x => ceil x : α -> α) (𝓝[<=] n) (𝓝[<=] n)
  证明: ((tendsto_pure_pure _ _).comp (tendsto_ceil_left_pure n)).mono_right
    pure_le_nhdsWithin le_rfl

Depends on / 依赖: le_rfl, mono_right, pure_le_nhdsWithin, tendsto_ceil_left_pure, tendsto_pure_pure
-/
theorem tendsto_ceil_left (n : Int) : Tendsto (fun x => ceil x : α -> α) (𝓝[<=] n) (𝓝[<=] n) :=
((tendsto_pure_pure _ _).comp (tendsto_ceil_left_pure n)).mono_right
    pure_le_nhdsWithin le_rfl

/--
theorem `tendsto_ceil_left'` / 定理 `tendsto_ceil_left'`

English:
theorem tendsto_ceil_left'
  given: (n : Int)
  proof: (tendsto_ceil_left n).mono_right inf_le_left

中文:
定理 tendsto_ceil_left'
  条件: (n : 整数)
  证明: (tendsto_ceil_left n).mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_ceil_left
-/
theorem tendsto_ceil_left' (n : Int) :
    Tendsto (fun x => ceil x : α -> α) (𝓝[<=] n) (𝓝 n) :=
  (tendsto_ceil_left n).mono_right inf_le_left

/--
theorem `tendsto_floor_left` / 定理 `tendsto_floor_left`

English:
theorem tendsto_floor_left
  given: (n : Int)
  proof: ((tendsto_pure_pure _ _).comp (tendsto_floor_left_pure_sub_one n)).mono_right by
    rw [← @cast_one α]; rw [← cast_sub]; exact pure_le_nhdsWithin le_rfl

中文:
定理 tendsto_floor_left
  条件: (n : 整数)
  证明: ((tendsto_pure_pure _ _).comp (tendsto_floor_left_pure_sub_one n)).mono_right by
    rw [← @cast_one α]; rw [← cast_sub]; exact pure_le_nhdsWithin le_rfl

Depends on / 依赖: cast_one, cast_sub, le_rfl, mono_right, pure_le_nhdsWithin, tendsto_floor_left_pure_sub_one, tendsto_pure_pure
-/
theorem tendsto_floor_left (n : Int) :
    Tendsto (fun x => floor x : α -> α) (𝓝[<] n) (𝓝[<=] (n - 1)) :=
((tendsto_pure_pure _ _).comp (tendsto_floor_left_pure_sub_one n)).mono_right by
    rw [← @cast_one α]; rw [← cast_sub]; exact pure_le_nhdsWithin le_rfl

/--
theorem `tendsto_ceil_right` / 定理 `tendsto_ceil_right`

English:
theorem tendsto_ceil_right
  given: (n : Int)
  proof: ((tendsto_pure_pure _ _).comp (tendsto_ceil_right_pure_add_one n)).mono_right by
    rw [← @cast_one α]; rw [← cast_add]; exact pure_le_nhdsWithin le_rfl

中文:
定理 tendsto_ceil_right
  条件: (n : 整数)
  证明: ((tendsto_pure_pure _ _).comp (tendsto_ceil_right_pure_add_one n)).mono_right by
    rw [← @cast_one α]; rw [← cast_add]; exact pure_le_nhdsWithin le_rfl

Depends on / 依赖: cast_add, cast_one, le_rfl, mono_right, pure_le_nhdsWithin, tendsto_ceil_right_pure_add_one, tendsto_pure_pure
-/
theorem tendsto_ceil_right (n : Int) :
    Tendsto (fun x => ceil x : α -> α) (𝓝[>] n) (𝓝[>=] (n + 1)) :=
((tendsto_pure_pure _ _).comp (tendsto_ceil_right_pure_add_one n)).mono_right by
    rw [← @cast_one α]; rw [← cast_add]; exact pure_le_nhdsWithin le_rfl

/--
theorem `tendsto_floor_left'` / 定理 `tendsto_floor_left'`

English:
theorem tendsto_floor_left'
  given: (n : Int)
  proof: (tendsto_floor_left n).mono_right inf_le_left

中文:
定理 tendsto_floor_left'
  条件: (n : 整数)
  证明: (tendsto_floor_left n).mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_floor_left
-/
theorem tendsto_floor_left' (n : Int) :
    Tendsto (fun x => floor x : α -> α) (𝓝[<] n) (𝓝 (n - 1)) :=
  (tendsto_floor_left n).mono_right inf_le_left

/--
theorem `tendsto_ceil_right'` / 定理 `tendsto_ceil_right'`

English:
theorem tendsto_ceil_right'
  given: (n : Int)
  proof: (tendsto_ceil_right n).mono_right inf_le_left

中文:
定理 tendsto_ceil_right'
  条件: (n : 整数)
  证明: (tendsto_ceil_right n).mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_ceil_right
-/
theorem tendsto_ceil_right' (n : Int) :
    Tendsto (fun x => ceil x : α -> α) (𝓝[>] n) (𝓝 (n + 1)) :=
  (tendsto_ceil_right n).mono_right inf_le_left

end OrderClosedTopology

/--
theorem `continuousOn_fract` / 定理 `continuousOn_fract`

English:
theorem continuousOn_fract
  given: [IsTopologicalAddGroup α] (n : Int)
  proof: continuousOn_id.sub (continuousOn_floor n)

中文:
定理 continuousOn_fract
  条件: [IsTopologicalAddGroup α] (n : 整数)
  证明: continuousOn_id.sub (continuousOn_floor n)

Depends on / 依赖: continuousOn_floor, continuousOn_id, continuousOn_id.sub
-/
theorem continuousOn_fract [IsTopologicalAddGroup α] (n : Int) :
    ContinuousOn (fract : α -> α) (Ico n (n + 1) : Set α) :=
  continuousOn_id.sub (continuousOn_floor n)

/--
theorem `continuousAt_fract` / 定理 `continuousAt_fract`

English:
theorem continuousAt_fract
  statement: [OrderClosedTopology α] [IsTopologicalAddGroup α]
  proof: (continuousOn_fract ⌊x⌋).continuousAt
    Ico_mem_nhds ((floor_le _).lt_of_ne h.symm) (lt_floor_add_one _)

中文:
定理 continuousAt_fract
  结论: [OrderClosedTopology α] [IsTopologicalAddGroup α]
  证明: (continuousOn_fract ⌊x⌋).continuousAt
    Ico_mem_nhds ((floor_le _).lt_of_ne h.symm) (lt_floor_add_one _)

Depends on / 依赖: Ico_mem_nhds, continuousAt, continuousOn_fract, floor_le, h.symm, lt_floor_add_one, lt_of_ne
-/
theorem continuousAt_fract [OrderClosedTopology α] [IsTopologicalAddGroup α]
    {x : α} (h : x != ⌊x⌋) : ContinuousAt fract x :=
(continuousOn_fract ⌊x⌋).continuousAt
    Ico_mem_nhds ((floor_le _).lt_of_ne h.symm) (lt_floor_add_one _)

variable [IsStrictOrderedRing α]

/--
theorem `tendsto_fract_left'` / 定理 `tendsto_fract_left'`

English:
theorem tendsto_fract_left'
  given: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int)
  proof: by
  rw [← sub_sub_cancel (n : α) 1]
  refine (tendsto_id.mono_left nhdsWithin_le_nhds).sub ?_
  exact tendsto_floor_left' n

中文:
定理 tendsto_fract_left'
  条件: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : 整数)
  证明: by
  rw [← sub_sub_cancel (n : α) 1]
  refine (tendsto_id.mono_left nhdsWithin_le_nhds).sub ?_
  exact tendsto_floor_left' n

Depends on / 依赖: mono_left, nhdsWithin_le_nhds, sub_sub_cancel, tendsto_floor_left, tendsto_id, tendsto_id.mono_left
-/
theorem tendsto_fract_left' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int) :
    Tendsto (fract : α -> α) (𝓝[<] n) (𝓝 1) := by
  rw [← sub_sub_cancel (n : α) 1]
  refine (tendsto_id.mono_left nhdsWithin_le_nhds).sub ?_
  exact tendsto_floor_left' n

/--
theorem `tendsto_fract_left` / 定理 `tendsto_fract_left`

English:
theorem tendsto_fract_left
  given: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int)
  proof: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (Eventually.of_forall fract_lt_one)

中文:
定理 tendsto_fract_left
  条件: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : 整数)
  证明: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (Eventually.of_forall fract_lt_one)

Depends on / 依赖: Eventually, Eventually.of_forall, fract_lt_one, of_forall, tendsto_fract_left, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem tendsto_fract_left [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int) :
    Tendsto (fract : α -> α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (Eventually.of_forall fract_lt_one)

/--
theorem `tendsto_fract_right'` / 定理 `tendsto_fract_right'`

English:
theorem tendsto_fract_right'
  given: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int)
  proof: sub_self (n : α) ▸ (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n)

中文:
定理 tendsto_fract_right'
  条件: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : 整数)
  证明: sub_self (n : α) ▸ (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n)

Depends on / 依赖: sub_self, tendsto_floor_right, tendsto_id, tendsto_nhdsWithin_of_tendsto_nhds
-/
theorem tendsto_fract_right' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int) :
    Tendsto (fract : α -> α) (𝓝[>=] n) (𝓝 0) :=
  sub_self (n : α) ▸ (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n)

/--
theorem `tendsto_fract_right` / 定理 `tendsto_fract_right`

English:
theorem tendsto_fract_right
  given: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int)
  proof: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (Eventually.of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

中文:
定理 tendsto_fract_right
  条件: [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : 整数)
  证明: tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (Eventually.of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

Depends on / 依赖: Eventually, Eventually.of_forall, fract_nonneg, of_forall, tendsto_fract_right, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem tendsto_fract_right [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : Int) :
    Tendsto (fract : α -> α) (𝓝[>=] n) (𝓝[>=] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (Eventually.of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/--
theorem `ContinuousOn.comp_fract'` / 定理 `ContinuousOn.comp_fract'`

English:
theorem ContinuousOn.comp_fract'
  statement: {f : β -> α -> γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
  proof: by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  rcases em (exists n : Int, t = n) with (⟨n, rfl⟩ | ht)
  · rw [ContinuousAt, nhds_prod_eq, ← nhdsLT_sup_nhdsGE (n : α), prod_sup, tendsto_sup]
    constructor
    · refine (((h (s, 1) ⟨trivial

中文:
定理 ContinuousOn.comp_fract'
  结论: {f : β -> α -> γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
  证明: by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  rcases em (exists n : Int, t = n) with (⟨n, rfl⟩ | ht)
  · rw [ContinuousAt, nhds_prod_eq, ← nhdsLT_sup_nhdsGE (n : α), prod_sup, tendsto_sup]
    constructor
    · refine (((h (s, 1) ⟨trivial

Depends on / 依赖: Continuous, ContinuousAt, Filter, Filter.prod_, Prod.map, continuous_iff_continuousAt, le_of_eq, le_rfl, mono_left, mono_right, nhdsLT_sup_nhdsGE, nhdsWithin_Ico_eq_nhdsLT, nhdsWithin_prod_eq, nhdsWithin_univ, nhds_prod_eq, one_pos, prodMap, prod_, prod_sup, tendsto
-/
theorem ContinuousOn.comp_fract' {f : β -> α -> γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
    (hf : forall s, f s 0 = f s 1) : Continuous fun st : β × α => f st.1 (fract st.2) := by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  rcases em (exists n : Int, t = n) with (⟨n, rfl⟩ | ht)
  · rw [ContinuousAt, nhds_prod_eq, ← nhdsLT_sup_nhdsGE (n : α), prod_sup, tendsto_sup]
    constructor
    · refine (((h (s, 1) ⟨trivial, zero_le_one, le_rfl⟩).tendsto.mono_left ?_).comp
        (tendsto_id.prodMap (tendsto_fract_left _))).mono_right (le_of_eq ?_)
      · rw [nhdsWithin_prod_eq, nhdsWithin_univ, ← nhdsWithin_Ico_eq_nhdsLT one_pos]
        exact Filter.prod_mono le_rfl (nhdsWithin_mono _ Ico_subset_Icc_self)
      · simp [hf]
    · refine (((h (s, 0) ⟨trivial, le_rfl, zero_le_one⟩).tendsto.mono_left <| le_of_eq ?_).comp
        (tendsto_id.prodMap (tendsto_fract_right _))).mono_right (le_of_eq ?_) <;>
        simp [nhdsWithin_prod_eq, nhdsWithin_univ]
  · replace ht : t != ⌊t⌋ := fun ht' => ht ⟨_, ht'⟩
    refine (h.continuousAt ?_).comp (continuousAt_id.prodMap (continuousAt_fract ht))
    exact prod_mem_nhds univ_mem (Icc_mem_nhds (fract_pos.2 ht) (fract_lt_one _))

/--
theorem `ContinuousOn.comp_fract` / 定理 `ContinuousOn.comp_fract`

English:
theorem ContinuousOn.comp_fract
  statement: {s : β -> α} {f : β -> α -> γ}
  proof: (h.comp_fract' hf).comp (continuous_id.prodMk hs)

中文:
定理 ContinuousOn.comp_fract
  结论: {s : β -> α} {f : β -> α -> γ}
  证明: (h.comp_fract' hf).comp (continuous_id.prodMk hs)
-/
theorem ContinuousOn.comp_fract {s : β -> α} {f : β -> α -> γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
(hf : forall s, f s 0 = f s 1) : Continuous fun x : β => f x Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prodMk hs)

/--
theorem `ContinuousOn.comp_fract''` / 定理 `ContinuousOn.comp_fract''`

English:
theorem ContinuousOn.comp_fract''
  given: {f : α -> β} (h : ContinuousOn f I) (hf : f 0 = f 1)
  proof: ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf

中文:
定理 ContinuousOn.comp_fract''
  条件: {f : α -> β} (h : ContinuousOn f I) (hf : f 0 = f 1)
  证明: ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf

Depends on / 依赖: ContinuousOn, ContinuousOn.comp_fract, comp_fract, continuousOn_snd, continuous_id, h.comp, mem_prod, mem_prod.mp
-/
theorem ContinuousOn.comp_fract'' {f : α -> β} (h : ContinuousOn f I) (hf : f 0 = f 1) :
    Continuous (f ∘ fract) :=
  ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf
