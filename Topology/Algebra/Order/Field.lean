/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.
-/

public section


open Set Filter TopologicalSpace Function
open scoped Pointwise Topology
open OrderDual (toDual ofDual)

section Semifield

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α -> 𝕜}

/--
theorem `Filter.Tendsto.atTop_mul_pos` / 定理 `Filter.Tendsto.atTop_mul_pos`

English:
theorem Filter.Tendsto.atTop_mul_pos
  statement: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
  proof: by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

中文:
定理 Filter.Tendsto.atTop_mul_pos
  结论: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
  证明: by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

Depends on / 依赖: atTop_mul_const, eventually, eventually_ge_atTop, filter_upwards, half_lt_self, half_pos, hf.atTop_mul_const, hf.eventually_ge_atTop, hg.eventually, hg.le, lt_mem_nhds, mul_le_mul_of_nonneg_left, tendsto_atTop_mono
-/
theorem Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

-- TODO: after removing this deprecated alias,
-- rename `Filter.Tendsto.atTop_mul'` to `Filter.Tendsto.atTop_mul`.
-- Same for the other 3 similar aliases below.
/--
theorem `Filter.Tendsto.pos_mul_atTop` / 定理 `Filter.Tendsto.pos_mul_atTop`

English:
theorem Filter.Tendsto.pos_mul_atTop
  statement: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
  proof: by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf

@[simp]

中文:
定理 Filter.Tendsto.pos_mul_atTop
  结论: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
  证明: by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf

@[simp]

Depends on / 依赖: atTop_mul_pos, hg.atTop_mul_pos, mul_comm
-/
theorem Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf

@[simp]
/--
lemma `inv_atTop₀` / 引理 `inv_atTop₀`

English:
lemma inv_atTop₀
  statement: (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0
  proof: (((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis
    (nhdsGT_basis _).congr (by simp) fun a ha => by simp [inv_Ioi₀ (inv_pos.2 ha)]

@[simp]

中文:
引理 inv_atTop₀
  结论: (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0
  证明: (((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis
    (nhdsGT_basis _).congr (by simp) fun a ha => by simp [inv_Ioi₀ (inv_pos.2 ha)]

@[simp]

Depends on / 依赖: atTop_basis_Ioi, comp_surjective, eq_of_same_basis, inv_pos, inv_surjective, nhdsGT_basis
-/
lemma inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0 :=
(((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis
    (nhdsGT_basis _).congr (by simp) fun a ha => by simp [inv_Ioi₀ (inv_pos.2 ha)]

@[simp]
/--
lemma `inv_nhdsGT_zero` / 引理 `inv_nhdsGT_zero`

English:
lemma inv_nhdsGT_zero
  statement: (𝓝[>] (0 : 𝕜))⁻¹ = atTop
  proof: by rw [← inv_atTop₀, inv_inv]

中文:
引理 inv_nhdsGT_zero
  结论: (𝓝[>] (0 : 𝕜))⁻¹ = atTop
  证明: by rw [← inv_atTop₀, inv_inv]

Depends on / 依赖: inv_inv
-/
lemma inv_nhdsGT_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop := by rw [← inv_atTop₀, inv_inv]

/--
theorem `tendsto_inv_nhdsGT_zero` / 定理 `tendsto_inv_nhdsGT_zero`

English:
theorem tendsto_inv_nhdsGT_zero
  statement: Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
  proof: inv_nhdsGT_zero.le

中文:
定理 tendsto_inv_nhdsGT_zero
  结论: Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
  证明: inv_nhdsGT_zero.le

Depends on / 依赖: inv_nhdsGT_zero, inv_nhdsGT_zero.le
-/
theorem tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop :=
  inv_nhdsGT_zero.le

/--
theorem `tendsto_inv_atTop_nhdsGT_zero` / 定理 `tendsto_inv_atTop_nhdsGT_zero`

English:
theorem tendsto_inv_atTop_nhdsGT_zero
  statement: Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜))
  proof: inv_atTop₀.le

中文:
定理 tendsto_inv_atTop_nhdsGT_zero
  结论: Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜))
  证明: inv_atTop₀.le
-/
theorem tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜)) :=
  inv_atTop₀.le

/--
theorem `tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop` / 定理 `tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop`

English:
theorem tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  statement: {f : 𝕜 -> α}
  proof: by
  convert! h.comp tendsto_inv_nhdsGT_zero
  grind [inv_inv]

中文:
定理 tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  结论: {f : 𝕜 -> α}
  证明: by
  convert! h.comp tendsto_inv_nhdsGT_zero
  grind [inv_inv]

Depends on / 依赖: convert, h.comp, inv_inv, tendsto_inv_nhdsGT_zero
-/
theorem tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop {f : 𝕜 -> α}
    (h : Tendsto (fun x => f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  convert! h.comp tendsto_inv_nhdsGT_zero
  grind [inv_inv]

/--
theorem `tendsto_inv_atTop_zero` / 定理 `tendsto_inv_atTop_zero`

English:
theorem tendsto_inv_atTop_zero
  statement: Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0)
  proof: tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left

中文:
定理 tendsto_inv_atTop_zero
  结论: Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0)
  证明: tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_inv_atTop_nhdsGT_zero, tendsto_inv_atTop_nhdsGT_zero.mono_right
-/
theorem tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left

/--
theorem `Filter.Tendsto.inv_tendsto_atTop` / 定理 `Filter.Tendsto.inv_tendsto_atTop`

English:
theorem Filter.Tendsto.inv_tendsto_atTop
  given: (h : Tendsto f l atTop)
  statement: Tendsto f⁻¹ l (𝓝 0)
  proof: tendsto_inv_atTop_zero.comp h

中文:
定理 Filter.Tendsto.inv_tendsto_atTop
  条件: (h : Tendsto f l atTop)
  结论: Tendsto f⁻¹ l (𝓝 0)
  证明: tendsto_inv_atTop_zero.comp h

Depends on / 依赖: tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp
-/
theorem Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp h

/--
theorem `Filter.Tendsto.inv_tendsto_nhdsGT_zero` / 定理 `Filter.Tendsto.inv_tendsto_nhdsGT_zero`

English:
theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero
  given: (h : Tendsto f l (𝓝[>] 0))
  statement: Tendsto f⁻¹ l atTop
  proof: tendsto_inv_nhdsGT_zero.comp h

中文:
定理 Filter.Tendsto.inv_tendsto_nhdsGT_zero
  条件: (h : Tendsto f l (𝓝[>] 0))
  结论: Tendsto f⁻¹ l atTop
  证明: tendsto_inv_nhdsGT_zero.comp h

Depends on / 依赖: tendsto_inv_nhdsGT_zero, tendsto_inv_nhdsGT_zero.comp
-/
theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop :=
  tendsto_inv_nhdsGT_zero.comp h

/--
theorem `tendsto_pow_neg_atTop` / 定理 `tendsto_pow_neg_atTop`

English:
theorem tendsto_pow_neg_atTop
  given: {n : Nat} (hn : n != 0)
  proof: by
  simpa only [zpow_neg, zpow_natCast] using! (tendsto_pow_atTop (α := 𝕜) hn).inv_tendsto_atTop

中文:
定理 tendsto_pow_neg_atTop
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  simpa only [zpow_neg, zpow_natCast] using! (tendsto_pow_atTop (α := 𝕜) hn).inv_tendsto_atTop

Depends on / 依赖: inv_tendsto_atTop, tendsto_pow_atTop, zpow_natCast, zpow_neg
-/
theorem tendsto_pow_neg_atTop {n : Nat} (hn : n != 0) :
    Tendsto (fun x : 𝕜 => x ^ (-(n : Int))) atTop (𝓝 0) := by
  simpa only [zpow_neg, zpow_natCast] using! (tendsto_pow_atTop (α := 𝕜) hn).inv_tendsto_atTop

/--
theorem `tendsto_zpow_atTop_zero` / 定理 `tendsto_zpow_atTop_zero`

English:
theorem tendsto_zpow_atTop_zero
  given: {n : Int} (hn : n < 0)
  proof: by
  lift -n to Nat using le_of_lt (neg_pos.mpr hn) with N h
  rw [← neg_pos]; rw [← h]; rw [Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'

中文:
定理 tendsto_zpow_atTop_zero
  条件: {n : 整数} (hn : n < 0)
  证明: by
  lift -n to Nat using le_of_lt (neg_pos.mpr hn) with N h
  rw [← neg_pos]; rw [← h]; rw [Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'

Depends on / 依赖: Nat.cast_pos, cast_pos, hn.ne, le_of_lt, neg_neg, neg_pos, neg_pos.mpr, tendsto_pow_neg_atTop
-/
theorem tendsto_zpow_atTop_zero {n : Int} (hn : n < 0) :
    Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0) := by
  lift -n to Nat using le_of_lt (neg_pos.mpr hn) with N h
  rw [← neg_pos]; rw [← h]; rw [Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toContinuousInv₀ [ContinuousMul 𝕜] :
ContinuousInv₀ 𝕜 := .of_nhds_one tendsto_order.2 by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', h₀, hxx', h₁⟩ : exists x', 0 < x' ∧ x <= x' ∧ x' < 1 :=
      ⟨max x (1 / 2), one_half_pos.trans_le (le_max_right _ _), le_max_left _ _,
        max_lt hx one_half_lt_one⟩
    filter_upwards [Ioo_mem_nhds one_pos ((one_lt_inv₀ h₀).2 h₁)] with y hy
exact hxx'.trans_lt lt_inv_of_lt_inv₀ hy.1 hy.2
  · filter_upwards [Ioi_mem_nhds (inv_lt_one_of_one_lt₀ hx)] with y hy
    exact inv_lt_of_inv_lt₀ (by positivity) hy

end Semifield

/--
theorem `IsTopologicalRing.of_norm` / 定理 `IsTopologicalRing.of_norm`

English:
theorem IsTopologicalRing.of_norm
  statement: {R 𝕜 : Type*} [NonUnitalNonAssocRing R]
  proof: by
  have h0 : forall f : R -> R, forall c >= (0 : 𝕜), (forall x, norm (f x) <= c * norm x) ->
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf => (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 => ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx => (hf _).t

中文:
定理 IsTopologicalRing.of_norm
  结论: {R 𝕜 : 类型} [NonUnitalNonAssocRing R]
  证明: by
  have h0 : forall f : R -> R, forall c >= (0 : 𝕜), (forall x, norm (f x) <= c * norm x) ->
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf => (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 => ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx => (hf _).t

Depends on / 依赖: IsTopologicalRing, IsTopologicalRing.of_addGroup_of_nhds_zero, Tendsto, exists_pos_mul_lt, le_of_lt, mul_le_mul_of_nonneg_left, nhds_basis, nhds_basis.prod, nhds_basis.tendsto_iff, of_addGroup_of_nhds_zero, tendsto_iff, trans_lt
-/
theorem IsTopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace R] [IsTopologicalAddGroup R] (norm : R -> 𝕜)
    (norm_nonneg : forall x, 0 <= norm x) (norm_mul_le : forall x y, norm (x * y) <= norm x * norm y)
    (nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (fun ε => { x | norm x < ε })) :
    IsTopologicalRing R := by
  have h0 : forall f : R -> R, forall c >= (0 : 𝕜), (forall x, norm (f x) <= c * norm x) ->
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf => (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 => ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx => (hf _).trans_lt ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_of_lt hx) c0).trans_lt hδ
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  case hmul =>
    refine ((nhds_basis.prod nhds_basis).tendsto_iff nhds_basis).2 fun ε ε0 => ?_
    refine ⟨(1, ε), ⟨one_pos, ε0⟩, fun (x, y) ⟨hx, hy⟩ => ?_⟩
    simp only at *
    calc norm (x * y) <= norm x * norm y := norm_mul_le _ _
    _ < ε := (mul_le_of_le_one_left (norm_nonneg _) hx.le).trans_lt hy
  case hmul_left => exact fun x => h0 _ (norm x) (norm_nonneg _) (norm_mul_le x)
  case hmul_right =>
    exact fun y => h0 (· * y) (norm y) (norm_nonneg y) fun x =>
      (norm_mul_le x y).trans_eq (mul_comm _ _)

variable {𝕜 α : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α -> 𝕜}

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.topologicalRing : IsTopologicalRing 𝕜 :=
.of_norm abs abs_nonneg (fun _ _ => (abs_mul _ _).le) by
    simpa using nhds_basis_abs_sub_lt (0 : 𝕜)

/--
theorem `Filter.Tendsto.atTop_mul_neg` / 定理 `Filter.Tendsto.atTop_mul_neg`

English:
theorem Filter.Tendsto.atTop_mul_neg
  statement: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
  proof: by
  have := hf.atTop_mul_pos (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

中文:
定理 Filter.Tendsto.atTop_mul_neg
  结论: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
  证明: by
  have := hf.atTop_mul_pos (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

Depends on / 依赖: Function, Function.comp_def, atTop_mul_pos, comp_def, hf.atTop_mul_pos, hg.neg, neg_mul_eq_mul_neg, neg_neg, neg_pos, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.comp
-/
theorem Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul_pos (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/--
theorem `Filter.Tendsto.neg_mul_atTop` / 定理 `Filter.Tendsto.neg_mul_atTop`

English:
theorem Filter.Tendsto.neg_mul_atTop
  statement: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
  proof: by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

中文:
定理 Filter.Tendsto.neg_mul_atTop
  结论: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
  证明: by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

Depends on / 依赖: atTop_mul_neg, hg.atTop_mul_neg, mul_comm
-/
theorem Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

/--
theorem `Filter.Tendsto.atBot_mul_pos` / 定理 `Filter.Tendsto.atBot_mul_pos`

English:
theorem Filter.Tendsto.atBot_mul_pos
  statement: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
  proof: by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_pos hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

中文:
定理 Filter.Tendsto.atBot_mul_pos
  结论: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
  证明: by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_pos hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

Depends on / 依赖: Function, Function.comp_def, atTop_mul_pos, comp_def, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.comp
-/
theorem Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_pos hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

/--
theorem `Filter.Tendsto.atBot_mul_neg` / 定理 `Filter.Tendsto.atBot_mul_neg`

English:
theorem Filter.Tendsto.atBot_mul_neg
  statement: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
  proof: by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

中文:
定理 Filter.Tendsto.atBot_mul_neg
  结论: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
  证明: by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

Depends on / 依赖: Function, Function.comp_def, atTop_mul_neg, comp_def, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp
-/
theorem Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

/--
theorem `Filter.Tendsto.pos_mul_atBot` / 定理 `Filter.Tendsto.pos_mul_atBot`

English:
theorem Filter.Tendsto.pos_mul_atBot
  statement: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
  proof: by
  simpa only [mul_comm] using hg.atBot_mul_pos hC hf

中文:
定理 Filter.Tendsto.pos_mul_atBot
  结论: {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
  证明: by
  simpa only [mul_comm] using hg.atBot_mul_pos hC hf

Depends on / 依赖: atBot_mul_pos, hg.atBot_mul_pos, mul_comm
-/
theorem Filter.Tendsto.pos_mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atBot_mul_pos hC hf

/--
theorem `Filter.Tendsto.neg_mul_atBot` / 定理 `Filter.Tendsto.neg_mul_atBot`

English:
theorem Filter.Tendsto.neg_mul_atBot
  statement: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
  proof: by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

@[simp]

中文:
定理 Filter.Tendsto.neg_mul_atBot
  结论: {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
  证明: by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

@[simp]

Depends on / 依赖: atBot_mul_neg, hg.atBot_mul_neg, mul_comm
-/
theorem Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

@[simp]
/--
lemma `inv_atBot₀` / 引理 `inv_atBot₀`

English:
lemma inv_atBot₀
  statement: (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0
  proof: (((atBot_basis_Iio' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis
    (nhdsLT_basis _).congr (by simp) fun a ha => by simp [inv_Iio₀ (inv_neg''.2 ha)]

@[simp]

中文:
引理 inv_atBot₀
  结论: (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0
  证明: (((atBot_basis_Iio' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis
    (nhdsLT_basis _).congr (by simp) fun a ha => by simp [inv_Iio₀ (inv_neg''.2 ha)]

@[simp]

Depends on / 依赖: atBot_basis_Iio, comp_surjective, eq_of_same_basis, inv_neg, inv_surjective, nhdsLT_basis
-/
lemma inv_atBot₀ : (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0 :=
(((atBot_basis_Iio' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis
    (nhdsLT_basis _).congr (by simp) fun a ha => by simp [inv_Iio₀ (inv_neg''.2 ha)]

@[simp]
/--
lemma `inv_nhdsLT_zero` / 引理 `inv_nhdsLT_zero`

English:
lemma inv_nhdsLT_zero
  statement: (𝓝[<] (0 : 𝕜))⁻¹ = atBot
  proof: by
  rw [← inv_atBot₀]; rw [inv_inv]

中文:
引理 inv_nhdsLT_zero
  结论: (𝓝[<] (0 : 𝕜))⁻¹ = atBot
  证明: by
  rw [← inv_atBot₀]; rw [inv_inv]

Depends on / 依赖: inv_inv
-/
lemma inv_nhdsLT_zero : (𝓝[<] (0 : 𝕜))⁻¹ = atBot := by
  rw [← inv_atBot₀]; rw [inv_inv]

/--
theorem `tendsto_inv_nhdsLT_zero` / 定理 `tendsto_inv_nhdsLT_zero`

English:
theorem tendsto_inv_nhdsLT_zero
  statement: Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot
  proof: inv_nhdsLT_zero.le

中文:
定理 tendsto_inv_nhdsLT_zero
  结论: Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot
  证明: inv_nhdsLT_zero.le

Depends on / 依赖: inv_nhdsLT_zero, inv_nhdsLT_zero.le
-/
theorem tendsto_inv_nhdsLT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot :=
  inv_nhdsLT_zero.le

/--
theorem `tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot` / 定理 `tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot`

English:
theorem tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot
  statement: {f : 𝕜 -> α}
  proof: by
  convert! h.comp tendsto_inv_nhdsLT_zero
  grind

中文:
定理 tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot
  结论: {f : 𝕜 -> α}
  证明: by
  convert! h.comp tendsto_inv_nhdsLT_zero
  grind

Depends on / 依赖: convert, h.comp, tendsto_inv_nhdsLT_zero
-/
theorem tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot {f : 𝕜 -> α}
    (h : Tendsto (fun x => f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  convert! h.comp tendsto_inv_nhdsLT_zero
  grind

/--
theorem `tendsto_inv_atBot_nhdsLT_zero` / 定理 `tendsto_inv_atBot_nhdsLT_zero`

English:
theorem tendsto_inv_atBot_nhdsLT_zero
  statement: Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜))
  proof: inv_atBot₀.le

中文:
定理 tendsto_inv_atBot_nhdsLT_zero
  结论: Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜))
  证明: inv_atBot₀.le
-/
theorem tendsto_inv_atBot_nhdsLT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜)) :=
  inv_atBot₀.le

/--
theorem `tendsto_inv_atBot_zero` / 定理 `tendsto_inv_atBot_zero`

English:
theorem tendsto_inv_atBot_zero
  statement: Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0)
  proof: tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left

中文:
定理 tendsto_inv_atBot_zero
  结论: Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0)
  证明: tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_inv_atBot_nhdsLT_zero, tendsto_inv_atBot_nhdsLT_zero.mono_right
-/
theorem tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0) :=
  tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left

/--
theorem `Filter.Tendsto.div_atTop` / 定理 `Filter.Tendsto.div_atTop`

English:
theorem Filter.Tendsto.div_atTop
  given: {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop)
  proof: by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atTop_zero.comp hg)

中文:
定理 Filter.Tendsto.div_atTop
  条件: {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop)
  证明: by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atTop_zero.comp hg)

Depends on / 依赖: div_eq_mul_inv, h.mul, mul_zero, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp
-/
theorem Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atTop_zero.comp hg)

/--
theorem `Filter.Tendsto.div_atBot` / 定理 `Filter.Tendsto.div_atBot`

English:
theorem Filter.Tendsto.div_atBot
  given: {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atBot)
  proof: by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atBot_zero.comp hg)

中文:
定理 Filter.Tendsto.div_atBot
  条件: {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atBot)
  证明: by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atBot_zero.comp hg)

Depends on / 依赖: div_eq_mul_inv, h.mul, mul_zero, tendsto_inv_atBot_zero, tendsto_inv_atBot_zero.comp
-/
theorem Filter.Tendsto.div_atBot {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atBot_zero.comp hg)

/--
lemma `Filter.Tendsto.const_div_atTop` / 引理 `Filter.Tendsto.const_div_atTop`

English:
lemma Filter.Tendsto.const_div_atTop
  given: (hg : Tendsto g l atTop) (r : 𝕜)
  proof: tendsto_const_nhds.div_atTop hg

中文:
引理 Filter.Tendsto.const_div_atTop
  条件: (hg : Tendsto g l atTop) (r : 𝕜)
  证明: tendsto_const_nhds.div_atTop hg

Depends on / 依赖: div_atTop, tendsto_const_nhds, tendsto_const_nhds.div_atTop
-/
lemma Filter.Tendsto.const_div_atTop (hg : Tendsto g l atTop) (r : 𝕜) :
    Tendsto (fun n => r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atTop hg

/--
lemma `Filter.Tendsto.const_div_atBot` / 引理 `Filter.Tendsto.const_div_atBot`

English:
lemma Filter.Tendsto.const_div_atBot
  given: (hg : Tendsto g l atBot) (r : 𝕜)
  proof: tendsto_const_nhds.div_atBot hg

中文:
引理 Filter.Tendsto.const_div_atBot
  条件: (hg : Tendsto g l atBot) (r : 𝕜)
  证明: tendsto_const_nhds.div_atBot hg

Depends on / 依赖: div_atBot, tendsto_const_nhds, tendsto_const_nhds.div_atBot
-/
lemma Filter.Tendsto.const_div_atBot (hg : Tendsto g l atBot) (r : 𝕜) :
    Tendsto (fun n => r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atBot hg

/--
theorem `Filter.Tendsto.inv_tendsto_atBot` / 定理 `Filter.Tendsto.inv_tendsto_atBot`

English:
theorem Filter.Tendsto.inv_tendsto_atBot
  given: (h : Tendsto f l atBot)
  statement: Tendsto f⁻¹ l (𝓝 0)
  proof: tendsto_inv_atBot_zero.comp h

中文:
定理 Filter.Tendsto.inv_tendsto_atBot
  条件: (h : Tendsto f l atBot)
  结论: Tendsto f⁻¹ l (𝓝 0)
  证明: tendsto_inv_atBot_zero.comp h

Depends on / 依赖: tendsto_inv_atBot_zero, tendsto_inv_atBot_zero.comp
-/
theorem Filter.Tendsto.inv_tendsto_atBot (h : Tendsto f l atBot) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atBot_zero.comp h

/--
theorem `Filter.Tendsto.inv_tendsto_nhdsLT_zero` / 定理 `Filter.Tendsto.inv_tendsto_nhdsLT_zero`

English:
theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero
  given: (h : Tendsto f l (𝓝[<] 0))
  statement: Tendsto f⁻¹ l atBot
  proof: tendsto_inv_nhdsLT_zero.comp h

中文:
定理 Filter.Tendsto.inv_tendsto_nhdsLT_zero
  条件: (h : Tendsto f l (𝓝[<] 0))
  结论: Tendsto f⁻¹ l atBot
  证明: tendsto_inv_nhdsLT_zero.comp h

Depends on / 依赖: tendsto_inv_nhdsLT_zero, tendsto_inv_nhdsLT_zero.comp
-/
theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero (h : Tendsto f l (𝓝[<] 0)) : Tendsto f⁻¹ l atBot :=
  tendsto_inv_nhdsLT_zero.comp h

/--
theorem `bdd_le_mul_tendsto_zero'` / 定理 `bdd_le_mul_tendsto_zero'`

English:
theorem bdd_le_mul_tendsto_zero'
  statement: {f g : α -> 𝕜} (C : 𝕜) (hf : forallᶠ x in l, |f x| <= C)
  proof: by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x => |C * g x|) l (𝓝 0) := by
    convert! (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filte

中文:
定理 bdd_le_mul_tendsto_zero'
  结论: {f g : α -> 𝕜} (C : 𝕜) (hf : 对任意ᶠ x in l, |f x| <= C)
  证明: by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x => |C * g x|) l (𝓝 0) := by
    convert! (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filte

Depends on / 依赖: Tendsto, abs_mul, abs_nonneg, abs_zero, comp_apply, const_mul, convert, filter_upwards, hg.const_mul, hx.trans, le_abs_self, mul_le_mul_of_nonneg_right, mul_zero, simp_rw, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_zero_iff_abs_tendsto_zero
-/
theorem bdd_le_mul_tendsto_zero' {f g : α -> 𝕜} (C : 𝕜) (hf : forallᶠ x in l, |f x| <= C)
    (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x => f x * g x) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x => |C * g x|) l (𝓝 0) := by
    convert! (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filter_upwards [hf] with x hx
    simp only [comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _)

/--
theorem `bdd_le_mul_tendsto_zero` / 定理 `bdd_le_mul_tendsto_zero`

English:
theorem bdd_le_mul_tendsto_zero
  statement: {f g : α -> 𝕜} {b B : 𝕜} (hb : forallᶠ x in l, b <= f x)
  proof: by
  set C := max |b| |B|
  have hbC : -C <= b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B <= C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx => abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

中文:
定理 bdd_le_mul_tendsto_zero
  结论: {f g : α -> 𝕜} {b B : 𝕜} (hb : 对任意ᶠ x in l, b <= f x)
  证明: by
  set C := max |b| |B|
  have hbC : -C <= b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B <= C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx => abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

Depends on / 依赖: abs_le, abs_le.mpr, bdd_le_mul_tendsto_zero, filter_upwards, hBx.trans, hbC.trans, le_abs_self, le_max_of_le_left, le_max_of_le_right, neg_le, neg_le.mpr, neg_le_abs
-/
theorem bdd_le_mul_tendsto_zero {f g : α -> 𝕜} {b B : 𝕜} (hb : forallᶠ x in l, b <= f x)
    (hB : forallᶠ x in l, f x <= B) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) := by
  set C := max |b| |B|
  have hbC : -C <= b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B <= C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx => abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

/--
theorem `tendsto_bdd_div_atTop_nhds_zero` / 定理 `tendsto_bdd_div_atTop_nhds_zero`

English:
theorem tendsto_bdd_div_atTop_nhds_zero
  statement: {f g : α -> 𝕜} {b B : 𝕜}
  proof: by
  simp only [div_eq_mul_inv]
  exact bdd_le_mul_tendsto_zero hb hB hg.inv_tendsto_atTop

中文:
定理 tendsto_bdd_div_atTop_nhds_zero
  结论: {f g : α -> 𝕜} {b B : 𝕜}
  证明: by
  simp only [div_eq_mul_inv]
  exact bdd_le_mul_tendsto_zero hb hB hg.inv_tendsto_atTop

Depends on / 依赖: bdd_le_mul_tendsto_zero, div_eq_mul_inv, hg.inv_tendsto_atTop, inv_tendsto_atTop
-/
theorem tendsto_bdd_div_atTop_nhds_zero {f g : α -> 𝕜} {b B : 𝕜}
    (hb : forallᶠ x in l, b <= f x) (hB : forallᶠ x in l, f x <= B) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact bdd_le_mul_tendsto_zero hb hB hg.inv_tendsto_atTop

/--
theorem `tendsto_const_mul_zpow_atTop_zero` / 定理 `tendsto_const_mul_zpow_atTop_zero`

English:
theorem tendsto_const_mul_zpow_atTop_zero
  given: {n : Int} {c : 𝕜} (hn : n < 0)
  proof: mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)

中文:
定理 tendsto_const_mul_zpow_atTop_zero
  条件: {n : 整数} {c : 𝕜} (hn : n < 0)
  证明: mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)

Depends on / 依赖: Filter, Filter.Tendsto.const_mul, Tendsto, const_mul, mul_zero, tendsto_zpow_atTop_zero
-/
theorem tendsto_const_mul_zpow_atTop_zero {n : Int} {c : 𝕜} (hn : n < 0) :
    Tendsto (fun x => c * x ^ n) atTop (𝓝 0) :=
  mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)

/--
theorem `tendsto_const_mul_pow_nhds_iff'` / 定理 `tendsto_const_mul_pow_nhds_iff'`

English:
theorem tendsto_const_mul_pow_nhds_iff'
  given: {n : Nat} {c d : 𝕜}
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_atBot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_m

中文:
定理 tendsto_const_mul_pow_nhds_iff'
  条件: {n : 自然数} {c d : 𝕜}
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_atBot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_m

Depends on / 依赖: eq_or_ne, hc.ne, lt_trichotomy, not_tendsto_nhds_of_tendsto_atBot, not_tendsto_nhds_of_tendsto_atTop, tendsto_const_mul_pow_atBot_iff, tendsto_const_mul_pow_atTop_iff, tendsto_const_nhds_iff
-/
theorem tendsto_const_mul_pow_nhds_iff' {n : Nat} {c d : 𝕜} :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_atBot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_mul_pow_atTop_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atTop this, hc.ne', hn]

/--
theorem `tendsto_const_mul_pow_nhds_iff` / 定理 `tendsto_const_mul_pow_nhds_iff`

English:
theorem tendsto_const_mul_pow_nhds_iff
  given: {n : Nat} {c d : 𝕜} (hc : c != 0)
  proof: by
  simp [tendsto_const_mul_pow_nhds_iff', hc]

中文:
定理 tendsto_const_mul_pow_nhds_iff
  条件: {n : 自然数} {c d : 𝕜} (hc : c != 0)
  证明: by
  simp [tendsto_const_mul_pow_nhds_iff', hc]

Depends on / 依赖: tendsto_const_mul_pow_nhds_iff
-/
theorem tendsto_const_mul_pow_nhds_iff {n : Nat} {c d : 𝕜} (hc : c != 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d := by
  simp [tendsto_const_mul_pow_nhds_iff', hc]

/--
theorem `tendsto_const_mul_zpow_atTop_nhds_iff` / 定理 `tendsto_const_mul_zpow_atTop_nhds_iff`

English:
theorem tendsto_const_mul_zpow_atTop_nhds_iff
  given: {n : Int} {c d : 𝕜} (hc : c != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h wit

中文:
定理 tendsto_const_mul_zpow_atTop_nhds_iff
  条件: {n : 整数} {c d : 𝕜} (hc : c != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h wit

Depends on / 依赖: Int.negSucc_lt_zero, Or.inr, h.left, h.right, mul_one, negSucc, negSucc_lt_zero, tendsto_const_mul_pow_nhds_iff, tendsto_const_mul_zpow_atTop_zero, tendsto_const_nhds, tendsto_nhds_unique, zpow_zero
-/
theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : Int} {c d : 𝕜} (hc : c != 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h with h | h
    · simp only [h.left, h.right, zpow_zero, mul_one]
      exact tendsto_const_nhds
    · exact h.2.symm ▸ tendsto_const_mul_zpow_atTop_zero h.1

instance (priority := 100) IsStrictOrderedRing.toIsTopologicalDivisionRing :
    IsTopologicalDivisionRing 𝕜 := ⟨⟩

-- TODO: generalize to a `GroupWithZero`
/--
theorem `comap_mulLeft_nhdsGT_zero` / 定理 `comap_mulLeft_nhdsGT_zero`

English:
theorem comap_mulLeft_nhdsGT_zero
  given: {x : 𝕜} (hx : 0 < x)
  statement: comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0
  proof: by
  rw [nhdsWithin]; rw [comap_inf]; rw [comap_principal]; rw [preimage_const_mul_Ioi₀ _ hx]; rw [zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp

中文:
定理 comap_mulLeft_nhdsGT_zero
  条件: {x : 𝕜} (hx : 0 < x)
  结论: comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0
  证明: by
  rw [nhdsWithin]; rw [comap_inf]; rw [comap_principal]; rw [preimage_const_mul_Ioi₀ _ hx]; rw [zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, comap_inf, comap_nhds_eq, comap_principal, hx.ne, nhdsWithin, zero_div
-/
theorem comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x) : comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0 := by
  rw [nhdsWithin]; rw [comap_inf]; rw [comap_principal]; rw [preimage_const_mul_Ioi₀ _ hx]; rw [zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp

/--
theorem `eventually_nhdsGT_zero_mul_left` / 定理 `eventually_nhdsGT_zero_mul_left`

English:
theorem eventually_nhdsGT_zero_mul_left
  statement: {x : 𝕜} (hx : 0 < x) {p : 𝕜 -> Prop}
  proof: by
  rw [← comap_mulLeft_nhdsGT_zero hx]
  exact h.comap fun ε => x * ε

中文:
定理 eventually_nhdsGT_zero_mul_left
  结论: {x : 𝕜} (hx : 0 < x) {p : 𝕜 -> 命题}
  证明: by
  rw [← comap_mulLeft_nhdsGT_zero hx]
  exact h.comap fun ε => x * ε

Depends on / 依赖: comap_mulLeft_nhdsGT_zero, h.comap
-/
theorem eventually_nhdsGT_zero_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 -> Prop}
    (h : forallᶠ ε in 𝓝[>] 0, p ε) : forallᶠ ε in 𝓝[>] 0, p (x * ε) := by
  rw [← comap_mulLeft_nhdsGT_zero hx]
  exact h.comap fun ε => x * ε
