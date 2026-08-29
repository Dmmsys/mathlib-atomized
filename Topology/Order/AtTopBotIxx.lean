/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.Limit
import Mathlib.Topology.Order.LeftRightNhds

/-!
# `Filter.atTop` and `Filter.atBot` for intervals in a linear order topology

Let `X` be a linear order with order topology.
Let `a` be a point that is either the bottom element of `X` or is not isolated on the left,
see `Order.IsSuccPrelimit`.
Then the `Filter.atTop` filter on `Set.Iio a` and `𝓝[<] a` are related by the coercion map
via pushforward and pullback, see `map_coe_Iio_atTop` and `comap_coe_Iio_nhdsLT`.

We prove several versions of this statement for `Set.Iio`, `Set.Ioi`, and `Set.Ioo`,
as well as `Filter.atTop` and `Filter.atBot`.

The assumption on `a` is automatically satisfied for densely ordered types,
see `Order.IsSuccPrelimit.of_dense`.
-/

public section

open Set Filter Order OrderDual
open scoped Topology

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  {s : Set X} {a b : X}

/--
theorem `comap_coe_nhdsLT_eq_atTop_iff` / 定理 `comap_coe_nhdsLT_eq_atTop_iff`

English:
theorem comap_coe_nhdsLT_eq_atTop_iff
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [eq_iff_true_of_subsingleton]
  have := hsne.to_subtype
  simp only [hsne, true_imp_iff]
  by_cases hsub : s subseteq Iio b
  · simp only [hsub, true_and]
    constructor
    · intro h a ha
      have := preimage_mem_comap (m := ((↑) : s ->

中文:
定理 comap_coe_nhdsLT_eq_atTop_iff
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [eq_iff_true_of_subsingleton]
  have := hsne.to_subtype
  simp only [hsne, true_imp_iff]
  by_cases hsub : s subseteq Iio b
  · simp only [hsub, true_and]
    constructor
    · intro h a ha
      have := preimage_mem_comap (m := ((↑) : s ->

Depends on / 依赖: Filter, Filter.nonempty_of_mem, Ioo_mem_nhdsLT, atTop_basis, eq_empty_or_nonempty, eq_iff_true_of_subsingleton, hsne.mono, hsne.to_subtype, nhdsLT_basis_of_exists_lt, nonempty_of_mem, preimage_mem_comap, s.eq_empty_or_nonempty, subseteq, to_subtype, true_and, true_imp_iff
-/
theorem comap_coe_nhdsLT_eq_atTop_iff :
    comap ((↑) : s -> X) (𝓝[<] b) = atTop ↔
      s subseteq Iio b ∧ (s.Nonempty -> forall a < b, (s inter Ioo a b).Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [eq_iff_true_of_subsingleton]
  have := hsne.to_subtype
  simp only [hsne, true_imp_iff]
  by_cases hsub : s subseteq Iio b
  · simp only [hsub, true_and]
    constructor
    · intro h a ha
      have := preimage_mem_comap (m := ((↑) : s -> X)) (Ioo_mem_nhdsLT ha)
      rw [h] at this
      rcases Filter.nonempty_of_mem this with ⟨⟨c, hcs⟩, hc⟩
      exact ⟨c, hcs, hc⟩
    · intro h
.ext atTop_basis ?_ ?_ refine (nhdsLT_basis_of_exists_lt (hsne.mono hsub)).comap _
      · intro a hab
        rcases h a hab with ⟨c, hcs, hc⟩
        use ⟨c, hcs⟩
        simp_all [subset_def, hc.1.trans_le]
      · rintro ⟨a, has⟩ -
        use a, hsub has
        simp_all [subset_def, le_of_lt]
  · suffices ¬Tendsto (↑) (atTop : Filter s) (𝓝[<] b) by
      contrapose this
      simp_all [tendsto_iff_comap]
    intro h
    rcases not_subset_iff_exists_mem_notMem.mp hsub with ⟨a, has, ha⟩
.exists .and (eventually_ge_atTop ⟨a, has⟩) rcases h.eventually eventually_mem_nhdsWithin
      with ⟨⟨c, hcs⟩, hcb, hac⟩
    apply lt_irrefl a
    calc
      a <= c := by simpa using hac
      _ < b := by simpa using hcb
      _ <= a := by simpa using ha

/--
theorem `comap_coe_nhdsGT_eq_atBot_iff` / 定理 `comap_coe_nhdsGT_eq_atBot_iff`

English:
theorem comap_coe_nhdsGT_eq_atBot_iff
  proof: by
  refine comap_coe_nhdsLT_eq_atTop_iff (s := OrderDual.ofDual ⁻¹' s) (b := OrderDual.toDual b)
.trans ?_
  simp [← preimage_inter, ofDual.surjective]

中文:
定理 comap_coe_nhdsGT_eq_atBot_iff
  证明: by
  refine comap_coe_nhdsLT_eq_atTop_iff (s := OrderDual.ofDual ⁻¹' s) (b := OrderDual.toDual b)
.trans ?_
  simp [← preimage_inter, ofDual.surjective]

Depends on / 依赖: OrderDual, OrderDual.ofDual, OrderDual.toDual, comap_coe_nhdsLT_eq_atTop_iff, ofDual, ofDual.surjective, preimage_inter, surjective, toDual
-/
theorem comap_coe_nhdsGT_eq_atBot_iff :
    comap ((↑) : s -> X) (𝓝[>] b) = atBot ↔
      s subseteq Ioi b ∧ (s.Nonempty -> forall a > b, (s inter Ioo b a).Nonempty) := by
  refine comap_coe_nhdsLT_eq_atTop_iff (s := OrderDual.ofDual ⁻¹' s) (b := OrderDual.toDual b)
.trans ?_
  simp [← preimage_inter, ofDual.surjective]

/--
theorem `comap_coe_nhdsLT_of_Ioo_subset` / 定理 `comap_coe_nhdsLT_of_Ioo_subset`

English:
theorem comap_coe_nhdsLT_of_Ioo_subset
  statement: (hsb : s subseteq Iio b) (hs : s.Nonempty -> exists a < b, Ioo a b subseteq s)
  proof: by
  rw [comap_coe_nhdsLT_eq_atTop_iff]
  refine ⟨hsb, fun hsne a ha => ?_⟩
  rcases hs hsne with ⟨c, hcb, hcs⟩
  rcases hb.lt_iff_exists_lt.mp (max_lt ha hcb) with ⟨x, hxb, hacx⟩
  rw [max_lt_iff] at hacx
  exact ⟨x, hcs ⟨hacx.2, hxb⟩, hacx.1, hxb⟩

中文:
定理 comap_coe_nhdsLT_of_Ioo_subset
  结论: (hsb : s subseteq 左无界右开区间 b) (hs : s.非空 -> 存在 a < b, 开区间 a b subseteq s)
  证明: by
  rw [comap_coe_nhdsLT_eq_atTop_iff]
  refine ⟨hsb, fun hsne a ha => ?_⟩
  rcases hs hsne with ⟨c, hcb, hcs⟩
  rcases hb.lt_iff_exists_lt.mp (max_lt ha hcb) with ⟨x, hxb, hacx⟩
  rw [max_lt_iff] at hacx
  exact ⟨x, hcs ⟨hacx.2, hxb⟩, hacx.1, hxb⟩

Depends on / 依赖: comap_coe_nhdsLT_eq_atTop_iff, hb.lt_iff_exists_lt.mp, lt_iff_exists_lt, max_lt, max_lt_iff, of_dense
-/
theorem comap_coe_nhdsLT_of_Ioo_subset (hsb : s subseteq Iio b) (hs : s.Nonempty -> exists a < b, Ioo a b subseteq s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : s -> X) (𝓝[<] b) = atTop := by
  rw [comap_coe_nhdsLT_eq_atTop_iff]
  refine ⟨hsb, fun hsne a ha => ?_⟩
  rcases hs hsne with ⟨c, hcb, hcs⟩
  rcases hb.lt_iff_exists_lt.mp (max_lt ha hcb) with ⟨x, hxb, hacx⟩
  rw [max_lt_iff] at hacx
  exact ⟨x, hcs ⟨hacx.2, hxb⟩, hacx.1, hxb⟩

/--
theorem `comap_coe_nhdsGT_of_Ioo_subset` / 定理 `comap_coe_nhdsGT_of_Ioo_subset`

English:
theorem comap_coe_nhdsGT_of_Ioo_subset
  statement: (hsa : s subseteq Ioi a) (hs : s.Nonempty -> exists b > a, Ioo a b subseteq s)
  proof: by
  refine comap_coe_nhdsLT_of_Ioo_subset (show ofDual ⁻¹' s subseteq Iio (toDual a) from hsa) ?_ ha.dual
  simpa only [OrderDual.exists, Ioo_toDual]

中文:
定理 comap_coe_nhdsGT_of_Ioo_subset
  结论: (hsa : s subseteq 左开右无界区间 a) (hs : s.非空 -> 存在 b > a, 开区间 a b subseteq s)
  证明: by
  refine comap_coe_nhdsLT_of_Ioo_subset (show ofDual ⁻¹' s subseteq Iio (toDual a) from hsa) ?_ ha.dual
  simpa only [OrderDual.exists, Ioo_toDual]

Depends on / 依赖: Ioo_toDual, OrderDual, OrderDual.exists, comap_coe_nhdsLT_of_Ioo_subset, ha.dual, ofDual, of_dense, subseteq, toDual
-/
theorem comap_coe_nhdsGT_of_Ioo_subset (hsa : s subseteq Ioi a) (hs : s.Nonempty -> exists b > a, Ioo a b subseteq s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : s -> X) (𝓝[>] a) = atBot := by
  refine comap_coe_nhdsLT_of_Ioo_subset (show ofDual ⁻¹' s subseteq Iio (toDual a) from hsa) ?_ ha.dual
  simpa only [OrderDual.exists, Ioo_toDual]

/--
theorem `map_coe_atTop_of_Ioo_subset` / 定理 `map_coe_atTop_of_Ioo_subset`

English:
theorem map_coe_atTop_of_Ioo_subset
  statement: (hsb : s subseteq Iio b) (hs : forall a' < b, exists a < b, Ioo a b subseteq s)
  proof: by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop]; rw [Filter.map_bot]; rw [hb']; rw [nhdsWithin_empty]
  · rw [← comap_coe_nhdsLT_of_Ioo_subset hsb (fun _ => hs a ha) hb, map_comap_of_mem]
  

中文:
定理 map_coe_atTop_of_Ioo_subset
  结论: (hsb : s subseteq 左无界右开区间 b) (hs : 对任意 a' < b, 存在 a < b, 开区间 a b subseteq s)
  证明: by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop]; rw [Filter.map_bot]; rw [hb']; rw [nhdsWithin_empty]
  · rw [← comap_coe_nhdsLT_of_Ioo_subset hsb (fun _ => hs a ha) hb, map_comap_of_mem]
  

Depends on / 依赖: Filter, Filter.map_bot, IsEmpty, Subtype, Subtype.range_val, comap_coe_nhdsLT_of_Ioo_subset, eq_empty_or_nonempty, filter_eq_bot_of_isEmpty, map_bot, map_comap_of_mem, mem_nhdsLT_iff_exists_Ioo_subset, nhdsWithin_empty, of_dense, range_val, subset
-/
theorem map_coe_atTop_of_Ioo_subset (hsb : s subseteq Iio b) (hs : forall a' < b, exists a < b, Ioo a b subseteq s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : s -> X) atTop = 𝓝[<] b := by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop]; rw [Filter.map_bot]; rw [hb']; rw [nhdsWithin_empty]
  · rw [← comap_coe_nhdsLT_of_Ioo_subset hsb (fun _ => hs a ha) hb, map_comap_of_mem]
    rw [Subtype.range_val]
    exact (mem_nhdsLT_iff_exists_Ioo_subset' ha).2 (hs a ha)

/--
theorem `map_coe_atBot_of_Ioo_subset` / 定理 `map_coe_atBot_of_Ioo_subset`

English:
theorem map_coe_atBot_of_Ioo_subset
  statement: (hsa : s subseteq Ioi a) (hs : forall b' > a, exists b > a, Ioo a b subseteq s)
  proof: by
  refine map_coe_atTop_of_Ioo_subset (s := ofDual ⁻¹' s) (b := toDual a) hsa ?_ ha.dual
  intro b' hb'
  simpa [OrderDual.exists] using hs (ofDual b') hb'

中文:
定理 map_coe_atBot_of_Ioo_subset
  结论: (hsa : s subseteq 左开右无界区间 a) (hs : 对任意 b' > a, 存在 b > a, 开区间 a b subseteq s)
  证明: by
  refine map_coe_atTop_of_Ioo_subset (s := ofDual ⁻¹' s) (b := toDual a) hsa ?_ ha.dual
  intro b' hb'
  simpa [OrderDual.exists] using hs (ofDual b') hb'

Depends on / 依赖: OrderDual, OrderDual.exists, ha.dual, map_coe_atTop_of_Ioo_subset, ofDual, of_dense, toDual
-/
theorem map_coe_atBot_of_Ioo_subset (hsa : s subseteq Ioi a) (hs : forall b' > a, exists b > a, Ioo a b subseteq s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : s -> X) atBot = 𝓝[>] a := by
  refine map_coe_atTop_of_Ioo_subset (s := ofDual ⁻¹' s) (b := toDual a) hsa ?_ ha.dual
  intro b' hb'
  simpa [OrderDual.exists] using hs (ofDual b') hb'

/-- The `atTop` filter for an open interval `Ioo a b` comes from the left-neighbourhoods filter at
the right endpoint in the ambient order. -/
@[simp]
/--
theorem `comap_coe_Ioo_nhdsLT` / 定理 `comap_coe_Ioo_nhdsLT`

English:
theorem comap_coe_Ioo_nhdsLT
  given: (a b : X) (hb : IsSuccPrelimit b := by exact .of_dense _)
  proof: comap_coe_nhdsLT_of_Ioo_subset Ioo_subset_Iio_self
    (fun h => ⟨a, h.elim fun _x hx => hx.1.trans hx.2, Subset.rfl⟩) hb

中文:
定理 comap_coe_Ioo_nhdsLT
  条件: (a b : X) (hb : IsSuccPrelimit b := by exact .of_dense _)
  证明: comap_coe_nhdsLT_of_Ioo_subset Ioo_subset_Iio_self
    (fun h => ⟨a, h.elim fun _x hx => hx.1.trans hx.2, Subset.rfl⟩) hb

Depends on / 依赖: Ioo_subset_Iio_self, Subset, Subset.rfl, comap_coe_nhdsLT_of_Ioo_subset, h.elim, of_dense
-/
theorem comap_coe_Ioo_nhdsLT (a b : X) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : Ioo a b -> X) (𝓝[<] b) = atTop :=
  comap_coe_nhdsLT_of_Ioo_subset Ioo_subset_Iio_self
    (fun h => ⟨a, h.elim fun _x hx => hx.1.trans hx.2, Subset.rfl⟩) hb

/-- The `atBot` filter for an open interval `Ioo a b` comes from the right-neighbourhoods filter at
the left endpoint in the ambient order. -/
@[simp]
/--
theorem `comap_coe_Ioo_nhdsGT` / 定理 `comap_coe_Ioo_nhdsGT`

English:
theorem comap_coe_Ioo_nhdsGT
  given: (a b : X) (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: comap_coe_nhdsGT_of_Ioo_subset Ioo_subset_Ioi_self
    (fun h => ⟨b, h.elim fun _x hx => hx.1.trans hx.2, Subset.rfl⟩) ha

@[simp]

中文:
定理 comap_coe_Ioo_nhdsGT
  条件: (a b : X) (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: comap_coe_nhdsGT_of_Ioo_subset Ioo_subset_Ioi_self
    (fun h => ⟨b, h.elim fun _x hx => hx.1.trans hx.2, Subset.rfl⟩) ha

@[simp]

Depends on / 依赖: Ioo_subset_Ioi_self, Subset, Subset.rfl, comap_coe_nhdsGT_of_Ioo_subset, h.elim, of_dense
-/
theorem comap_coe_Ioo_nhdsGT (a b : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : Ioo a b -> X) (𝓝[>] a) = atBot :=
  comap_coe_nhdsGT_of_Ioo_subset Ioo_subset_Ioi_self
    (fun h => ⟨b, h.elim fun _x hx => hx.1.trans hx.2, Subset.rfl⟩) ha

@[simp]
/--
theorem `comap_coe_Ioi_nhdsGT` / 定理 `comap_coe_Ioi_nhdsGT`

English:
theorem comap_coe_Ioi_nhdsGT
  given: (a : X) (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: comap_coe_nhdsGT_of_Ioo_subset Subset.rfl (fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩) ha

@[simp]

中文:
定理 comap_coe_Ioi_nhdsGT
  条件: (a : X) (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: comap_coe_nhdsGT_of_Ioo_subset Subset.rfl (fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩) ha

@[simp]

Depends on / 依赖: Ioo_subset_Ioi_self, Subset, Subset.rfl, comap_coe_nhdsGT_of_Ioo_subset, of_dense
-/
theorem comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : Ioi a -> X) (𝓝[>] a) = atBot :=
  comap_coe_nhdsGT_of_Ioo_subset Subset.rfl (fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩) ha

@[simp]
/--
theorem `comap_coe_Iio_nhdsLT` / 定理 `comap_coe_Iio_nhdsLT`

English:
theorem comap_coe_Iio_nhdsLT
  given: (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _)
  proof: comap_coe_Ioi_nhdsGT (toDual a) ha.dual

@[simp]

中文:
定理 comap_coe_Iio_nhdsLT
  条件: (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _)
  证明: comap_coe_Ioi_nhdsGT (toDual a) ha.dual

@[simp]

Depends on / 依赖: comap_coe_Ioi_nhdsGT, ha.dual, of_dense, toDual
-/
theorem comap_coe_Iio_nhdsLT (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _) :
    comap ((↑) : Iio a -> X) (𝓝[<] a) = atTop :=
  comap_coe_Ioi_nhdsGT (toDual a) ha.dual

@[simp]
/--
theorem `map_coe_Ioo_atTop` / 定理 `map_coe_Ioo_atTop`

English:
theorem map_coe_Ioo_atTop
  given: (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _)
  proof: map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self (fun _ _ => ⟨_, h, Subset.rfl⟩) hb

@[simp]

中文:
定理 map_coe_Ioo_atTop
  条件: (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _)
  证明: map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self (fun _ _ => ⟨_, h, Subset.rfl⟩) hb

@[simp]

Depends on / 依赖: Ioo_subset_Iio_self, Subset, Subset.rfl, map_coe_atTop_of_Ioo_subset, of_dense
-/
theorem map_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : Ioo a b -> X) atTop = 𝓝[<] b :=
  map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self (fun _ _ => ⟨_, h, Subset.rfl⟩) hb

@[simp]
/--
theorem `map_coe_Ioo_atBot` / 定理 `map_coe_Ioo_atBot`

English:
theorem map_coe_Ioo_atBot
  given: (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self (fun _ _ => ⟨_, h, Subset.rfl⟩) ha

@[simp]

中文:
定理 map_coe_Ioo_atBot
  条件: (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self (fun _ _ => ⟨_, h, Subset.rfl⟩) ha

@[simp]

Depends on / 依赖: Ioo_subset_Ioi_self, Subset, Subset.rfl, map_coe_atBot_of_Ioo_subset, of_dense
-/
theorem map_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : Ioo a b -> X) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self (fun _ _ => ⟨_, h, Subset.rfl⟩) ha

@[simp]
/--
theorem `map_coe_Ioi_atBot` / 定理 `map_coe_Ioi_atBot`

English:
theorem map_coe_Ioi_atBot
  given: (a : X) (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: map_coe_atBot_of_Ioo_subset Subset.rfl (fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩) ha

@[simp]

中文:
定理 map_coe_Ioi_atBot
  条件: (a : X) (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: map_coe_atBot_of_Ioo_subset Subset.rfl (fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩) ha

@[simp]

Depends on / 依赖: Ioo_subset_Ioi_self, Subset, Subset.rfl, map_coe_atBot_of_Ioo_subset, of_dense
-/
theorem map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : Ioi a -> X) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Subset.rfl (fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩) ha

@[simp]
/--
theorem `map_coe_Iio_atTop` / 定理 `map_coe_Iio_atTop`

English:
theorem map_coe_Iio_atTop
  given: (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _)
  proof: map_coe_Ioi_atBot (toDual a) ha.dual

中文:
定理 map_coe_Iio_atTop
  条件: (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _)
  证明: map_coe_Ioi_atBot (toDual a) ha.dual

Depends on / 依赖: ha.dual, map_coe_Ioi_atBot, of_dense, toDual
-/
theorem map_coe_Iio_atTop (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _) :
    map ((↑) : Iio a -> X) atTop = 𝓝[<] a :=
  map_coe_Ioi_atBot (toDual a) ha.dual

variable {α : Type*} {l : Filter α} {f : X -> α}

@[simp]
/--
theorem `tendsto_comp_coe_Ioo_atTop` / 定理 `tendsto_comp_coe_Ioo_atTop`

English:
theorem tendsto_comp_coe_Ioo_atTop
  given: (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _)
  proof: by
  rw [← map_coe_Ioo_atTop h hb]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_comp_coe_Ioo_atTop
  条件: (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _)
  证明: by
  rw [← map_coe_Ioo_atTop h hb]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, _iff, comp_def, map_coe_Ioo_atTop, of_dense, tendsto_map
-/
theorem tendsto_comp_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    Tendsto (fun x : Ioo a b => f x) atTop l ↔ Tendsto f (𝓝[<] b) l := by
  rw [← map_coe_Ioo_atTop h hb]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_comp_coe_Ioo_atBot` / 定理 `tendsto_comp_coe_Ioo_atBot`

English:
theorem tendsto_comp_coe_Ioo_atBot
  given: (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: by
  rw [← map_coe_Ioo_atBot h ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_comp_coe_Ioo_atBot
  条件: (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: by
  rw [← map_coe_Ioo_atBot h ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, _iff, comp_def, map_coe_Ioo_atBot, of_dense, tendsto_map
-/
theorem tendsto_comp_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Ioo a b => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioo_atBot h ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_comp_coe_Ioi_atBot` / 定理 `tendsto_comp_coe_Ioi_atBot`

English:
theorem tendsto_comp_coe_Ioi_atBot
  given: (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: by
  rw [← map_coe_Ioi_atBot a ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_comp_coe_Ioi_atBot
  条件: (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: by
  rw [← map_coe_Ioi_atBot a ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, _iff, comp_def, map_coe_Ioi_atBot, of_dense, tendsto_map
-/
theorem tendsto_comp_coe_Ioi_atBot (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Ioi a => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioi_atBot a ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_comp_coe_Iio_atTop` / 定理 `tendsto_comp_coe_Iio_atTop`

English:
theorem tendsto_comp_coe_Iio_atTop
  given: (ha : IsSuccPrelimit a := by exact .of_dense _)
  proof: by
  rw [← map_coe_Iio_atTop a ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_comp_coe_Iio_atTop
  条件: (ha : IsSuccPrelimit a := by exact .of_dense _)
  证明: by
  rw [← map_coe_Iio_atTop a ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, _iff, comp_def, map_coe_Iio_atTop, of_dense, tendsto_map
-/
theorem tendsto_comp_coe_Iio_atTop (ha : IsSuccPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Iio a => f x) atTop l ↔ Tendsto f (𝓝[<] a) l := by
  rw [← map_coe_Iio_atTop a ha]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_Ioo_atTop` / 定理 `tendsto_Ioo_atTop`

English:
theorem tendsto_Ioo_atTop
  given: {f : α -> Ioo a b} (hb : IsSuccPrelimit b := by exact .of_dense _)
  proof: by
  rw [← comap_coe_Ioo_nhdsLT a b hb]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_Ioo_atTop
  条件: {f : α -> 开区间 a b} (hb : IsSuccPrelimit b := by exact .of_dense _)
  证明: by
  rw [← comap_coe_Ioo_nhdsLT a b hb]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, comap_coe_Ioo_nhdsLT, comp_def, of_dense, tendsto_comap_iff
-/
theorem tendsto_Ioo_atTop {f : α -> Ioo a b} (hb : IsSuccPrelimit b := by exact .of_dense _) :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : X)) l (𝓝[<] b) := by
  rw [← comap_coe_Ioo_nhdsLT a b hb]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_Ioo_atBot` / 定理 `tendsto_Ioo_atBot`

English:
theorem tendsto_Ioo_atBot
  given: {f : α -> Ioo a b} (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: by
  rw [← comap_coe_Ioo_nhdsGT a b ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_Ioo_atBot
  条件: {f : α -> 开区间 a b} (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: by
  rw [← comap_coe_Ioo_nhdsGT a b ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, comap_coe_Ioo_nhdsGT, comp_def, of_dense, tendsto_comap_iff
-/
theorem tendsto_Ioo_atBot {f : α -> Ioo a b} (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : X)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioo_nhdsGT a b ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_Ioi_atBot` / 定理 `tendsto_Ioi_atBot`

English:
theorem tendsto_Ioi_atBot
  given: {f : α -> Ioi a} (ha : IsPredPrelimit a := by exact .of_dense _)
  proof: by
  rw [← comap_coe_Ioi_nhdsGT a ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_Ioi_atBot
  条件: {f : α -> 左开右无界区间 a} (ha : IsPredPrelimit a := by exact .of_dense _)
  证明: by
  rw [← comap_coe_Ioi_nhdsGT a ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Tendsto, comap_coe_Ioi_nhdsGT, comp_def, of_dense, tendsto_comap_iff
-/
theorem tendsto_Ioi_atBot {f : α -> Ioi a} (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : X)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioi_nhdsGT a ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_Iio_atTop` / 定理 `tendsto_Iio_atTop`

English:
theorem tendsto_Iio_atTop
  given: {f : α -> Iio a} (ha : IsSuccPrelimit a := by exact .of_dense _)
  proof: by
  rw [← comap_coe_Iio_nhdsLT a ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

中文:
定理 tendsto_Iio_atTop
  条件: {f : α -> 左无界右开区间 a} (ha : IsSuccPrelimit a := by exact .of_dense _)
  证明: by
  rw [← comap_coe_Iio_nhdsLT a ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Tendsto, comap_coe_Iio_nhdsLT, comp_def, of_dense, tendsto_comap_iff
-/
theorem tendsto_Iio_atTop {f : α -> Iio a} (ha : IsSuccPrelimit a := by exact .of_dense _) :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : X)) l (𝓝[<] a) := by
  rw [← comap_coe_Iio_nhdsLT a ha]; rw [tendsto_comap_iff]; rw [Function.comp_def]

section LocallyFinite
variable [LinearOrder α] [LocallyFiniteOrder α] [NoMaxOrder X] [NoMinOrder X]

/--
theorem `locallyFinite_Icc_of_tendsto` / 定理 `locallyFinite_Icc_of_tendsto`

English:
theorem locallyFinite_Icc_of_tendsto
  statement: {f g : α -> X}
  proof: by
  intro x
  cases isEmpty_or_nonempty α
  · use univ
    simp [Subsingleton.elim _ (∅ : Set α)]
  obtain ⟨x_L, hx_L⟩ := exists_lt x
  obtain ⟨x_R, hx_R⟩ := exists_gt x
  obtain ⟨a_L, ha_L : forall a <= a_L, g a <= x_L⟩ :=
.exists_forall_of_atBot hu.eventually_le_atBot x_L
  obtain ⟨a_R, ha_R : fo

中文:
定理 locallyFinite_Icc_of_tendsto
  结论: {f g : α -> X}
  证明: by
  intro x
  cases isEmpty_or_nonempty α
  · use univ
    simp [Subsingleton.elim _ (∅ : Set α)]
  obtain ⟨x_L, hx_L⟩ := exists_lt x
  obtain ⟨x_R, hx_R⟩ := exists_gt x
  obtain ⟨a_L, ha_L : forall a <= a_L, g a <= x_L⟩ :=
.exists_forall_of_atBot hu.eventually_le_atBot x_L
  obtain ⟨a_R, ha_R : fo

Depends on / 依赖: Ioo_mem_nhds, Subsingleton, Subsingleton.elim, contrapose, eventually_ge_atTop, eventually_le_atBot, exists_forall_of_atBot, exists_forall_of_atTop, exists_gt, exists_lt, finite_Icc, ha_L, ha_R, hl.eventually_ge_atTop, hu.eventually_le_atBot, hx_L, hx_R, isEmpty_or_nonempty, subset
-/
theorem locallyFinite_Icc_of_tendsto {f g : α -> X}
    (hl : Tendsto f atTop atTop) (hu : Tendsto g atBot atBot) :
    LocallyFinite (fun n => Set.Icc (f n) (g n)) := by
  intro x
  cases isEmpty_or_nonempty α
  · use univ
    simp [Subsingleton.elim _ (∅ : Set α)]
  obtain ⟨x_L, hx_L⟩ := exists_lt x
  obtain ⟨x_R, hx_R⟩ := exists_gt x
  obtain ⟨a_L, ha_L : forall a <= a_L, g a <= x_L⟩ :=
.exists_forall_of_atBot hu.eventually_le_atBot x_L
  obtain ⟨a_R, ha_R : forall a >= a_R, x_R <= f a⟩ :=
.exists_forall_of_atTop hl.eventually_ge_atTop x_R
  refine ⟨Ioo x_L x_R, Ioo_mem_nhds hx_L hx_R, (finite_Icc a_L a_R).subset ?_⟩
  rintro n ⟨y, ⟨hf, hg⟩, ⟨hxL, hxR⟩⟩
  constructor
  · contrapose! hxL
    exact hg.trans (ha_L n hxL.le)
  · contrapose! hxR
    exact (ha_R n hxR.le).trans hf

/--
theorem `locallyFinite_Ico_of_tendsto` / 定理 `locallyFinite_Ico_of_tendsto`

English:
theorem locallyFinite_Ico_of_tendsto
  statement: {l u : α -> X}
  proof: .subset fun _ => Set.Ico_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

中文:
定理 locallyFinite_Ico_of_tendsto
  结论: {l u : α -> X}
  证明: .subset fun _ => Set.Ico_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

Depends on / 依赖: Ico_subset_Icc_self, Set.Ico_subset_Icc_self, locallyFinite_Icc_of_tendsto, subset
-/
theorem locallyFinite_Ico_of_tendsto {l u : α -> X}
    (hl : Tendsto l atTop atTop) (hu : Tendsto u atBot atBot) :
    LocallyFinite (fun n => Set.Ico (l n) (u n)) :=
.subset fun _ => Set.Ico_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

/--
theorem `locallyFinite_Ioc_of_tendsto` / 定理 `locallyFinite_Ioc_of_tendsto`

English:
theorem locallyFinite_Ioc_of_tendsto
  statement: {l u : α -> X}
  proof: .subset fun _ => Set.Ioc_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

中文:
定理 locallyFinite_Ioc_of_tendsto
  结论: {l u : α -> X}
  证明: .subset fun _ => Set.Ioc_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

Depends on / 依赖: Ioc_subset_Icc_self, Set.Ioc_subset_Icc_self, locallyFinite_Icc_of_tendsto, subset
-/
theorem locallyFinite_Ioc_of_tendsto {l u : α -> X}
    (hl : Tendsto l atTop atTop) (hu : Tendsto u atBot atBot) :
    LocallyFinite (fun n => Set.Ioc (l n) (u n)) :=
.subset fun _ => Set.Ioc_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

/--
theorem `locallyFinite_Ioo_of_tendsto` / 定理 `locallyFinite_Ioo_of_tendsto`

English:
theorem locallyFinite_Ioo_of_tendsto
  statement: {l u : α -> X}
  proof: .subset fun _ => Set.Ioo_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

中文:
定理 locallyFinite_Ioo_of_tendsto
  结论: {l u : α -> X}
  证明: .subset fun _ => Set.Ioo_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

Depends on / 依赖: Ioo_subset_Icc_self, Set.Ioo_subset_Icc_self, locallyFinite_Icc_of_tendsto, subset
-/
theorem locallyFinite_Ioo_of_tendsto {l u : α -> X}
    (hl : Tendsto l atTop atTop) (hu : Tendsto u atBot atBot) :
    LocallyFinite (fun n => Set.Ioo (l n) (u n)) :=
.subset fun _ => Set.Ioo_subset_Icc_self locallyFinite_Icc_of_tendsto hl hu

end LocallyFinite
