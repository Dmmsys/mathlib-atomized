/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Linear locally finite orders

We prove that a `LinearOrder` which is a `LocallyFiniteOrder` also verifies
* `SuccOrder`
* `PredOrder`
* `IsSuccArchimedean`
* `IsPredArchimedean`
* `Countable`

Furthermore, we show that there is an `OrderIso` between such an order and a subset of `ℤ`.

## Main definitions

* `toZ i0 i`: in a linear order on which we can define predecessors and successors and which is
  succ-archimedean, we can assign a unique integer `toZ i0 i` to each element `i : ι` while
  respecting the order, starting from `toZ i0 i0 = 0`.

## Main results

Results about linear locally finite orders:
* `LinearLocallyFiniteOrder.SuccOrder`: a linear locally finite order has a successor function.
* `LinearLocallyFiniteOrder.PredOrder`: a linear locally finite order has a predecessor
  function.
* `LinearLocallyFiniteOrder.isSuccArchimedean`: a linear locally finite order is
  succ-archimedean.
* `LinearOrder.pred_archimedean_of_succ_archimedean`: a succ-archimedean linear order is also
  pred-archimedean.
* `countable_of_linear_succ_pred_arch` : a succ-archimedean linear order is countable.

About `toZ`:
* `orderIsoRangeToZOfLinearSuccPredArch`: `toZ` defines an `OrderIso` between `ι` and its
  range.
* `orderIsoNatOfLinearSuccPredArch`: if the order has a bot but no top, `toZ` defines an
  `OrderIso` between `ι` and `ℕ`.
* `orderIsoIntOfLinearSuccPredArch`: if the order has neither bot nor top, `toZ` defines an
  `OrderIso` between `ι` and `ℤ`.
* `orderIsoRangeOfLinearSuccPredArch`: if the order has both a bot and a top, `toZ` gives an
  `OrderIso` between `ι` and `Finset.range ((toZ ⊥ ⊤).toNat + 1)`.

-/

public section

open Order

variable {ι : Type*} [LinearOrder ι]

namespace LinearOrder

variable [SuccOrder ι] [PredOrder ι]

instance (priority := 100) isPredArchimedean_of_isSuccArchimedean [IsSuccArchimedean ι] :
    IsPredArchimedean ι where
  exists_pred_iterate_of_le {i j} hij := by
    have h_exists := exists_succ_iterate_of_le hij
    obtain ⟨n, hn_eq, hn_lt_ne⟩ : exists n, succ^[n] i = j ∧ forall m < n, succ^[m] i != j :=
      ⟨Nat.find h_exists, Nat.find_spec h_exists, fun m hmn => Nat.find_min h_exists hmn⟩
    refine ⟨n, ?_⟩
    rw [← hn_eq]
    cases n with
    | zero => simp only [Function.iterate_zero, id]
    | succ n =>
      rw [pred_succ_iterate_of_not_isMax]
      rw [Nat.succ_sub_succ_eq_sub]; rw [tsub_zero]
      suffices succ^[n] i < succ^[n.succ] i from not_isMax_of_lt this
      refine lt_of_le_of_ne ?_ ?_
      · rw [Function.iterate_succ_apply']
        exact le_succ _
      · rw [hn_eq]
        exact hn_lt_ne _ (Nat.lt_succ_self n)

/--
Instance `isSuccArchimedean_of_isPredArchimedean` / 实例 `isSuccArchimedean_of_isPredArchimedean`

English:
instance isSuccArchimedean_of_isPredArchimedean
  signature: [IsPredArchimedean ι]
  body: inferInstanceAs (IsSuccArchimedean ιᵒᵈᵒᵈ)

中文:
实例 isSuccArchimedean_of_isPredArchimedean
  签名: [IsPredArchimedean ι]
  定义体: inferInstanceAs (IsSuccArchimedean ιᵒᵈᵒᵈ)

Depends on / 依赖: IsSuccArchimedean
-/
instance isSuccArchimedean_of_isPredArchimedean [IsPredArchimedean ι] : IsSuccArchimedean ι :=
  inferInstanceAs (IsSuccArchimedean ιᵒᵈᵒᵈ)

/--
theorem `isSuccArchimedean_iff_isPredArchimedean` / 定理 `isSuccArchimedean_iff_isPredArchimedean`

English:
theorem isSuccArchimedean_iff_isPredArchimedean
  statement: IsSuccArchimedean ι ↔ IsPredArchimedean ι where
  proof: isPredArchimedean_of_isSuccArchimedean
  mpr _ := isSuccArchimedean_of_isPredArchimedean

中文:
定理 isSuccArchimedean_iff_isPredArchimedean
  结论: IsSuccArchimedean ι ↔ IsPredArchimedean ι where
  证明: isPredArchimedean_of_isSuccArchimedean
  mpr _ := isSuccArchimedean_of_isPredArchimedean

Depends on / 依赖: isPredArchimedean_of_isSuccArchimedean
-/
theorem isSuccArchimedean_iff_isPredArchimedean : IsSuccArchimedean ι ↔ IsPredArchimedean ι where
  mp _ := isPredArchimedean_of_isSuccArchimedean
  mpr _ := isSuccArchimedean_of_isPredArchimedean

end LinearOrder

namespace LinearLocallyFiniteOrder

/--
Definition of `succFn` / `succFn` 的定义

English:
definition succFn
  signature: (i : ι)
  body: (exists_glb_Ioi i).choose

中文:
定义 succFn
  签名: (i : ι)
  定义体: (exists_glb_Ioi i).choose

Depends on / 依赖: exists_glb_Ioi
-/
noncomputable def succFn (i : ι) : ι :=
  (exists_glb_Ioi i).choose

/--
theorem `succFn_spec` / 定理 `succFn_spec`

English:
theorem succFn_spec
  given: (i : ι)
  statement: IsGLB (Set.Ioi i) (succFn i)
  proof: (exists_glb_Ioi i).choose_spec

中文:
定理 succFn_spec
  条件: (i : ι)
  结论: IsGLB (Set.Ioi i) (succFn i)
  证明: (exists_glb_Ioi i).choose_spec

Depends on / 依赖: choose_spec, exists_glb_Ioi
-/
theorem succFn_spec (i : ι) : IsGLB (Set.Ioi i) (succFn i) :=
  (exists_glb_Ioi i).choose_spec

/--
theorem `le_succFn` / 定理 `le_succFn`

English:
theorem le_succFn
  given: (i : ι)
  statement: i <= succFn i
  proof: by
  rw [le_isGLB_iff (succFn_spec i)]; rw [mem_lowerBounds]
  exact fun x hx => le_of_lt hx

中文:
定理 le_succFn
  条件: (i : ι)
  结论: i <= succFn i
  证明: by
  rw [le_isGLB_iff (succFn_spec i)]; rw [mem_lowerBounds]
  exact fun x hx => le_of_lt hx

Depends on / 依赖: le_isGLB_iff, le_of_lt, mem_lowerBounds, succFn_spec
-/
theorem le_succFn (i : ι) : i <= succFn i := by
  rw [le_isGLB_iff (succFn_spec i)]; rw [mem_lowerBounds]
  exact fun x hx => le_of_lt hx

/--
theorem `isGLB_Ioc_of_isGLB_Ioi` / 定理 `isGLB_Ioc_of_isGLB_Ioi`

English:
theorem isGLB_Ioc_of_isGLB_Ioi
  given: {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k)
  proof: by
  simp_rw [IsGLB, IsGreatest, mem_upperBounds, mem_lowerBounds] at h ⊢
  refine ⟨fun x hx => h.1 x hx.1, fun x hx => h.2 x ?_⟩
  intro y hy
  rcases le_or_gt y j with h_le | h_lt
  · exact hx y ⟨hy, h_le⟩
  · exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le

中文:
定理 isGLB_Ioc_of_isGLB_Ioi
  条件: {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k)
  证明: by
  simp_rw [IsGLB, IsGreatest, mem_upperBounds, mem_lowerBounds] at h ⊢
  refine ⟨fun x hx => h.1 x hx.1, fun x hx => h.2 x ?_⟩
  intro y hy
  rcases le_or_gt y j with h_le | h_lt
  · exact hx y ⟨hy, h_le⟩
  · exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le

Depends on / 依赖: IsGreatest, h_le, h_lt, h_lt.le, hij_lt, le_or_gt, le_rfl, le_trans, mem_lowerBounds, mem_upperBounds, simp_rw
-/
theorem isGLB_Ioc_of_isGLB_Ioi {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k) :
    IsGLB (Set.Ioc i j) k := by
  simp_rw [IsGLB, IsGreatest, mem_upperBounds, mem_lowerBounds] at h ⊢
  refine ⟨fun x hx => h.1 x hx.1, fun x hx => h.2 x ?_⟩
  intro y hy
  rcases le_or_gt y j with h_le | h_lt
  · exact hx y ⟨hy, h_le⟩
  · exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le

/--
theorem `isMax_of_succFn_le` / 定理 `isMax_of_succFn_le`

English:
theorem isMax_of_succFn_le
  given: [LocallyFiniteOrder ι] (i : ι) (hi : succFn i <= i)
  statement: IsMax i
  proof: by
  refine fun j _ => not_lt.mp fun hij_lt => ?_
  have h_succFn_eq : succFn i = i := le_antisymm hi (le_succFn i)
  have h_glb : IsGLB (Finset.Ioc i j : Set ι) i := by
    rw [Finset.coe_Ioc]
    have h := succFn_spec i
    rw [h_succFn_eq] at h
    exact isGLB_Ioc_of_isGLB_Ioi hij_lt h
  have hi_

中文:
定理 isMax_of_succFn_le
  条件: [LocallyFiniteOrder ι] (i : ι) (hi : succFn i <= i)
  结论: IsMax i
  证明: by
  refine fun j _ => not_lt.mp fun hij_lt => ?_
  have h_succFn_eq : succFn i = i := le_antisymm hi (le_succFn i)
  have h_glb : IsGLB (Finset.Ioc i j : Set ι) i := by
    rw [Finset.coe_Ioc]
    have h := succFn_spec i
    rw [h_succFn_eq] at h
    exact isGLB_Ioc_of_isGLB_Ioi hij_lt h
  have hi_

Depends on / 依赖: Finset, Finset.Ioc, Finset.coe_Ioc, Finset.isGLB_mem, Finset.mem_Ioc, Finset.mem_Ioc.mpr, coe_Ioc, h_glb, h_succFn_eq, hi_mem, hij_lt, isGLB_Ioc_of_isGLB_Ioi, isGLB_mem, le_antisymm, le_rfl, le_succFn, lt_irrefl, mem_Ioc, not_lt, not_lt.mp
-/
theorem isMax_of_succFn_le [LocallyFiniteOrder ι] (i : ι) (hi : succFn i <= i) : IsMax i := by
  refine fun j _ => not_lt.mp fun hij_lt => ?_
  have h_succFn_eq : succFn i = i := le_antisymm hi (le_succFn i)
  have h_glb : IsGLB (Finset.Ioc i j : Set ι) i := by
    rw [Finset.coe_Ioc]
    have h := succFn_spec i
    rw [h_succFn_eq] at h
    exact isGLB_Ioc_of_isGLB_Ioi hij_lt h
  have hi_mem : i in Finset.Ioc i j := by
    refine Finset.isGLB_mem _ h_glb ?_
    exact ⟨_, Finset.mem_Ioc.mpr ⟨hij_lt, le_rfl⟩⟩
  rw [Finset.mem_Ioc] at hi_mem
  exact lt_irrefl i hi_mem.1

/--
theorem `succFn_le_of_lt` / 定理 `succFn_le_of_lt`

English:
theorem succFn_le_of_lt
  given: (i j : ι) (hij : i < j)
  statement: succFn i <= j
  proof: by
  have h := succFn_spec i
  rw [IsGLB]; rw [IsGreatest]; rw [mem_lowerBounds] at h
  exact h.1 j hij

中文:
定理 succFn_le_of_lt
  条件: (i j : ι) (hij : i < j)
  结论: succFn i <= j
  证明: by
  have h := succFn_spec i
  rw [IsGLB]; rw [IsGreatest]; rw [mem_lowerBounds] at h
  exact h.1 j hij

Depends on / 依赖: IsGreatest, mem_lowerBounds, succFn_spec
-/
theorem succFn_le_of_lt (i j : ι) (hij : i < j) : succFn i <= j := by
  have h := succFn_spec i
  rw [IsGLB]; rw [IsGreatest]; rw [mem_lowerBounds] at h
  exact h.1 j hij

/--
theorem `le_of_lt_succFn` / 定理 `le_of_lt_succFn`

English:
theorem le_of_lt_succFn
  given: (j i : ι) (hij : j < succFn i)
  statement: j <= i
  proof: by
  rw [lt_isGLB_iff (succFn_spec i)] at hij
  obtain ⟨k, hk_lb, hk⟩ := hij
  rw [mem_lowerBounds] at hk_lb
  exact not_lt.mp fun hi_lt_j => not_le.mpr hk (hk_lb j hi_lt_j)

中文:
定理 le_of_lt_succFn
  条件: (j i : ι) (hij : j < succFn i)
  结论: j <= i
  证明: by
  rw [lt_isGLB_iff (succFn_spec i)] at hij
  obtain ⟨k, hk_lb, hk⟩ := hij
  rw [mem_lowerBounds] at hk_lb
  exact not_lt.mp fun hi_lt_j => not_le.mpr hk (hk_lb j hi_lt_j)

Depends on / 依赖: hi_lt_j, hk_lb, lt_isGLB_iff, mem_lowerBounds, not_le, not_le.mpr, not_lt, not_lt.mp, succFn_spec
-/
theorem le_of_lt_succFn (j i : ι) (hij : j < succFn i) : j <= i := by
  rw [lt_isGLB_iff (succFn_spec i)] at hij
  obtain ⟨k, hk_lb, hk⟩ := hij
  rw [mem_lowerBounds] at hk_lb
  exact not_lt.mp fun hi_lt_j => not_le.mpr hk (hk_lb j hi_lt_j)

variable (ι) in
/-- A locally finite order is a `SuccOrder`.
This is not an instance, because its `succ` field conflicts with computable `SuccOrder` structures
on `ℕ` and `ℤ`. -/
@[instance_reducible]
/--
Definition of `succOrder` / `succOrder` 的定义

English:
definition succOrder
  signature: [LocallyFiniteOrder ι]
  body: succFn
  le_succ := le_succFn
  max_of_succ_le h := isMax_of_succFn_le _ h
  succ_le_of_lt h := succFn_le_of_lt _ _ h

中文:
定义 succOrder
  签名: [LocallyFiniteOrder ι]
  定义体: succFn
  le_succ := le_succFn
  max_of_succ_le h := isMax_of_succFn_le _ h
  succ_le_of_lt h := succFn_le_of_lt _ _ h

Depends on / 依赖: succFn
-/
noncomputable def succOrder [LocallyFiniteOrder ι] : SuccOrder ι where
  succ := succFn
  le_succ := le_succFn
  max_of_succ_le h := isMax_of_succFn_le _ h
  succ_le_of_lt h := succFn_le_of_lt _ _ h

variable (ι) in
/-- A locally finite order is a `PredOrder`.
This is not an instance, because its `succ` field conflicts with computable `PredOrder` structures
on `ℕ` and `ℤ`. -/
@[instance_reducible]
/--
Definition of `predOrder` / `predOrder` 的定义

English:
definition predOrder
  signature: [LocallyFiniteOrder ι]
  body: letI := succOrder (ι := ιᵒᵈ)
  inferInstanceAs (PredOrder ιᵒᵈᵒᵈ)

中文:
定义 predOrder
  签名: [LocallyFiniteOrder ι]
  定义体: letI := succOrder (ι := ιᵒᵈ)
  inferInstanceAs (PredOrder ιᵒᵈᵒᵈ)

Depends on / 依赖: PredOrder, succOrder
-/
noncomputable def predOrder [LocallyFiniteOrder ι] : PredOrder ι :=
  letI := succOrder (ι := ιᵒᵈ)
  inferInstanceAs (PredOrder ιᵒᵈᵒᵈ)

instance (priority := 100) [LocallyFiniteOrder ι] [SuccOrder ι] : IsSuccArchimedean ι where
  exists_succ_iterate_of_le := by
    intro i j hij
    rw [le_iff_lt_or_eq] at hij
    rcases hij with hij | hij
    swap
    · refine ⟨0, ?_⟩
      simpa only [Function.iterate_zero, id] using hij
    by_contra! h
    have h_lt : forall n, succ^[n] i < j := fun n => by
      induction n with
      | zero => simpa only [Function.iterate_zero, id] using hij
      | succ n hn =>
        refine lt_of_le_of_ne ?_ (h _)
        rw [Function.iterate_succ']; rw [Function.comp_apply]
        exact succ_le_of_lt hn
    have h_mem : forall n, succ^[n] i in Finset.Icc i j :=
      fun n => Finset.mem_Icc.mpr ⟨le_succ_iterate n i, (h_lt n).le⟩
    obtain ⟨n, m, hnm, h_eq⟩ : exists n m, n < m ∧ succ^[n] i = succ^[m] i := by
      let f : Nat -> Finset.Icc i j := fun n => ⟨succ^[n] i, h_mem n⟩
      obtain ⟨n, m, hnm_ne, hfnm⟩ : exists n m, n != m ∧ f n = f m :=
        Finite.exists_ne_map_eq_of_infinite f
      have hnm_eq : succ^[n] i = succ^[m] i := by simpa only [f, Subtype.mk_eq_mk] using hfnm
      rcases le_total n m with h_le | h_le
      · exact ⟨n, m, lt_of_le_of_ne h_le hnm_ne, hnm_eq⟩
      · exact ⟨m, n, lt_of_le_of_ne h_le hnm_ne.symm, hnm_eq.symm⟩
    have h_max : IsMax (succ^[n] i) := isMax_iterate_succ_of_eq_of_ne h_eq hnm.ne
    exact not_le.mpr (h_lt n) (h_max (h_lt n).le)

instance (priority := 100) [LocallyFiniteOrder ι] [PredOrder ι] : IsPredArchimedean ι :=
  inferInstanceAs (IsPredArchimedean ιᵒᵈᵒᵈ)

end LinearLocallyFiniteOrder

section toZ

-- Requiring either of `IsSuccArchimedean` or `IsPredArchimedean` is equivalent.
variable [SuccOrder ι] [IsSuccArchimedean ι] [PredOrder ι] {i0 i : ι}

-- For "to_Z"

/--
Definition of `toZ` / `toZ` 的定义

English:
definition toZ
  signature: (i0 i : ι)
  body: dite (i0 <= i) (fun hi => Nat.find (exists_succ_iterate_of_le hi)) fun hi =>
    -Nat.find (exists_pred_iterate_of_le (α := ι) (not_le.mp hi).le)

中文:
定义 toZ
  签名: (i0 i : ι)
  定义体: dite (i0 <= i) (fun hi => Nat.find (exists_succ_iterate_of_le hi)) fun hi =>
    -Nat.find (exists_pred_iterate_of_le (α := ι) (not_le.mp hi).le)

Depends on / 依赖: Nat.find, exists_pred_iterate_of_le, exists_succ_iterate_of_le, not_le, not_le.mp
-/
def toZ (i0 i : ι) : Int :=
  dite (i0 <= i) (fun hi => Nat.find (exists_succ_iterate_of_le hi)) fun hi =>
    -Nat.find (exists_pred_iterate_of_le (α := ι) (not_le.mp hi).le)

/--
theorem `toZ_of_ge` / 定理 `toZ_of_ge`

English:
theorem toZ_of_ge
  given: (hi : i0 <= i)
  statement: toZ i0 i = Nat.find (exists_succ_iterate_of_le hi)
  proof: dif_pos hi

中文:
定理 toZ_of_ge
  条件: (hi : i0 <= i)
  结论: toZ i0 i = 自然数.find (存在_succ_iterate_of_le hi)
  证明: dif_pos hi

Depends on / 依赖: dif_pos
-/
theorem toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_iterate_of_le hi) :=
  dif_pos hi

/--
theorem `toZ_of_lt` / 定理 `toZ_of_lt`

English:
theorem toZ_of_lt
  given: (hi : i < i0)
  proof: dif_neg (not_le.mpr hi)

@[simp]

中文:
定理 toZ_of_lt
  条件: (hi : i < i0)
  证明: dif_neg (not_le.mpr hi)

@[simp]

Depends on / 依赖: Decidable, hi.le, leadingCoeff, m.leadingCoeff
-/
theorem toZ_of_lt (hi : i < i0) :
    toZ i0 i = -Nat.find (exists_pred_iterate_of_le (α := ι) hi.le) :=
  dif_neg (not_le.mpr hi)

@[simp]
/--
theorem `toZ_of_eq` / 定理 `toZ_of_eq`

English:
theorem toZ_of_eq
  statement: toZ i0 i0 = 0
  proof: by
  rw [toZ_of_ge le_rfl]
  norm_cast
  rw [← nonpos_iff_eq_zero]
  apply Nat.find_le
  rw [Function.iterate_zero]; rw [id]

中文:
定理 toZ_of_eq
  结论: toZ i0 i0 = 0
  证明: by
  rw [toZ_of_ge le_rfl]
  norm_cast
  rw [← nonpos_iff_eq_zero]
  apply Nat.find_le
  rw [Function.iterate_zero]; rw [id]

Depends on / 依赖: Function, Function.iterate_zero, Nat.find_le, find_le, iterate_zero, le_rfl, nonpos_iff_eq_zero, toZ_of_ge
-/
theorem toZ_of_eq : toZ i0 i0 = 0 := by
  rw [toZ_of_ge le_rfl]
  norm_cast
  rw [← nonpos_iff_eq_zero]
  apply Nat.find_le
  rw [Function.iterate_zero]; rw [id]

/--
theorem `iterate_succ_toZ` / 定理 `iterate_succ_toZ`

English:
theorem iterate_succ_toZ
  given: (i : ι) (hi : i0 <= i)
  statement: succ^[(toZ i0 i).toNat] i0 = i
  proof: by
  rw [toZ_of_ge hi]; rw [Int.toNat_natCast]
  exact Nat.find_spec (exists_succ_iterate_of_le hi)

中文:
定理 iterate_succ_toZ
  条件: (i : ι) (hi : i0 <= i)
  结论: succ^[(toZ i0 i).to自然数] i0 = i
  证明: by
  rw [toZ_of_ge hi]; rw [Int.toNat_natCast]
  exact Nat.find_spec (exists_succ_iterate_of_le hi)

Depends on / 依赖: Int.toNat_natCast, Nat.find_spec, exists_succ_iterate_of_le, find_spec, toNat_natCast, toZ_of_ge
-/
theorem iterate_succ_toZ (i : ι) (hi : i0 <= i) : succ^[(toZ i0 i).toNat] i0 = i := by
  rw [toZ_of_ge hi]; rw [Int.toNat_natCast]
  exact Nat.find_spec (exists_succ_iterate_of_le hi)

/--
theorem `iterate_pred_toZ` / 定理 `iterate_pred_toZ`

English:
theorem iterate_pred_toZ
  given: (i : ι) (hi : i < i0)
  statement: pred^[(-toZ i0 i).toNat] i0 = i
  proof: by
  rw [toZ_of_lt hi]; rw [neg_neg]; rw [Int.toNat_natCast]
  exact Nat.find_spec (exists_pred_iterate_of_le hi.le)

中文:
定理 iterate_pred_toZ
  条件: (i : ι) (hi : i < i0)
  结论: pred^[(-toZ i0 i).to自然数] i0 = i
  证明: by
  rw [toZ_of_lt hi]; rw [neg_neg]; rw [Int.toNat_natCast]
  exact Nat.find_spec (exists_pred_iterate_of_le hi.le)

Depends on / 依赖: Int.toNat_natCast, Nat.find_spec, exists_pred_iterate_of_le, find_spec, hi.le, neg_neg, toNat_natCast, toZ_of_lt
-/
theorem iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i0 i).toNat] i0 = i := by
  rw [toZ_of_lt hi]; rw [neg_neg]; rw [Int.toNat_natCast]
  exact Nat.find_spec (exists_pred_iterate_of_le hi.le)

/--
lemma `toZ_nonneg` / 引理 `toZ_nonneg`

English:
lemma toZ_nonneg
  given: (hi : i0 <= i)
  statement: 0 <= toZ i0 i
  proof: by rw [toZ_of_ge hi]; exact Int.natCast_nonneg _

中文:
引理 toZ_nonneg
  条件: (hi : i0 <= i)
  结论: 0 <= toZ i0 i
  证明: by rw [toZ_of_ge hi]; exact Int.natCast_nonneg _

Depends on / 依赖: Int.natCast_nonneg, natCast_nonneg, toZ_of_ge
-/
lemma toZ_nonneg (hi : i0 <= i) : 0 <= toZ i0 i := by rw [toZ_of_ge hi]; exact Int.natCast_nonneg _

/--
theorem `toZ_neg` / 定理 `toZ_neg`

English:
theorem toZ_neg
  given: (hi : i < i0)
  statement: toZ i0 i < 0
  proof: by
  refine lt_of_le_of_ne ?_ ?_
  · rw [toZ_of_lt hi]
    lia
  · by_contra h
    have h_eq := iterate_pred_toZ i hi
    rw [← h_eq]; rw [h] at hi
    simp only [neg_zero, Int.toNat_zero, Function.iterate_zero, id, lt_self_iff_false] at hi

中文:
定理 toZ_neg
  条件: (hi : i < i0)
  结论: toZ i0 i < 0
  证明: by
  refine lt_of_le_of_ne ?_ ?_
  · rw [toZ_of_lt hi]
    lia
  · by_contra h
    have h_eq := iterate_pred_toZ i hi
    rw [← h_eq]; rw [h] at hi
    simp only [neg_zero, Int.toNat_zero, Function.iterate_zero, id, lt_self_iff_false] at hi

Depends on / 依赖: Function, Function.iterate_zero, Int.toNat_zero, h_eq, iterate_pred_toZ, iterate_zero, lt_of_le_of_ne, lt_self_iff_false, neg_zero, toNat_zero, toZ_of_lt
-/
theorem toZ_neg (hi : i < i0) : toZ i0 i < 0 := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [toZ_of_lt hi]
    lia
  · by_contra h
    have h_eq := iterate_pred_toZ i hi
    rw [← h_eq]; rw [h] at hi
    simp only [neg_zero, Int.toNat_zero, Function.iterate_zero, id, lt_self_iff_false] at hi

/--
theorem `toZ_iterate_succ_le` / 定理 `toZ_iterate_succ_le`

English:
theorem toZ_iterate_succ_le
  given: (n : Nat)
  statement: toZ i0 (succ^[n] i0) <= n
  proof: by
  rw [toZ_of_ge (le_succ_iterate _ _)]
  norm_cast
  exact Nat.find_min' _ rfl

中文:
定理 toZ_iterate_succ_le
  条件: (n : 自然数)
  结论: toZ i0 (succ^[n] i0) <= n
  证明: by
  rw [toZ_of_ge (le_succ_iterate _ _)]
  norm_cast
  exact Nat.find_min' _ rfl

Depends on / 依赖: Nat.find_min, find_min, le_succ_iterate, toZ_of_ge
-/
theorem toZ_iterate_succ_le (n : Nat) : toZ i0 (succ^[n] i0) <= n := by
  rw [toZ_of_ge (le_succ_iterate _ _)]
  norm_cast
  exact Nat.find_min' _ rfl

/--
theorem `toZ_iterate_pred_ge` / 定理 `toZ_iterate_pred_ge`

English:
theorem toZ_iterate_pred_ge
  given: (n : Nat)
  statement: -(n : Int) <= toZ i0 (pred^[n] i0)
  proof: by
  rcases le_or_gt i0 (pred^[n] i0) with h | h
  · have h_eq : pred^[n] i0 = i0 := le_antisymm (pred_iterate_le _ _) h
    rw [h_eq]; rw [toZ_of_eq]
    lia
  · rw [toZ_of_lt h]
    refine Int.neg_le_neg ?_
    norm_cast
    exact Nat.find_min' _ rfl

中文:
定理 toZ_iterate_pred_ge
  条件: (n : 自然数)
  结论: -(n : 整数) <= toZ i0 (pred^[n] i0)
  证明: by
  rcases le_or_gt i0 (pred^[n] i0) with h | h
  · have h_eq : pred^[n] i0 = i0 := le_antisymm (pred_iterate_le _ _) h
    rw [h_eq]; rw [toZ_of_eq]
    lia
  · rw [toZ_of_lt h]
    refine Int.neg_le_neg ?_
    norm_cast
    exact Nat.find_min' _ rfl

Depends on / 依赖: Int.neg_le_neg, Nat.find_min, find_min, h_eq, le_antisymm, le_or_gt, leadingCoeff_zero, neg_le_neg, pred_iterate_le, toZ_of_eq, toZ_of_lt
-/
theorem toZ_iterate_pred_ge (n : Nat) : -(n : Int) <= toZ i0 (pred^[n] i0) := by
  rcases le_or_gt i0 (pred^[n] i0) with h | h
  · have h_eq : pred^[n] i0 = i0 := le_antisymm (pred_iterate_le _ _) h
    rw [h_eq]; rw [toZ_of_eq]
    lia
  · rw [toZ_of_lt h]
    refine Int.neg_le_neg ?_
    norm_cast
    exact Nat.find_min' _ rfl

/--
theorem `toZ_iterate_succ_of_not_isMax` / 定理 `toZ_iterate_succ_of_not_isMax`

English:
theorem toZ_iterate_succ_of_not_isMax
  given: (n : Nat) (hn : ¬IsMax (succ^[n] i0))
  proof: by
  let m := (toZ i0 (succ^[n] i0)).toNat
  have h_eq : succ^[m] i0 = succ^[n] i0 := iterate_succ_toZ _ (le_succ_iterate _ _)
  by_cases hmn : m = n
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max]; rw [toZ_of_ge (le_succ_iterate _ _)]; rw [max_eq_left]
    exact Int.natCast_nonneg _
  suffices IsMax

中文:
定理 toZ_iterate_succ_of_not_isMax
  条件: (n : 自然数) (hn : ¬IsMax (succ^[n] i0))
  证明: by
  let m := (toZ i0 (succ^[n] i0)).toNat
  have h_eq : succ^[m] i0 = succ^[n] i0 := iterate_succ_toZ _ (le_succ_iterate _ _)
  by_cases hmn : m = n
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max]; rw [toZ_of_ge (le_succ_iterate _ _)]; rw [max_eq_left]
    exact Int.natCast_nonneg _
  suffices IsMax

Depends on / 依赖: Int.natCast_nonneg, Int.toNat_eq_max, Ne.symm, absurd, h_eq, h_eq.symm, isMax_iterate_succ_of_eq_of_ne, iterate_succ_toZ, le_succ_iterate, max_eq_left, natCast_nonneg, nth_rw, toNat_eq_max, toZ_of_ge
-/
theorem toZ_iterate_succ_of_not_isMax (n : Nat) (hn : ¬IsMax (succ^[n] i0)) :
    toZ i0 (succ^[n] i0) = n := by
  let m := (toZ i0 (succ^[n] i0)).toNat
  have h_eq : succ^[m] i0 = succ^[n] i0 := iterate_succ_toZ _ (le_succ_iterate _ _)
  by_cases hmn : m = n
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max]; rw [toZ_of_ge (le_succ_iterate _ _)]; rw [max_eq_left]
    exact Int.natCast_nonneg _
  suffices IsMax (succ^[n] i0) from absurd this hn
  exact isMax_iterate_succ_of_eq_of_ne h_eq.symm (Ne.symm hmn)

/--
theorem `toZ_iterate_pred_of_not_isMin` / 定理 `toZ_iterate_pred_of_not_isMin`

English:
theorem toZ_iterate_pred_of_not_isMin
  given: (n : Nat) (hn : ¬IsMin (pred^[n] i0))
  proof: by
  rcases n with - | n
  · simp
  have : pred^[n.succ] i0 < i0 := by
    refine lt_of_le_of_ne (pred_iterate_le _ _) fun h_pred_iterate_eq => hn ?_
    have h_pred_eq_pred : pred^[n.succ] i0 = pred^[0] i0 := by
      rwa [Function.iterate_zero, id]
    exact isMin_iterate_pred_of_eq_of_ne h_pred_e

中文:
定理 toZ_iterate_pred_of_not_isMin
  条件: (n : 自然数) (hn : ¬IsMin (pred^[n] i0))
  证明: by
  rcases n with - | n
  · simp
  have : pred^[n.succ] i0 < i0 := by
    refine lt_of_le_of_ne (pred_iterate_le _ _) fun h_pred_iterate_eq => hn ?_
    have h_pred_eq_pred : pred^[n.succ] i0 = pred^[0] i0 := by
      rwa [Function.iterate_zero, id]
    exact isMin_iterate_pred_of_eq_of_ne h_pred_e

Depends on / 依赖: Function, Function.iterate_zero, Int.toNat_eq_max, Nat.succ_ne_zero, h_eq, h_pred_eq_pred, h_pred_iterate_eq, isMin_iterate_pred_of_eq_of_ne, iterate_pred_toZ, iterate_zero, lt_of_le_of_ne, n.succ, nth_rw, pred_iterate_le, succ_ne_zero, toNat_eq_max, toZ_of_lt
-/
theorem toZ_iterate_pred_of_not_isMin (n : Nat) (hn : ¬IsMin (pred^[n] i0)) :
    toZ i0 (pred^[n] i0) = -n := by
  rcases n with - | n
  · simp
  have : pred^[n.succ] i0 < i0 := by
    refine lt_of_le_of_ne (pred_iterate_le _ _) fun h_pred_iterate_eq => hn ?_
    have h_pred_eq_pred : pred^[n.succ] i0 = pred^[0] i0 := by
      rwa [Function.iterate_zero, id]
    exact isMin_iterate_pred_of_eq_of_ne h_pred_eq_pred (Nat.succ_ne_zero n)
  let m := (-toZ i0 (pred^[n.succ] i0)).toNat
  have h_eq : pred^[m] i0 = pred^[n.succ] i0 := iterate_pred_toZ _ this
  by_cases hmn : m = n + 1
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max]; rw [toZ_of_lt this]; rw [max_eq_left]; rw [neg_neg]
    rw [neg_neg]
    exact Int.natCast_nonneg _
  · suffices IsMin (pred^[n.succ] i0) from absurd this hn
    exact isMin_iterate_pred_of_eq_of_ne h_eq.symm (Ne.symm hmn)

/--
theorem `toZ_strictMono` / 定理 `toZ_strictMono`

English:
theorem toZ_strictMono
  statement: StrictMono (toZ i0)
  proof: by
  intro j i h_le
  contrapose! h_le
  rcases le_or_gt i0 i with hi | hi <;> rcases le_or_gt i0 j with hj | hj
  · rw [← iterate_succ_toZ i hi, ← iterate_succ_toZ j hj]
    exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ _) (Int.toNat_le_toNat h_le)
  · exact absurd ((toZ_neg hj).tran

中文:
定理 toZ_strictMono
  结论: StrictMono (toZ i0)
  证明: by
  intro j i h_le
  contrapose! h_le
  rcases le_or_gt i0 i with hi | hi <;> rcases le_or_gt i0 j with hj | hj
  · rw [← iterate_succ_toZ i hi, ← iterate_succ_toZ j hj]
    exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ _) (Int.toNat_le_toNat h_le)
  · exact absurd ((toZ_neg hj).tran

Depends on / 依赖: Int.toNat_le_toNat, Monotone, Monotone.antitone_iterate_of_map_le, Monotone.monotone_iterate_of_le_map, absurd, antitone_iterate_of_map_le, contrapose, h_le, hi.le.trans, iterate_pred_toZ, iterate_succ_toZ, le_or_gt, le_succ, monotone_iterate_of_le_map, not_lt, not_lt.mpr, pred_le, pred_mono, succ_mono, toNat_le_toNat
-/
theorem toZ_strictMono : StrictMono (toZ i0) := by
  intro j i h_le
  contrapose! h_le
  rcases le_or_gt i0 i with hi | hi <;> rcases le_or_gt i0 j with hj | hj
  · rw [← iterate_succ_toZ i hi, ← iterate_succ_toZ j hj]
    exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ _) (Int.toNat_le_toNat h_le)
  · exact absurd ((toZ_neg hj).trans_le (toZ_nonneg hi)) (not_lt.mpr h_le)
  · exact hi.le.trans hj
  · rw [← iterate_pred_toZ i hi, ← iterate_pred_toZ j hj]
    refine Monotone.antitone_iterate_of_map_le pred_mono (pred_le _) (Int.toNat_le_toNat ?_)
    exact Int.neg_le_neg h_le

/--
theorem `injective_toZ` / 定理 `injective_toZ`

English:
theorem injective_toZ
  statement: Function.Injective (toZ i0)
  proof: toZ_strictMono.injective

@[simp]

中文:
定理 injective_toZ
  结论: Function.Injective (toZ i0)
  证明: toZ_strictMono.injective

@[simp]

Depends on / 依赖: injective, toZ_strictMono, toZ_strictMono.injective
-/
theorem injective_toZ : Function.Injective (toZ i0) :=
  toZ_strictMono.injective

@[simp]
/--
theorem `toZ_le_toZ` / 定理 `toZ_le_toZ`

English:
theorem toZ_le_toZ
  given: {i j : ι}
  statement: toZ i0 i <= toZ i0 j ↔ i <= j
  proof: toZ_strictMono.le_iff_le

@[deprecated (since := "2026-05-07")]
alias toZ_le_iff := toZ_le_toZ

@[deprecated toZ_le_toZ (since := "2026-05-06")]
alias ⟨le_of_toZ_le, toZ_mono⟩ := toZ_le_toZ

@[simp]

中文:
定理 toZ_le_toZ
  条件: {i j : ι}
  结论: toZ i0 i <= toZ i0 j ↔ i <= j
  证明: toZ_strictMono.le_iff_le

@[deprecated (since := "2026-05-07")]
alias toZ_le_iff := toZ_le_toZ

@[deprecated toZ_le_toZ (since := "2026-05-06")]
alias ⟨le_of_toZ_le, toZ_mono⟩ := toZ_le_toZ

@[simp]

Depends on / 依赖: le_iff_le, toZ_strictMono, toZ_strictMono.le_iff_le
-/
theorem toZ_le_toZ {i j : ι} : toZ i0 i <= toZ i0 j ↔ i <= j :=
  toZ_strictMono.le_iff_le

@[deprecated (since := "2026-05-07")]
alias toZ_le_iff := toZ_le_toZ

@[deprecated toZ_le_toZ (since := "2026-05-06")]
alias ⟨le_of_toZ_le, toZ_mono⟩ := toZ_le_toZ

@[simp]
/--
theorem `toZ_lt_toZ` / 定理 `toZ_lt_toZ`

English:
theorem toZ_lt_toZ
  given: {i j : ι}
  statement: toZ i0 i < toZ i0 j ↔ i < j
  proof: toZ_strictMono.lt_iff_lt

@[deprecated (since := "2026-05-07")]
alias toZ_lt_iff := toZ_lt_toZ

@[simp]

中文:
定理 toZ_lt_toZ
  条件: {i j : ι}
  结论: toZ i0 i < toZ i0 j ↔ i < j
  证明: toZ_strictMono.lt_iff_lt

@[deprecated (since := "2026-05-07")]
alias toZ_lt_iff := toZ_lt_toZ

@[simp]

Depends on / 依赖: lt_iff_lt, toZ_strictMono, toZ_strictMono.lt_iff_lt
-/
theorem toZ_lt_toZ {i j : ι} : toZ i0 i < toZ i0 j ↔ i < j :=
  toZ_strictMono.lt_iff_lt

@[deprecated (since := "2026-05-07")]
alias toZ_lt_iff := toZ_lt_toZ

@[simp]
/--
theorem `toZ_inj` / 定理 `toZ_inj`

English:
theorem toZ_inj
  given: {i j : ι}
  statement: toZ i0 i = toZ i0 j ↔ i = j
  proof: injective_toZ.eq_iff

中文:
定理 toZ_inj
  条件: {i j : ι}
  结论: toZ i0 i = toZ i0 j ↔ i = j
  证明: injective_toZ.eq_iff

Depends on / 依赖: eq_iff, injective_toZ, injective_toZ.eq_iff
-/
theorem toZ_inj {i j : ι} : toZ i0 i = toZ i0 j ↔ i = j :=
  injective_toZ.eq_iff

/--
theorem `toZ_iterate_succ` / 定理 `toZ_iterate_succ`

English:
theorem toZ_iterate_succ
  given: [NoMaxOrder ι] (n : Nat)
  statement: toZ i0 (succ^[n] i0) = n
  proof: toZ_iterate_succ_of_not_isMax n (not_isMax _)

中文:
定理 toZ_iterate_succ
  条件: [NoMaxOrder ι] (n : 自然数)
  结论: toZ i0 (succ^[n] i0) = n
  证明: toZ_iterate_succ_of_not_isMax n (not_isMax _)

Depends on / 依赖: not_isMax, toZ_iterate_succ_of_not_isMax
-/
theorem toZ_iterate_succ [NoMaxOrder ι] (n : Nat) : toZ i0 (succ^[n] i0) = n :=
  toZ_iterate_succ_of_not_isMax n (not_isMax _)

/--
theorem `toZ_iterate_pred` / 定理 `toZ_iterate_pred`

English:
theorem toZ_iterate_pred
  given: [NoMinOrder ι] (n : Nat)
  statement: toZ i0 (pred^[n] i0) = -n
  proof: toZ_iterate_pred_of_not_isMin n (not_isMin _)

中文:
定理 toZ_iterate_pred
  条件: [NoMinOrder ι] (n : 自然数)
  结论: toZ i0 (pred^[n] i0) = -n
  证明: toZ_iterate_pred_of_not_isMin n (not_isMin _)

Depends on / 依赖: not_isMin, toZ_iterate_pred_of_not_isMin
-/
theorem toZ_iterate_pred [NoMinOrder ι] (n : Nat) : toZ i0 (pred^[n] i0) = -n :=
  toZ_iterate_pred_of_not_isMin n (not_isMin _)

end toZ

section OrderIso

variable [SuccOrder ι] [PredOrder ι] [IsSuccArchimedean ι]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `orderIsoRangeToZOfLinearSuccPredArch` / `orderIsoRangeToZOfLinearSuccPredArch` 的定义

English:
definition orderIsoRangeToZOfLinearSuccPredArch
  signature: [hι : Nonempty ι]
  body: Equiv.ofInjective _ injective_toZ
  map_rel_iff' := by simp

中文:
定义 orderIsoRangeToZOfLinearSuccPredArch
  签名: [hι : Nonempty ι]
  定义体: Equiv.ofInjective _ injective_toZ
  map_rel_iff' := by simp

Depends on / 依赖: Equiv.ofInjective, injective_toZ, ofInjective
-/
noncomputable def orderIsoRangeToZOfLinearSuccPredArch [hι : Nonempty ι] :
    ι ≃o Set.range (toZ hι.some) where
  toEquiv := Equiv.ofInjective _ injective_toZ
  map_rel_iff' := by simp

instance (priority := 100) countable_of_linear_succ_pred_arch : Countable ι := by
  rcases isEmpty_or_nonempty ι with _ | hι
  · infer_instance
  · exact Countable.of_equiv _ orderIsoRangeToZOfLinearSuccPredArch.symm.toEquiv

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `orderIsoIntOfLinearSuccPredArch` / `orderIsoIntOfLinearSuccPredArch` 的定义

English:
definition orderIsoIntOfLinearSuccPredArch
  signature: [NoMaxOrder ι] [NoMinOrder ι] [hι : Nonempty ι]
  body: toZ hι.some
  invFun n := if 0 <= n then succ^[n.toNat] hι.some else pred^[(-n).toNat] hι.some
  left_inv i := by
    rcases le_or_gt hι.some i with hi | hi
    · have h_nonneg : 0 <= toZ hι.some i := toZ_nonneg hi
      simp_rw [if_pos h_nonneg]
      exact iterate_succ_toZ i hi
    · have h_neg : 

中文:
定义 orderIsoIntOfLinearSuccPredArch
  签名: [NoMaxOrder ι] [NoMinOrder ι] [hι : Nonempty ι]
  定义体: toZ hι.some
  invFun n := if 0 <= n then succ^[n.toNat] hι.some else pred^[(-n).toNat] hι.some
  left_inv i := by
    rcases le_or_gt hι.some i with hi | hi
    · have h_nonneg : 0 <= toZ hι.some i := toZ_nonneg hi
      simp_rw [if_pos h_nonneg]
      exact iterate_succ_toZ i hi
    · have h_neg : 
-/
noncomputable def orderIsoIntOfLinearSuccPredArch [NoMaxOrder ι] [NoMinOrder ι] [hι : Nonempty ι] :
    ι ≃o Int where
  toFun := toZ hι.some
  invFun n := if 0 <= n then succ^[n.toNat] hι.some else pred^[(-n).toNat] hι.some
  left_inv i := by
    rcases le_or_gt hι.some i with hi | hi
    · have h_nonneg : 0 <= toZ hι.some i := toZ_nonneg hi
      simp_rw [if_pos h_nonneg]
      exact iterate_succ_toZ i hi
    · have h_neg : toZ hι.some i < 0 := toZ_neg hi
      simp_rw [if_neg (not_le.mpr h_neg)]
      exact iterate_pred_toZ i hi
  right_inv n := by
    rcases le_or_gt 0 n with hn | hn
    · simp_rw [if_pos hn]
      rw [toZ_iterate_succ]
      exact Int.toNat_of_nonneg hn
    · simp_rw [if_neg (not_le.mpr hn)]
      rw [toZ_iterate_pred]
      simp only [hn.le, Int.toNat_of_nonneg, Int.neg_nonneg_of_nonpos, Int.neg_neg]
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `orderIsoNatOfLinearSuccPredArch` / `orderIsoNatOfLinearSuccPredArch` 的定义

English:
definition orderIsoNatOfLinearSuccPredArch
  signature: [NoMaxOrder ι] [OrderBot ι]
  body: (toZ ⊥ i).toNat
  invFun n := succ^[n] ⊥
  left_inv i := by
    dsimp only
    exact iterate_succ_toZ i bot_le
  right_inv n := by
    dsimp only
    rw [toZ_iterate_succ]
    exact Int.toNat_natCast n
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Int.toNat_le]
    rw [← toZ_le_

中文:
定义 orderIsoNatOfLinearSuccPredArch
  签名: [NoMaxOrder ι] [OrderBot ι]
  定义体: (toZ ⊥ i).toNat
  invFun n := succ^[n] ⊥
  left_inv i := by
    dsimp only
    exact iterate_succ_toZ i bot_le
  right_inv n := by
    dsimp only
    rw [toZ_iterate_succ]
    exact Int.toNat_natCast n
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Int.toNat_le]
    rw [← toZ_le_
-/
def orderIsoNatOfLinearSuccPredArch [NoMaxOrder ι] [OrderBot ι] : ι ≃o Nat where
  toFun i := (toZ ⊥ i).toNat
  invFun n := succ^[n] ⊥
  left_inv i := by
    dsimp only
    exact iterate_succ_toZ i bot_le
  right_inv n := by
    dsimp only
    rw [toZ_iterate_succ]
    exact Int.toNat_natCast n
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Int.toNat_le]
    rw [← toZ_le_toZ (i0 := (⊥ : ι))]; rw [Int.toNat_of_nonneg (toZ_nonneg bot_le)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `orderIsoRangeOfLinearSuccPredArch` / `orderIsoRangeOfLinearSuccPredArch` 的定义

English:
definition orderIsoRangeOfLinearSuccPredArch
  signature: [OrderBot ι] [OrderTop ι]
  body: ⟨(toZ ⊥ i).toNat,
      Finset.mem_range_succ_iff.mpr (Int.toNat_le_toNat (toZ_le_toZ.mpr le_top))⟩
  invFun n := succ^[n] ⊥
  left_inv i := iterate_succ_toZ i bot_le
  right_inv n := by
    ext1
    simp only
    refine le_antisymm ?_ ?_
    · rw [Int.toNat_le]
      exact toZ_iterate_succ_le _
   

中文:
定义 orderIsoRangeOfLinearSuccPredArch
  签名: [OrderBot ι] [OrderTop ι]
  定义体: ⟨(toZ ⊥ i).toNat,
      Finset.mem_range_succ_iff.mpr (Int.toNat_le_toNat (toZ_le_toZ.mpr le_top))⟩
  invFun n := succ^[n] ⊥
  left_inv i := iterate_succ_toZ i bot_le
  right_inv n := by
    ext1
    simp only
    refine le_antisymm ?_ ?_
    · rw [Int.toNat_le]
      exact toZ_iterate_succ_le _
   

Depends on / 依赖: Finset, Finset.mem_range.mp, Finset.mem_range_succ_iff.mpr, Int.toNat_le, Int.toNat_le_toNat, Int.toNat_natCast, Nat.lt_succ_iff.mp, bot_le, hn_max, invFun, isTop_iff_eq_top, isTop_iff_isMax, iterate_succ_toZ, le_antisymm, le_top, left_inv, lt_succ_iff, mem_range, mem_range_succ_iff, n.prop
-/
def orderIsoRangeOfLinearSuccPredArch [OrderBot ι] [OrderTop ι] :
    ι ≃o Finset.range ((toZ ⊥ (⊤ : ι)).toNat + 1) where
  toFun i :=
    ⟨(toZ ⊥ i).toNat,
      Finset.mem_range_succ_iff.mpr (Int.toNat_le_toNat (toZ_le_toZ.mpr le_top))⟩
  invFun n := succ^[n] ⊥
  left_inv i := iterate_succ_toZ i bot_le
  right_inv n := by
    ext1
    simp only
    refine le_antisymm ?_ ?_
    · rw [Int.toNat_le]
      exact toZ_iterate_succ_le _
    by_cases hn_max : IsMax (succ^[↑n] (⊥ : ι))
    · rw [← isTop_iff_isMax, isTop_iff_eq_top] at hn_max
      rw [hn_max]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp n.prop)
    · rw [toZ_iterate_succ_of_not_isMax _ hn_max]
      simp only [Int.toNat_natCast, le_refl]
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Int.toNat_le]
    rw [← toZ_le_toZ (i0 := (⊥ : ι))]; rw [Int.toNat_of_nonneg (toZ_nonneg bot_le)]

end OrderIso

instance (priority := 100) Countable.of_linearOrder_locallyFiniteOrder [LocallyFiniteOrder ι] :
    Countable ι :=
  have := LinearLocallyFiniteOrder.succOrder ι
  have := LinearLocallyFiniteOrder.predOrder ι
  countable_of_linear_succ_pred_arch
