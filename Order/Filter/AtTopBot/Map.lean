/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Set.OrderIso

/-!
# Map and comap of `Filter.atTop` and `Filter.atBot`
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace OrderIso

open Filter

variable [Preorder α] [Preorder β]

@[simp]
/--
theorem `comap_atTop` / 定理 `comap_atTop`

English:
theorem comap_atTop
  given: (e : α ≃o β)
  statement: comap e atTop = atTop
  proof: by
  simp [atTop, ← e.surjective.iInf_comp]

@[simp]

中文:
定理 comap_atTop
  条件: (e : α ≃o β)
  结论: comap e atTop = atTop
  证明: by
  simp [atTop, ← e.surjective.iInf_comp]

@[simp]

Depends on / 依赖: e.surjective.iInf_comp, iInf_comp, surjective
-/
theorem comap_atTop (e : α ≃o β) : comap e atTop = atTop := by
  simp [atTop, ← e.surjective.iInf_comp]

@[simp]
/--
theorem `comap_atBot` / 定理 `comap_atBot`

English:
theorem comap_atBot
  given: (e : α ≃o β)
  statement: comap e atBot = atBot
  proof: e.dual.comap_atTop

@[simp]

中文:
定理 comap_atBot
  条件: (e : α ≃o β)
  结论: comap e atBot = atBot
  证明: e.dual.comap_atTop

@[simp]

Depends on / 依赖: comap_atTop, e.dual.comap_atTop
-/
theorem comap_atBot (e : α ≃o β) : comap e atBot = atBot :=
  e.dual.comap_atTop

@[simp]
/--
theorem `map_atTop` / 定理 `map_atTop`

English:
theorem map_atTop
  given: (e : α ≃o β)
  statement: map (e : α -> β) atTop = atTop
  proof: by
  rw [← e.comap_atTop]; rw [map_comap_of_surjective e.surjective]

@[simp]

中文:
定理 map_atTop
  条件: (e : α ≃o β)
  结论: map (e : α -> β) atTop = atTop
  证明: by
  rw [← e.comap_atTop]; rw [map_comap_of_surjective e.surjective]

@[simp]

Depends on / 依赖: comap_atTop, e.comap_atTop, e.surjective, map_comap_of_surjective, surjective
-/
theorem map_atTop (e : α ≃o β) : map (e : α -> β) atTop = atTop := by
  rw [← e.comap_atTop]; rw [map_comap_of_surjective e.surjective]

@[simp]
/--
theorem `map_atBot` / 定理 `map_atBot`

English:
theorem map_atBot
  given: (e : α ≃o β)
  statement: map (e : α -> β) atBot = atBot
  proof: e.dual.map_atTop

中文:
定理 map_atBot
  条件: (e : α ≃o β)
  结论: map (e : α -> β) atBot = atBot
  证明: e.dual.map_atTop

Depends on / 依赖: e.dual.map_atTop, map_atTop
-/
theorem map_atBot (e : α ≃o β) : map (e : α -> β) atBot = atBot :=
  e.dual.map_atTop

/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  given: (e : α ≃o β)
  statement: Tendsto e atTop atTop
  proof: e.map_atTop.le

中文:
定理 tendsto_atTop
  条件: (e : α ≃o β)
  结论: 收敛 e atTop atTop
  证明: e.map_atTop.le

Depends on / 依赖: e.map_atTop.le, map_atTop
-/
theorem tendsto_atTop (e : α ≃o β) : Tendsto e atTop atTop :=
  e.map_atTop.le

/--
theorem `tendsto_atBot` / 定理 `tendsto_atBot`

English:
theorem tendsto_atBot
  given: (e : α ≃o β)
  statement: Tendsto e atBot atBot
  proof: e.map_atBot.le

@[simp]

中文:
定理 tendsto_atBot
  条件: (e : α ≃o β)
  结论: 收敛 e atBot atBot
  证明: e.map_atBot.le

@[simp]

Depends on / 依赖: e.map_atBot.le, map_atBot
-/
theorem tendsto_atBot (e : α ≃o β) : Tendsto e atBot atBot :=
  e.map_atBot.le

@[simp]
/--
theorem `tendsto_atTop_iff` / 定理 `tendsto_atTop_iff`

English:
theorem tendsto_atTop_iff
  given: {l : Filter γ} {f : γ -> α} (e : α ≃o β)
  proof: by
  rw [← e.comap_atTop]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_atTop_iff
  条件: {l : 滤子 γ} {f : γ -> α} (e : α ≃o β)
  证明: by
  rw [← e.comap_atTop]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comap_atTop, comp_def, e.comap_atTop, tendsto_comap_iff
-/
theorem tendsto_atTop_iff {l : Filter γ} {f : γ -> α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atTop ↔ Tendsto f l atTop := by
  rw [← e.comap_atTop]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_atBot_iff` / 定理 `tendsto_atBot_iff`

English:
theorem tendsto_atBot_iff
  given: {l : Filter γ} {f : γ -> α} (e : α ≃o β)
  proof: e.dual.tendsto_atTop_iff

中文:
定理 tendsto_atBot_iff
  条件: {l : 滤子 γ} {f : γ -> α} (e : α ≃o β)
  证明: e.dual.tendsto_atTop_iff

Depends on / 依赖: e.dual.tendsto_atTop_iff, tendsto_atTop_iff
-/
theorem tendsto_atBot_iff {l : Filter γ} {f : γ -> α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atBot ↔ Tendsto f l atBot :=
  e.dual.tendsto_atTop_iff

end OrderIso
