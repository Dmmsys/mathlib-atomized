/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-! # Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

public section

open Function

namespace Set

variable {α : Type*} {s t u : Set α}

/--
Definition of `inclusion` / `inclusion` 的定义

English:
abbreviation inclusion
  signature: (h : s subseteq t)
  body: fun x => ⟨x, h x.prop⟩

中文:
缩写 inclusion
  签名: (h : s subseteq t)
  定义体: fun x => ⟨x, h x.prop⟩

Depends on / 依赖: x.prop
-/
abbrev inclusion (h : s subseteq t) : s -> t := fun x => ⟨x, h x.prop⟩

/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  given: (x : s)
  statement: inclusion Subset.rfl x = x
  proof: rfl

中文:
定理 inclusion_self
  条件: (x : s)
  结论: inclusion 子集.rfl x = x
  证明: rfl
-/
theorem inclusion_self (x : s) : inclusion Subset.rfl x = x :=
  rfl

/--
theorem `inclusion_eq_id` / 定理 `inclusion_eq_id`

English:
theorem inclusion_eq_id
  given: (h : s subseteq s)
  statement: inclusion h = id
  proof: rfl

中文:
定理 inclusion_eq_id
  条件: (h : s subseteq s)
  结论: inclusion h = id
  证明: rfl
-/
theorem inclusion_eq_id (h : s subseteq s) : inclusion h = id :=
  rfl

/--
theorem `inclusion_eq_subtype_map` / 定理 `inclusion_eq_subtype_map`

English:
theorem inclusion_eq_subtype_map
  given: (h : s subseteq t)
  statement: inclusion h = Subtype.map id h
  proof: rfl

@[simp]

中文:
定理 inclusion_eq_subtype_map
  条件: (h : s subseteq t)
  结论: inclusion h = 子类型.map id h
  证明: rfl

@[simp]
-/
theorem inclusion_eq_subtype_map (h : s subseteq t) : inclusion h = Subtype.map id h :=
  rfl

@[simp]
/--
theorem `inclusion_mk` / 定理 `inclusion_mk`

English:
theorem inclusion_mk
  given: {h : s subseteq t} (a : α) (ha : a in s)
  statement: inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩
  proof: rfl

中文:
定理 inclusion_mk
  条件: {h : s subseteq t} (a : α) (ha : a in s)
  结论: inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩
  证明: rfl
-/
theorem inclusion_mk {h : s subseteq t} (a : α) (ha : a in s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl

/--
theorem `inclusion_right` / 定理 `inclusion_right`

English:
theorem inclusion_right
  given: (h : s subseteq t) (x : t) (m : (x : α) in s)
  statement: inclusion h ⟨x, m⟩ = x
  proof: rfl

@[simp]

中文:
定理 inclusion_right
  条件: (h : s subseteq t) (x : t) (m : (x : α) in s)
  结论: inclusion h ⟨x, m⟩ = x
  证明: rfl

@[simp]
-/
theorem inclusion_right (h : s subseteq t) (x : t) (m : (x : α) in s) : inclusion h ⟨x, m⟩ = x :=
  rfl

@[simp]
/--
theorem `inclusion_inclusion` / 定理 `inclusion_inclusion`

English:
theorem inclusion_inclusion
  given: (hst : s subseteq t) (htu : t subseteq u) (x : s)
  proof: rfl

@[simp]

中文:
定理 inclusion_inclusion
  条件: (hst : s subseteq t) (htu : t subseteq u) (x : s)
  证明: rfl

@[simp]
-/
theorem inclusion_inclusion (hst : s subseteq t) (htu : t subseteq u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x :=
  rfl

@[simp]
/--
theorem `inclusion_comp_inclusion` / 定理 `inclusion_comp_inclusion`

English:
theorem inclusion_comp_inclusion
  given: {α} {s t u : Set α} (hst : s subseteq t) (htu : t subseteq u)
  proof: funext (inclusion_inclusion hst htu)

@[simp]

中文:
定理 inclusion_comp_inclusion
  条件: {α} {s t u : 集合 α} (hst : s subseteq t) (htu : t subseteq u)
  证明: funext (inclusion_inclusion hst htu)

@[simp]

Depends on / 依赖: inclusion_inclusion
-/
theorem inclusion_comp_inclusion {α} {s t u : Set α} (hst : s subseteq t) (htu : t subseteq u) :
    inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
  funext (inclusion_inclusion hst htu)

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: (h : s subseteq t) (x : s)
  statement: (inclusion h x : α) = (x : α)
  proof: rfl

中文:
定理 coe_inclusion
  条件: (h : s subseteq t) (x : s)
  结论: (inclusion h x : α) = (x : α)
  证明: rfl
-/
theorem coe_inclusion (h : s subseteq t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl

/--
theorem `val_comp_inclusion` / 定理 `val_comp_inclusion`

English:
theorem val_comp_inclusion
  given: (h : s subseteq t)
  statement: Subtype.val ∘ inclusion h = Subtype.val
  proof: rfl

中文:
定理 val_comp_inclusion
  条件: (h : s subseteq t)
  结论: 子类型.val ∘ inclusion h = 子类型.val
  证明: rfl
-/
theorem val_comp_inclusion (h : s subseteq t) : Subtype.val ∘ inclusion h = Subtype.val :=
  rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: (h : s subseteq t)
  statement: (inclusion h).Injective
  proof: Subtype.map_injective h injective_id

中文:
定理 inclusion_injective
  条件: (h : s subseteq t)
  结论: (inclusion h).单射
  证明: Subtype.map_injective h injective_id

Depends on / 依赖: Subtype, Subtype.map_injective, injective_id, map_injective
-/
theorem inclusion_injective (h : s subseteq t) : (inclusion h).Injective :=
  Subtype.map_injective h injective_id

/--
theorem `inclusion_inj` / 定理 `inclusion_inj`

English:
theorem inclusion_inj
  given: (h : s subseteq t) {x y : s}
  statement: inclusion h x = inclusion h y ↔ x = y
  proof: (inclusion_injective h).eq_iff

中文:
定理 inclusion_inj
  条件: (h : s subseteq t) {x y : s}
  结论: inclusion h x = inclusion h y ↔ x = y
  证明: (inclusion_injective h).eq_iff

Depends on / 依赖: eq_iff, inclusion_injective
-/
theorem inclusion_inj (h : s subseteq t) {x y : s} : inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

/--
theorem `eq_of_inclusion_surjective` / 定理 `eq_of_inclusion_surjective`

English:
theorem eq_of_inclusion_surjective
  statement: {s t : Set α} {h : s subseteq t}
  proof: h.antisymm fun x hx => by grind [h_surj ⟨x, hx⟩]

中文:
定理 eq_of_inclusion_surjective
  结论: {s t : 集合 α} {h : s subseteq t}
  证明: h.antisymm fun x hx => by grind [h_surj ⟨x, hx⟩]

Depends on / 依赖: antisymm, h.antisymm, h_surj
-/
theorem eq_of_inclusion_surjective {s t : Set α} {h : s subseteq t}
    (h_surj : Function.Surjective (inclusion h)) : s = t :=
  h.antisymm fun x hx => by grind [h_surj ⟨x, hx⟩]

/--
theorem `inclusion_le_inclusion` / 定理 `inclusion_le_inclusion`

English:
theorem inclusion_le_inclusion
  given: [LE α] {s t : Set α} (h : s subseteq t) {x y : s}
  proof: .rfl

中文:
定理 inclusion_le_inclusion
  条件: [LE α] {s t : 集合 α} (h : s subseteq t) {x y : s}
  证明: .rfl
-/
theorem inclusion_le_inclusion [LE α] {s t : Set α} (h : s subseteq t) {x y : s} :
    inclusion h x <= inclusion h y ↔ x <= y := .rfl

/--
theorem `inclusion_lt_inclusion` / 定理 `inclusion_lt_inclusion`

English:
theorem inclusion_lt_inclusion
  given: [LT α] {s t : Set α} (h : s subseteq t) {x y : s}
  proof: .rfl

中文:
定理 inclusion_lt_inclusion
  条件: [LT α] {s t : 集合 α} (h : s subseteq t) {x y : s}
  证明: .rfl
-/
theorem inclusion_lt_inclusion [LT α] {s t : Set α} (h : s subseteq t) {x y : s} :
    inclusion h x < inclusion h y ↔ x < y := .rfl

end Set
