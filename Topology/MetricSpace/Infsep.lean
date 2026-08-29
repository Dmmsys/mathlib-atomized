/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Topology.MetricSpace.Basic

/-!
# Infimum separation

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `Set` namespace to give access to dot notation.

## Main definitions
* `Set.einfsep`: Extended infimum separation of a set.
* `Set.infsep`: Infimum separation of a set (when in a pseudometric space).

-/

@[expose] public section


variable {α β : Type*}

namespace Set

section Einfsep

open ENNReal

open Function

/--
Definition of `einfsep` / `einfsep` 的定义

English:
definition einfsep
  signature: [EDist α] (s : Set α)
  body: ⨅ (x in s) (y in s) (_ : x != y), edist x y

中文:
定义 einfsep
  签名: [EDist α] (s : Set α)
  定义体: ⨅ (x in s) (y in s) (_ : x != y), edist x y
-/
noncomputable def einfsep [EDist α] (s : Set α) : Real>=0∞ :=
  ⨅ (x in s) (y in s) (_ : x != y), edist x y

section EDist

variable [EDist α] {x y : α} {s t : Set α}

/--
theorem `le_einfsep_iff` / 定理 `le_einfsep_iff`

English:
theorem le_einfsep_iff
  given: {d}
  proof: by
  simp_rw [einfsep, le_iInf_iff]

中文:
定理 le_einfsep_iff
  条件: {d}
  证明: by
  simp_rw [einfsep, le_iInf_iff]

Depends on / 依赖: einfsep, le_iInf_iff, simp_rw
-/
theorem le_einfsep_iff {d} :
    d <= s.einfsep ↔ forall x in s, forall y in s, x != y -> d <= edist x y := by
  simp_rw [einfsep, le_iInf_iff]

/--
theorem `einfsep_zero` / 定理 `einfsep_zero`

English:
theorem einfsep_zero
  statement: s.einfsep = 0 ↔ forall C > 0, exists x in s, exists y in s, x != y ∧ edist x y < C
  proof: by
  simp_rw [einfsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]

中文:
定理 einfsep_zero
  结论: s.einfsep = 0 ↔ 对任意 C > 0, 存在 x in s, 存在 y in s, x != y ∧ edist x y < C
  证明: by
  simp_rw [einfsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]

Depends on / 依赖: _root_, _root_.bot_eq_zero, bot_eq_zero, einfsep, exists_prop, iInf_eq_bot, iInf_lt_iff, simp_rw
-/
theorem einfsep_zero : s.einfsep = 0 ↔ forall C > 0, exists x in s, exists y in s, x != y ∧ edist x y < C := by
  simp_rw [einfsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]

/--
theorem `einfsep_pos` / 定理 `einfsep_pos`

English:
theorem einfsep_pos
  statement: 0 < s.einfsep ↔ exists C > 0, forall x in s, forall y in s, x != y -> C <= edist x y
  proof: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [einfsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]

中文:
定理 einfsep_pos
  结论: 0 < s.einfsep ↔ 存在 C > 0, 对任意 x in s, 对任意 y in s, x != y -> C <= edist x y
  证明: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [einfsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]

Depends on / 依赖: einfsep_zero, exists_prop, not_and, not_exists, not_forall, not_lt, pos_iff_ne_zero
-/
theorem einfsep_pos : 0 < s.einfsep ↔ exists C > 0, forall x in s, forall y in s, x != y -> C <= edist x y := by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [einfsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]

/--
theorem `einfsep_top` / 定理 `einfsep_top`

English:
theorem einfsep_top
  proof: by
  simp_rw [einfsep, iInf_eq_top]

中文:
定理 einfsep_top
  证明: by
  simp_rw [einfsep, iInf_eq_top]

Depends on / 依赖: einfsep, iInf_eq_top, simp_rw
-/
theorem einfsep_top :
    s.einfsep = ∞ ↔ forall x in s, forall y in s, x != y -> edist x y = ∞ := by
  simp_rw [einfsep, iInf_eq_top]

/--
theorem `einfsep_lt_top` / 定理 `einfsep_lt_top`

English:
theorem einfsep_lt_top
  proof: by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

中文:
定理 einfsep_lt_top
  证明: by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

Depends on / 依赖: einfsep, exists_prop, iInf_lt_iff, simp_rw
-/
theorem einfsep_lt_top :
    s.einfsep < ∞ ↔ exists x in s, exists y in s, x != y ∧ edist x y < ∞ := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

/--
theorem `einfsep_ne_top` / 定理 `einfsep_ne_top`

English:
theorem einfsep_ne_top
  proof: by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]

中文:
定理 einfsep_ne_top
  证明: by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]

Depends on / 依赖: einfsep_lt_top, lt_top_iff_ne_top, simp_rw
-/
theorem einfsep_ne_top :
    s.einfsep != ∞ ↔ exists x in s, exists y in s, x != y ∧ edist x y != ∞ := by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]

/--
theorem `einfsep_lt_iff` / 定理 `einfsep_lt_iff`

English:
theorem einfsep_lt_iff
  given: {d}
  proof: by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

中文:
定理 einfsep_lt_iff
  条件: {d}
  证明: by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

Depends on / 依赖: einfsep, exists_prop, iInf_lt_iff, simp_rw
-/
theorem einfsep_lt_iff {d} :
    s.einfsep < d ↔ exists x in s, exists y in s, x != y ∧ edist x y < d := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

/--
theorem `nontrivial_of_einfsep_lt_top` / 定理 `nontrivial_of_einfsep_lt_top`

English:
theorem nontrivial_of_einfsep_lt_top
  given: (hs : s.einfsep < ∞)
  statement: s.Nontrivial
  proof: by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

中文:
定理 nontrivial_of_einfsep_lt_top
  条件: (hs : s.einfsep < ∞)
  结论: s.Nontrivial
  证明: by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

Depends on / 依赖: einfsep_lt_top
-/
theorem nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial := by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

/--
theorem `nontrivial_of_einfsep_ne_top` / 定理 `nontrivial_of_einfsep_ne_top`

English:
theorem nontrivial_of_einfsep_ne_top
  given: (hs : s.einfsep != ∞)
  statement: s.Nontrivial
  proof: nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)

中文:
定理 nontrivial_of_einfsep_ne_top
  条件: (hs : s.einfsep != ∞)
  结论: s.Nontrivial
  证明: nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)

Depends on / 依赖: lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, nontrivial_of_einfsep_lt_top
-/
theorem nontrivial_of_einfsep_ne_top (hs : s.einfsep != ∞) : s.Nontrivial :=
  nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)

/--
theorem `Subsingleton.einfsep` / 定理 `Subsingleton.einfsep`

English:
theorem Subsingleton.einfsep
  given: (hs : s.Subsingleton)
  statement: s.einfsep = ∞
  proof: by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim

中文:
定理 Subsingleton.einfsep
  条件: (hs : s.Subsingleton)
  结论: s.einfsep = ∞
  证明: by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim

Depends on / 依赖: einfsep_top
-/
theorem Subsingleton.einfsep (hs : s.Subsingleton) : s.einfsep = ∞ := by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim

/--
theorem `le_einfsep_image_iff` / 定理 `le_einfsep_image_iff`

English:
theorem le_einfsep_image_iff
  given: {d} {f : β -> α} {s : Set β}
  statement: d <= einfsep (f '' s)
  proof: by
  simp_rw [le_einfsep_iff, forall_mem_image]

中文:
定理 le_einfsep_image_iff
  条件: {d} {f : β -> α} {s : Set β}
  结论: d <= einfsep (f '' s)
  证明: by
  simp_rw [le_einfsep_iff, forall_mem_image]

Depends on / 依赖: forall_mem_image, le_einfsep_iff, simp_rw
-/
theorem le_einfsep_image_iff {d} {f : β -> α} {s : Set β} : d <= einfsep (f '' s)
    ↔ forall x in s, forall y in s, f x != f y -> d <= edist (f x) (f y) := by
  simp_rw [le_einfsep_iff, forall_mem_image]

/--
theorem `le_edist_of_le_einfsep` / 定理 `le_edist_of_le_einfsep`

English:
theorem le_edist_of_le_einfsep
  statement: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  proof: le_einfsep_iff.1 hd x hx y hy hxy

中文:
定理 le_edist_of_le_einfsep
  结论: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  证明: le_einfsep_iff.1 hd x hx y hy hxy

Depends on / 依赖: le_einfsep_iff
-/
theorem le_edist_of_le_einfsep {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
    (hd : d <= s.einfsep) : d <= edist x y :=
  le_einfsep_iff.1 hd x hx y hy hxy

/--
theorem `einfsep_le_edist_of_mem` / 定理 `einfsep_le_edist_of_mem`

English:
theorem einfsep_le_edist_of_mem
  given: {x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  proof: le_edist_of_le_einfsep hx hy hxy le_rfl

中文:
定理 einfsep_le_edist_of_mem
  条件: {x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  证明: le_edist_of_le_einfsep hx hy hxy le_rfl

Depends on / 依赖: le_edist_of_le_einfsep, le_rfl
-/
theorem einfsep_le_edist_of_mem {x} (hx : x in s) {y} (hy : y in s) (hxy : x != y) :
    s.einfsep <= edist x y :=
  le_edist_of_le_einfsep hx hy hxy le_rfl

/--
theorem `einfsep_le_of_mem_of_edist_le` / 定理 `einfsep_le_of_mem_of_edist_le`

English:
theorem einfsep_le_of_mem_of_edist_le
  statement: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  proof: le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'

中文:
定理 einfsep_le_of_mem_of_edist_le
  结论: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  证明: le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'

Depends on / 依赖: einfsep_le_edist_of_mem, le_trans
-/
theorem einfsep_le_of_mem_of_edist_le {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
    (hxy' : edist x y <= d) : s.einfsep <= d :=
  le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'

/--
theorem `le_einfsep` / 定理 `le_einfsep`

English:
theorem le_einfsep
  given: {d} (h : forall x in s, forall y in s, x != y -> d <= edist x y)
  statement: d <= s.einfsep
  proof: le_einfsep_iff.2 h

@[simp]

中文:
定理 le_einfsep
  条件: {d} (h : 对任意 x in s, 对任意 y in s, x != y -> d <= edist x y)
  结论: d <= s.einfsep
  证明: le_einfsep_iff.2 h

@[simp]

Depends on / 依赖: le_einfsep_iff
-/
theorem le_einfsep {d} (h : forall x in s, forall y in s, x != y -> d <= edist x y) : d <= s.einfsep :=
  le_einfsep_iff.2 h

@[simp]
/--
theorem `einfsep_empty` / 定理 `einfsep_empty`

English:
theorem einfsep_empty
  statement: (∅ : Set α).einfsep = ∞
  proof: subsingleton_empty.einfsep

@[simp]

中文:
定理 einfsep_empty
  结论: (∅ : Set α).einfsep = ∞
  证明: subsingleton_empty.einfsep

@[simp]

Depends on / 依赖: einfsep, subsingleton_empty, subsingleton_empty.einfsep
-/
theorem einfsep_empty : (∅ : Set α).einfsep = ∞ :=
  subsingleton_empty.einfsep

@[simp]
/--
theorem `einfsep_singleton` / 定理 `einfsep_singleton`

English:
theorem einfsep_singleton
  statement: ({x} : Set α).einfsep = ∞
  proof: subsingleton_singleton.einfsep

中文:
定理 einfsep_singleton
  结论: ({x} : Set α).einfsep = ∞
  证明: subsingleton_singleton.einfsep

Depends on / 依赖: einfsep, subsingleton_singleton, subsingleton_singleton.einfsep
-/
theorem einfsep_singleton : ({x} : Set α).einfsep = ∞ :=
  subsingleton_singleton.einfsep

/--
theorem `einfsep_iUnion_mem_option` / 定理 `einfsep_iUnion_mem_option`

English:
theorem einfsep_iUnion_mem_option
  given: {ι : Type*} (o : Option ι) (s : ι -> Set α)
  proof: by cases o <;> simp

中文:
定理 einfsep_iUnion_mem_option
  条件: {ι : 类型} (o : Option ι) (s : ι -> Set α)
  证明: by cases o <;> simp
-/
theorem einfsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι -> Set α) :
    (⋃ i in o, s i).einfsep = ⨅ i in o, (s i).einfsep := by cases o <;> simp

/--
theorem `einfsep_anti` / 定理 `einfsep_anti`

English:
theorem einfsep_anti
  given: (hst : s subseteq t)
  statement: t.einfsep <= s.einfsep
  proof: le_einfsep fun _x hx _y hy => einfsep_le_edist_of_mem (hst hx) (hst hy)

中文:
定理 einfsep_anti
  条件: (hst : s subseteq t)
  结论: t.einfsep <= s.einfsep
  证明: le_einfsep fun _x hx _y hy => einfsep_le_edist_of_mem (hst hx) (hst hy)

Depends on / 依赖: einfsep_le_edist_of_mem, le_einfsep
-/
theorem einfsep_anti (hst : s subseteq t) : t.einfsep <= s.einfsep :=
  le_einfsep fun _x hx _y hy => einfsep_le_edist_of_mem (hst hx) (hst hy)

/--
theorem `einfsep_insert_le` / 定理 `einfsep_insert_le`

English:
theorem einfsep_insert_le
  statement: (insert x s).einfsep <= ⨅ (y in s) (_ : x != y), edist x y
  proof: by
  simp_rw [le_iInf_iff]
  exact fun _ hy hxy => einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy

中文:
定理 einfsep_insert_le
  结论: (insert x s).einfsep <= ⨅ (y in s) (_ : x != y), edist x y
  证明: by
  simp_rw [le_iInf_iff]
  exact fun _ hy hxy => einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy

Depends on / 依赖: einfsep_le_edist_of_mem, le_iInf_iff, mem_insert, mem_insert_of_mem, simp_rw
-/
theorem einfsep_insert_le : (insert x s).einfsep <= ⨅ (y in s) (_ : x != y), edist x y := by
  simp_rw [le_iInf_iff]
  exact fun _ hy hxy => einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy

/--
theorem `le_einfsep_pair` / 定理 `le_einfsep_pair`

English:
theorem le_einfsep_pair
  statement: edist x y ⊓ edist y x <= ({x, y} : Set α).einfsep
  proof: by
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction

中文:
定理 le_einfsep_pair
  结论: edist x y ⊓ edist y x <= ({x, y} : Set α).einfsep
  证明: by
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction

Depends on / 依赖: inf_le_iff, le_einfsep_iff, le_refl, mem_insert_iff, mem_singleton_iff, or_true, simp_rw, true_or
-/
theorem le_einfsep_pair : edist x y ⊓ edist y x <= ({x, y} : Set α).einfsep := by
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction

/--
theorem `einfsep_pair_le_left` / 定理 `einfsep_pair_le_left`

English:
theorem einfsep_pair_le_left
  given: (hxy : x != y)
  statement: ({x, y} : Set α).einfsep <= edist x y
  proof: einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

中文:
定理 einfsep_pair_le_left
  条件: (hxy : x != y)
  结论: ({x, y} : Set α).einfsep <= edist x y
  证明: einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

Depends on / 依赖: einfsep_le_edist_of_mem, mem_insert, mem_insert_of_mem, mem_singleton
-/
theorem einfsep_pair_le_left (hxy : x != y) : ({x, y} : Set α).einfsep <= edist x y :=
  einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

/--
theorem `einfsep_pair_le_right` / 定理 `einfsep_pair_le_right`

English:
theorem einfsep_pair_le_right
  given: (hxy : x != y)
  statement: ({x, y} : Set α).einfsep <= edist y x
  proof: by
  rw [pair_comm]; exact einfsep_pair_le_left hxy.symm

中文:
定理 einfsep_pair_le_right
  条件: (hxy : x != y)
  结论: ({x, y} : Set α).einfsep <= edist y x
  证明: by
  rw [pair_comm]; exact einfsep_pair_le_left hxy.symm

Depends on / 依赖: einfsep_pair_le_left, hxy.symm, pair_comm
-/
theorem einfsep_pair_le_right (hxy : x != y) : ({x, y} : Set α).einfsep <= edist y x := by
  rw [pair_comm]; exact einfsep_pair_le_left hxy.symm

/--
theorem `einfsep_pair_eq_inf` / 定理 `einfsep_pair_eq_inf`

English:
theorem einfsep_pair_eq_inf
  given: (hxy : x != y)
  statement: ({x, y} : Set α).einfsep = edist x y ⊓ edist y x
  proof: le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair

中文:
定理 einfsep_pair_eq_inf
  条件: (hxy : x != y)
  结论: ({x, y} : Set α).einfsep = edist x y ⊓ edist y x
  证明: le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair

Depends on / 依赖: einfsep_pair_le_left, einfsep_pair_le_right, le_antisymm, le_einfsep_pair, le_inf
-/
theorem einfsep_pair_eq_inf (hxy : x != y) : ({x, y} : Set α).einfsep = edist x y ⊓ edist y x :=
  le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair

/--
theorem `einfsep_eq_iInf` / 定理 `einfsep_eq_iInf`

English:
theorem einfsep_eq_iInf
  statement: s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α)
  proof: by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

中文:
定理 einfsep_eq_iInf
  结论: s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α)
  证明: by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

Depends on / 依赖: Prod.forall, SetCoe, SetCoe.forall, and_imp, eq_of_forall_le_iff, imp_forall_iff, le_einfsep_iff, le_iInf_iff, mem_offDiag, simp_rw, uncurry_apply_pair
-/
theorem einfsep_eq_iInf : s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

/--
theorem `einfsep_of_fintype` / 定理 `einfsep_of_fintype`

English:
theorem einfsep_of_fintype
  given: [Fintype s]
  statement: s.einfsep = s.offDiag.toFinset.inf (uncurry edist)
  proof: by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

中文:
定理 einfsep_of_fintype
  条件: [Fintype s]
  结论: s.einfsep = s.offDiag.toFinset.inf (uncurry edist)
  证明: by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

Depends on / 依赖: Finset, Finset.le_inf_iff, Prod.forall, and_imp, eq_of_forall_le_iff, imp_forall_iff, le_einfsep_iff, le_inf_iff, mem_offDiag, mem_toFinset, simp_rw, uncurry_apply_pair
-/
theorem einfsep_of_fintype [Fintype s] : s.einfsep = s.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

/--
theorem `Finite.einfsep` / 定理 `Finite.einfsep`

English:
theorem Finite.einfsep
  given: (hs : s.Finite)
  statement: s.einfsep = hs.offDiag.toFinset.inf (uncurry edist)
  proof: by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, Finite.mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

中文:
定理 Finite.einfsep
  条件: (hs : s.Finite)
  结论: s.einfsep = hs.offDiag.toFinset.inf (uncurry edist)
  证明: by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, Finite.mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.le_inf_iff, Prod.forall, and_imp, eq_of_forall_le_iff, imp_forall_iff, le_einfsep_iff, le_inf_iff, mem_offDiag, mem_toFinset, simp_rw, uncurry_apply_pair
-/
theorem Finite.einfsep (hs : s.Finite) : s.einfsep = hs.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, Finite.mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

/--
theorem `Finset.coe_einfsep` / 定理 `Finset.coe_einfsep`

English:
theorem Finset.coe_einfsep
  given: {s : Finset α}
  proof: by
  simp_rw [einfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]

中文:
定理 Finset.coe_einfsep
  条件: {s : Finset α}
  证明: by
  simp_rw [einfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]

Depends on / 依赖: Finset, Finset.coe_offDiag, Finset.toFinset_coe, coe_offDiag, einfsep_of_fintype, simp_rw, toFinset_coe
-/
theorem Finset.coe_einfsep {s : Finset α} :
    (s : Set α).einfsep = s.offDiag.inf (uncurry edist) := by
  simp_rw [einfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]

/--
theorem `Nontrivial.einfsep_exists_of_finite` / 定理 `Nontrivial.einfsep_exists_of_finite`

English:
theorem Nontrivial.einfsep_exists_of_finite
  given: [Finite s] (hs : s.Nontrivial)
  proof: by
  cases nonempty_fintype s
  simp_rw [einfsep_of_fintype]
  rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry edist) with ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

中文:
定理 Nontrivial.einfsep_exists_of_finite
  条件: [Finite s] (hs : s.Nontrivial)
  证明: by
  cases nonempty_fintype s
  simp_rw [einfsep_of_fintype]
  rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry edist) with ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

Depends on / 依赖: Finset, Finset.exists_mem_eq_inf, einfsep_of_fintype, exists_mem_eq_inf, mem_toFinset, nonempty_fintype, offDiag, s.offDiag.toFinset, simp_rw, toFinset, uncurry, w.fst, w.snd
-/
theorem Nontrivial.einfsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    exists x in s, exists y in s, x != y ∧ s.einfsep = edist x y := by
  cases nonempty_fintype s
  simp_rw [einfsep_of_fintype]
  rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry edist) with ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

/--
theorem `Finite.einfsep_exists_of_nontrivial` / 定理 `Finite.einfsep_exists_of_nontrivial`

English:
theorem Finite.einfsep_exists_of_nontrivial
  given: (hsf : s.Finite) (hs : s.Nontrivial)
  proof: letI := hsf.fintype
  hs.einfsep_exists_of_finite

中文:
定理 Finite.einfsep_exists_of_nontrivial
  条件: (hsf : s.Finite) (hs : s.Nontrivial)
  证明: letI := hsf.fintype
  hs.einfsep_exists_of_finite

Depends on / 依赖: einfsep_exists_of_finite, fintype, hs.einfsep_exists_of_finite, hsf.fintype
-/
theorem Finite.einfsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    exists x in s, exists y in s, x != y ∧ s.einfsep = edist x y :=
  letI := hsf.fintype
  hs.einfsep_exists_of_finite

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y z : α} {s : Set α}

/--
theorem `einfsep_pair` / 定理 `einfsep_pair`

English:
theorem einfsep_pair
  given: (hxy : x != y)
  statement: ({x, y} : Set α).einfsep = edist x y
  proof: by
  nth_rw 1 [← min_self (edist x y)]
  convert! einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]

中文:
定理 einfsep_pair
  条件: (hxy : x != y)
  结论: ({x, y} : Set α).einfsep = edist x y
  证明: by
  nth_rw 1 [← min_self (edist x y)]
  convert! einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]

Depends on / 依赖: convert, edist_comm, einfsep_pair_eq_inf, min_self, nth_rw
-/
theorem einfsep_pair (hxy : x != y) : ({x, y} : Set α).einfsep = edist x y := by
  nth_rw 1 [← min_self (edist x y)]
  convert! einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]

/--
theorem `einfsep_insert` / 定理 `einfsep_insert`

English:
theorem einfsep_insert
  statement: einfsep (insert x s) =
  proof: by
  refine le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) ?_
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.

中文:
定理 einfsep_insert
  结论: einfsep (insert x s) =
  证明: by
  refine le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) ?_
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.

Depends on / 依赖: False.elim, Or.inl, Or.inr, edist_comm, einfsep_anti, einfsep_insert_le, einfsep_le_edist_of_mem, hyz.symm, iInf_le_of_le, inf_le_iff, le_antisymm, le_einfsep_iff, le_min, mem_insert_iff, simp_rw, subset_insert
-/
theorem einfsep_insert : einfsep (insert x s) =
    (⨅ (y in s) (_ : x != y), edist x y) ⊓ s.einfsep := by
  refine le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) ?_
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.inl (iInf_le_of_le _ (iInf₂_le hy hyz.symm))
  · exact Or.inr (einfsep_le_edist_of_mem hy hz hyz)

/--
theorem `einfsep_triple` / 定理 `einfsep_triple`

English:
theorem einfsep_triple
  given: (hxy : x != y) (hyz : y != z) (hxz : x != z)
  proof: by
  simp_rw [einfsep_insert, iInf_insert, iInf_singleton, einfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]

中文:
定理 einfsep_triple
  条件: (hxy : x != y) (hyz : y != z) (hxz : x != z)
  证明: by
  simp_rw [einfsep_insert, iInf_insert, iInf_singleton, einfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]

Depends on / 依赖: ciInf_pos, einfsep_insert, einfsep_singleton, iInf_insert, iInf_singleton, inf_top_eq, simp_rw
-/
theorem einfsep_triple (hxy : x != y) (hyz : y != z) (hxz : x != z) :
    einfsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z := by
  simp_rw [einfsep_insert, iInf_insert, iInf_singleton, einfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]

/--
theorem `le_einfsep_pi_of_le` / 定理 `le_einfsep_pi_of_le`

English:
theorem le_einfsep_pi_of_le
  statement: {X : β -> Type*} [Fintype β] [forall b, PseudoEMetricSpace (X b)]
  proof: by
  refine le_einfsep fun x hx y hy hxy => ?_
  rw [mem_univ_pi] at hx hy
  rcases Function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)

中文:
定理 le_einfsep_pi_of_le
  结论: {X : β -> 类型} [Fintype β] [对任意 b, PseudoEMetricSpace (X b)]
  证明: by
  refine le_einfsep fun x hx y hy hxy => ?_
  rw [mem_univ_pi] at hx hy
  rcases Function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)

Depends on / 依赖: Function, Function.ne_iff.mp, edist_le_pi_edist, le_einfsep, le_einfsep_iff, le_trans, mem_univ_pi, ne_iff
-/
theorem le_einfsep_pi_of_le {X : β -> Type*} [Fintype β] [forall b, PseudoEMetricSpace (X b)]
    {s : forall b : β, Set (X b)} {c : Real>=0∞} (h : forall b, c <= einfsep (s b)) :
    c <= einfsep (Set.pi univ s) := by
  refine le_einfsep fun x hx y hy hxy => ?_
  rw [mem_univ_pi] at hx hy
  rcases Function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {s : Set α}

/--
theorem `subsingleton_of_einfsep_eq_top` / 定理 `subsingleton_of_einfsep_eq_top`

English:
theorem subsingleton_of_einfsep_eq_top
  given: (hs : s.einfsep = ∞)
  statement: s.Subsingleton
  proof: by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)

中文:
定理 subsingleton_of_einfsep_eq_top
  条件: (hs : s.einfsep = ∞)
  结论: s.Subsingleton
  证明: by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)

Depends on / 依赖: edist_ne_top, einfsep_top, of_not_not
-/
theorem subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.Subsingleton := by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)

/--
theorem `einfsep_eq_top_iff` / 定理 `einfsep_eq_top_iff`

English:
theorem einfsep_eq_top_iff
  statement: s.einfsep = ∞ ↔ s.Subsingleton
  proof: ⟨subsingleton_of_einfsep_eq_top, Subsingleton.einfsep⟩

中文:
定理 einfsep_eq_top_iff
  结论: s.einfsep = ∞ ↔ s.Subsingleton
  证明: ⟨subsingleton_of_einfsep_eq_top, Subsingleton.einfsep⟩

Depends on / 依赖: Subsingleton, Subsingleton.einfsep, einfsep, subsingleton_of_einfsep_eq_top
-/
theorem einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingleton :=
  ⟨subsingleton_of_einfsep_eq_top, Subsingleton.einfsep⟩

/--
theorem `Nontrivial.einfsep_ne_top` / 定理 `Nontrivial.einfsep_ne_top`

English:
theorem Nontrivial.einfsep_ne_top
  given: (hs : s.Nontrivial)
  statement: s.einfsep != ∞
  proof: by
  contrapose! hs
  exact subsingleton_of_einfsep_eq_top hs

中文:
定理 Nontrivial.einfsep_ne_top
  条件: (hs : s.Nontrivial)
  结论: s.einfsep != ∞
  证明: by
  contrapose! hs
  exact subsingleton_of_einfsep_eq_top hs

Depends on / 依赖: contrapose, subsingleton_of_einfsep_eq_top
-/
theorem Nontrivial.einfsep_ne_top (hs : s.Nontrivial) : s.einfsep != ∞ := by
  contrapose! hs
  exact subsingleton_of_einfsep_eq_top hs

/--
theorem `Nontrivial.einfsep_lt_top` / 定理 `Nontrivial.einfsep_lt_top`

English:
theorem Nontrivial.einfsep_lt_top
  given: (hs : s.Nontrivial)
  statement: s.einfsep < ∞
  proof: by
  rw [lt_top_iff_ne_top]
  exact hs.einfsep_ne_top

中文:
定理 Nontrivial.einfsep_lt_top
  条件: (hs : s.Nontrivial)
  结论: s.einfsep < ∞
  证明: by
  rw [lt_top_iff_ne_top]
  exact hs.einfsep_ne_top

Depends on / 依赖: einfsep_ne_top, hs.einfsep_ne_top, lt_top_iff_ne_top
-/
theorem Nontrivial.einfsep_lt_top (hs : s.Nontrivial) : s.einfsep < ∞ := by
  rw [lt_top_iff_ne_top]
  exact hs.einfsep_ne_top

/--
theorem `einfsep_lt_top_iff` / 定理 `einfsep_lt_top_iff`

English:
theorem einfsep_lt_top_iff
  statement: s.einfsep < ∞ ↔ s.Nontrivial
  proof: ⟨nontrivial_of_einfsep_lt_top, Nontrivial.einfsep_lt_top⟩

中文:
定理 einfsep_lt_top_iff
  结论: s.einfsep < ∞ ↔ s.Nontrivial
  证明: ⟨nontrivial_of_einfsep_lt_top, Nontrivial.einfsep_lt_top⟩

Depends on / 依赖: Nontrivial, Nontrivial.einfsep_lt_top, einfsep_lt_top, nontrivial_of_einfsep_lt_top
-/
theorem einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_lt_top, Nontrivial.einfsep_lt_top⟩

/--
theorem `einfsep_ne_top_iff` / 定理 `einfsep_ne_top_iff`

English:
theorem einfsep_ne_top_iff
  statement: s.einfsep != ∞ ↔ s.Nontrivial
  proof: ⟨nontrivial_of_einfsep_ne_top, Nontrivial.einfsep_ne_top⟩

中文:
定理 einfsep_ne_top_iff
  结论: s.einfsep != ∞ ↔ s.Nontrivial
  证明: ⟨nontrivial_of_einfsep_ne_top, Nontrivial.einfsep_ne_top⟩

Depends on / 依赖: Nontrivial, Nontrivial.einfsep_ne_top, einfsep_ne_top, nontrivial_of_einfsep_ne_top
-/
theorem einfsep_ne_top_iff : s.einfsep != ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_ne_top, Nontrivial.einfsep_ne_top⟩

/--
theorem `le_einfsep_of_forall_dist_le` / 定理 `le_einfsep_of_forall_dist_le`

English:
theorem le_einfsep_of_forall_dist_le
  given: {d} (h : forall x in s, forall y in s, x != y -> d <= dist x y)
  proof: le_einfsep fun x hx y hy hxy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

中文:
定理 le_einfsep_of_forall_dist_le
  条件: {d} (h : 对任意 x in s, 对任意 y in s, x != y -> d <= dist x y)
  证明: le_einfsep fun x hx y hy hxy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, edist_dist, le_einfsep, ofReal_le_ofReal
-/
theorem le_einfsep_of_forall_dist_le {d} (h : forall x in s, forall y in s, x != y -> d <= dist x y) :
    ENNReal.ofReal d <= s.einfsep :=
  le_einfsep fun x hx y hy hxy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

end PseudoMetricSpace

section EMetricSpace

variable [EMetricSpace α] {s : Set α}

/--
theorem `einfsep_pos_of_finite` / 定理 `einfsep_pos_of_finite`

English:
theorem einfsep_pos_of_finite
  given: [Finite s]
  statement: 0 < s.einfsep
  proof: by
  cases nonempty_fintype s
  by_cases hs : s.Nontrivial
  · rcases hs.einfsep_exists_of_finite with ⟨x, _hx, y, _hy, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    exact hs.einfsep.symm ▸ WithTop.top_pos

中文:
定理 einfsep_pos_of_finite
  条件: [Finite s]
  结论: 0 < s.einfsep
  证明: by
  cases nonempty_fintype s
  by_cases hs : s.Nontrivial
  · rcases hs.einfsep_exists_of_finite with ⟨x, _hx, y, _hy, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    exact hs.einfsep.symm ▸ WithTop.top_pos

Depends on / 依赖: Nontrivial, WithTop, WithTop.top_pos, edist_pos, einfsep, einfsep_exists_of_finite, hs.einfsep.symm, hs.einfsep_exists_of_finite, nonempty_fintype, not_nontrivial_iff, s.Nontrivial, top_pos
-/
theorem einfsep_pos_of_finite [Finite s] : 0 < s.einfsep := by
  cases nonempty_fintype s
  by_cases hs : s.Nontrivial
  · rcases hs.einfsep_exists_of_finite with ⟨x, _hx, y, _hy, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    exact hs.einfsep.symm ▸ WithTop.top_pos

/--
theorem `relatively_discrete_of_finite` / 定理 `relatively_discrete_of_finite`

English:
theorem relatively_discrete_of_finite
  given: [Finite s]
  proof: by
  rw [← einfsep_pos]
  exact einfsep_pos_of_finite

中文:
定理 relatively_discrete_of_finite
  条件: [Finite s]
  证明: by
  rw [← einfsep_pos]
  exact einfsep_pos_of_finite

Depends on / 依赖: einfsep_pos, einfsep_pos_of_finite
-/
theorem relatively_discrete_of_finite [Finite s] :
    exists C > 0, forall x in s, forall y in s, x != y -> C <= edist x y := by
  rw [← einfsep_pos]
  exact einfsep_pos_of_finite

/--
theorem `Finite.einfsep_pos` / 定理 `Finite.einfsep_pos`

English:
theorem Finite.einfsep_pos
  given: (hs : s.Finite)
  statement: 0 < s.einfsep
  proof: letI := hs.fintype
  einfsep_pos_of_finite

中文:
定理 Finite.einfsep_pos
  条件: (hs : s.Finite)
  结论: 0 < s.einfsep
  证明: letI := hs.fintype
  einfsep_pos_of_finite

Depends on / 依赖: einfsep_pos_of_finite, fintype, hs.fintype
-/
theorem Finite.einfsep_pos (hs : s.Finite) : 0 < s.einfsep :=
  letI := hs.fintype
  einfsep_pos_of_finite

/--
theorem `Finite.relatively_discrete` / 定理 `Finite.relatively_discrete`

English:
theorem Finite.relatively_discrete
  given: (hs : s.Finite)
  proof: letI := hs.fintype
  relatively_discrete_of_finite

中文:
定理 Finite.relatively_discrete
  条件: (hs : s.Finite)
  证明: letI := hs.fintype
  relatively_discrete_of_finite

Depends on / 依赖: fintype, hs.fintype, relatively_discrete_of_finite
-/
theorem Finite.relatively_discrete (hs : s.Finite) :
    exists C > 0, forall x in s, forall y in s, x != y -> C <= edist x y :=
  letI := hs.fintype
  relatively_discrete_of_finite

end EMetricSpace

end Einfsep

section Infsep

open ENNReal

open Set Function

/--
Definition of `infsep` / `infsep` 的定义

English:
definition infsep
  signature: [EDist α] (s : Set α)
  body: ENNReal.toReal s.einfsep

中文:
定义 infsep
  签名: [EDist α] (s : Set α)
  定义体: ENNReal.toReal s.einfsep

Depends on / 依赖: ENNReal, ENNReal.toReal, einfsep, s.einfsep, toReal
-/
noncomputable def infsep [EDist α] (s : Set α) : Real :=
  ENNReal.toReal s.einfsep

section EDist

variable [EDist α] {x y : α} {s : Set α}

/--
theorem `infsep_zero` / 定理 `infsep_zero`

English:
theorem infsep_zero
  statement: s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞
  proof: by
  rw [infsep]; rw [ENNReal.toReal_eq_zero_iff]

中文:
定理 infsep_zero
  结论: s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞
  证明: by
  rw [infsep]; rw [ENNReal.toReal_eq_zero_iff]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, infsep, toReal_eq_zero_iff
-/
theorem infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞ := by
  rw [infsep]; rw [ENNReal.toReal_eq_zero_iff]

/--
theorem `infsep_nonneg` / 定理 `infsep_nonneg`

English:
theorem infsep_nonneg
  statement: 0 <= s.infsep
  proof: ENNReal.toReal_nonneg

中文:
定理 infsep_nonneg
  结论: 0 <= s.infsep
  证明: ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, toReal_nonneg
-/
theorem infsep_nonneg : 0 <= s.infsep :=
  ENNReal.toReal_nonneg

/--
theorem `infsep_pos` / 定理 `infsep_pos`

English:
theorem infsep_pos
  statement: 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞
  proof: by
  simp_rw [infsep, ENNReal.toReal_pos_iff]

中文:
定理 infsep_pos
  结论: 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞
  证明: by
  simp_rw [infsep, ENNReal.toReal_pos_iff]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff, infsep, simp_rw, toReal_pos_iff
-/
theorem infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞ := by
  simp_rw [infsep, ENNReal.toReal_pos_iff]

/--
theorem `Subsingleton.infsep_zero` / 定理 `Subsingleton.infsep_zero`

English:
theorem Subsingleton.infsep_zero
  given: (hs : s.Subsingleton)
  statement: s.infsep = 0
  proof: Set.infsep_zero.mpr Or.inr hs.einfsep

中文:
定理 Subsingleton.infsep_zero
  条件: (hs : s.Subsingleton)
  结论: s.infsep = 0
  证明: Set.infsep_zero.mpr Or.inr hs.einfsep

Depends on / 依赖: Or.inr, Set.infsep_zero.mpr, einfsep, hs.einfsep, infsep_zero
-/
theorem Subsingleton.infsep_zero (hs : s.Subsingleton) : s.infsep = 0 :=
Set.infsep_zero.mpr Or.inr hs.einfsep

/--
theorem `nontrivial_of_infsep_pos` / 定理 `nontrivial_of_infsep_pos`

English:
theorem nontrivial_of_infsep_pos
  given: (hs : 0 < s.infsep)
  statement: s.Nontrivial
  proof: by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  exact hs.infsep_zero ▸ lt_irrefl _

中文:
定理 nontrivial_of_infsep_pos
  条件: (hs : 0 < s.infsep)
  结论: s.Nontrivial
  证明: by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  exact hs.infsep_zero ▸ lt_irrefl _

Depends on / 依赖: contrapose, hs.infsep_zero, infsep_zero, lt_irrefl, not_nontrivial_iff
-/
theorem nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.Nontrivial := by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  exact hs.infsep_zero ▸ lt_irrefl _

/--
theorem `infsep_empty` / 定理 `infsep_empty`

English:
theorem infsep_empty
  statement: (∅ : Set α).infsep = 0
  proof: subsingleton_empty.infsep_zero

中文:
定理 infsep_empty
  结论: (∅ : Set α).infsep = 0
  证明: subsingleton_empty.infsep_zero

Depends on / 依赖: infsep_zero, subsingleton_empty, subsingleton_empty.infsep_zero
-/
theorem infsep_empty : (∅ : Set α).infsep = 0 :=
  subsingleton_empty.infsep_zero

/--
theorem `infsep_singleton` / 定理 `infsep_singleton`

English:
theorem infsep_singleton
  statement: ({x} : Set α).infsep = 0
  proof: subsingleton_singleton.infsep_zero

中文:
定理 infsep_singleton
  结论: ({x} : Set α).infsep = 0
  证明: subsingleton_singleton.infsep_zero

Depends on / 依赖: infsep_zero, subsingleton_singleton, subsingleton_singleton.infsep_zero
-/
theorem infsep_singleton : ({x} : Set α).infsep = 0 :=
  subsingleton_singleton.infsep_zero

/--
theorem `infsep_pair_le_toReal_inf` / 定理 `infsep_pair_le_toReal_inf`

English:
theorem infsep_pair_le_toReal_inf
  given: (hxy : x != y)
  proof: by
  simp_rw [infsep, einfsep_pair_eq_inf hxy]
  simp

中文:
定理 infsep_pair_le_toReal_inf
  条件: (hxy : x != y)
  证明: by
  simp_rw [infsep, einfsep_pair_eq_inf hxy]
  simp

Depends on / 依赖: einfsep_pair_eq_inf, infsep, simp_rw
-/
theorem infsep_pair_le_toReal_inf (hxy : x != y) :
    ({x, y} : Set α).infsep <= (edist x y ⊓ edist y x).toReal := by
  simp_rw [infsep, einfsep_pair_eq_inf hxy]
  simp

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y : α}

/--
theorem `infsep_pair_eq_toReal` / 定理 `infsep_pair_eq_toReal`

English:
theorem infsep_pair_eq_toReal
  statement: ({x, y} : Set α).infsep = (edist x y).toReal
  proof: by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.toReal_zero]
  · rw [infsep, einfsep_pair hxy]

中文:
定理 infsep_pair_eq_toReal
  结论: ({x, y} : Set α).infsep = (edist x y).to实数
  证明: by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.toReal_zero]
  · rw [infsep, einfsep_pair hxy]

Depends on / 依赖: ENNReal, ENNReal.toReal_zero, edist_self, einfsep_pair, infsep, infsep_singleton, pair_eq_singleton, toReal_zero
-/
theorem infsep_pair_eq_toReal : ({x, y} : Set α).infsep = (edist x y).toReal := by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.toReal_zero]
  · rw [infsep, einfsep_pair hxy]

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {x y z : α} {s t : Set α}

/--
theorem `Nontrivial.le_infsep_iff` / 定理 `Nontrivial.le_infsep_iff`

English:
theorem Nontrivial.le_infsep_iff
  given: {d} (hs : s.Nontrivial)
  proof: by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal hs.einfsep_ne_top, le_einfsep_iff, edist_dist,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]

中文:
定理 Nontrivial.le_infsep_iff
  条件: {d} (hs : s.Nontrivial)
  证明: by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal hs.einfsep_ne_top, le_einfsep_iff, edist_dist,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_iff_le_toReal, ENNReal.ofReal_le_ofReal_iff, dist_nonneg, edist_dist, einfsep_ne_top, hs.einfsep_ne_top, infsep, le_einfsep_iff, ofReal_le_iff_le_toReal, ofReal_le_ofReal_iff, simp_rw
-/
theorem Nontrivial.le_infsep_iff {d} (hs : s.Nontrivial) :
    d <= s.infsep ↔ forall x in s, forall y in s, x != y -> d <= dist x y := by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal hs.einfsep_ne_top, le_einfsep_iff, edist_dist,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]

/--
theorem `Nontrivial.infsep_lt_iff` / 定理 `Nontrivial.infsep_lt_iff`

English:
theorem Nontrivial.infsep_lt_iff
  given: {d} (hs : s.Nontrivial)
  proof: by
  contrapose!; exact hs.le_infsep_iff

中文:
定理 Nontrivial.infsep_lt_iff
  条件: {d} (hs : s.Nontrivial)
  证明: by
  contrapose!; exact hs.le_infsep_iff

Depends on / 依赖: contrapose, hs.le_infsep_iff, le_infsep_iff
-/
theorem Nontrivial.infsep_lt_iff {d} (hs : s.Nontrivial) :
    s.infsep < d ↔ exists x in s, exists y in s, x != y ∧ dist x y < d := by
  contrapose!; exact hs.le_infsep_iff

/--
theorem `Nontrivial.le_infsep` / 定理 `Nontrivial.le_infsep`

English:
theorem Nontrivial.le_infsep
  statement: {d} (hs : s.Nontrivial)
  proof: hs.le_infsep_iff.2 h

中文:
定理 Nontrivial.le_infsep
  结论: {d} (hs : s.Nontrivial)
  证明: hs.le_infsep_iff.2 h

Depends on / 依赖: hs.le_infsep_iff, le_infsep_iff
-/
theorem Nontrivial.le_infsep {d} (hs : s.Nontrivial)
    (h : forall x in s, forall y in s, x != y -> d <= dist x y) : d <= s.infsep :=
  hs.le_infsep_iff.2 h

/--
theorem `le_edist_of_le_infsep` / 定理 `le_edist_of_le_infsep`

English:
theorem le_edist_of_le_infsep
  statement: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  proof: by
  by_cases hs : s.Nontrivial
  · exact hs.le_infsep_iff.1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [hs.infsep_zero] at hd
    exact le_trans hd dist_nonneg

中文:
定理 le_edist_of_le_infsep
  结论: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  证明: by
  by_cases hs : s.Nontrivial
  · exact hs.le_infsep_iff.1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [hs.infsep_zero] at hd
    exact le_trans hd dist_nonneg

Depends on / 依赖: Nontrivial, dist_nonneg, hs.infsep_zero, hs.le_infsep_iff, infsep_zero, le_infsep_iff, le_trans, not_nontrivial_iff, s.Nontrivial
-/
theorem le_edist_of_le_infsep {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
    (hd : d <= s.infsep) : d <= dist x y := by
  by_cases hs : s.Nontrivial
  · exact hs.le_infsep_iff.1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [hs.infsep_zero] at hd
    exact le_trans hd dist_nonneg

/--
theorem `infsep_le_dist_of_mem` / 定理 `infsep_le_dist_of_mem`

English:
theorem infsep_le_dist_of_mem
  given: (hx : x in s) (hy : y in s) (hxy : x != y)
  statement: s.infsep <= dist x y
  proof: le_edist_of_le_infsep hx hy hxy le_rfl

中文:
定理 infsep_le_dist_of_mem
  条件: (hx : x in s) (hy : y in s) (hxy : x != y)
  结论: s.infsep <= dist x y
  证明: le_edist_of_le_infsep hx hy hxy le_rfl

Depends on / 依赖: le_edist_of_le_infsep, le_rfl
-/
theorem infsep_le_dist_of_mem (hx : x in s) (hy : y in s) (hxy : x != y) : s.infsep <= dist x y :=
  le_edist_of_le_infsep hx hy hxy le_rfl

/--
theorem `infsep_le_of_mem_of_edist_le` / 定理 `infsep_le_of_mem_of_edist_le`

English:
theorem infsep_le_of_mem_of_edist_le
  statement: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  proof: le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'

中文:
定理 infsep_le_of_mem_of_edist_le
  结论: {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
  证明: le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'

Depends on / 依赖: infsep_le_dist_of_mem, le_trans
-/
theorem infsep_le_of_mem_of_edist_le {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
    (hxy' : dist x y <= d) : s.infsep <= d :=
  le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'

/--
theorem `infsep_pair` / 定理 `infsep_pair`

English:
theorem infsep_pair
  statement: ({x, y} : Set α).infsep = dist x y
  proof: by
  rw [infsep_pair_eq_toReal]; rw [edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg

中文:
定理 infsep_pair
  结论: ({x, y} : Set α).infsep = dist x y
  证明: by
  rw [infsep_pair_eq_toReal]; rw [edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, dist_nonneg, edist_dist, infsep_pair_eq_toReal, toReal_ofReal
-/
theorem infsep_pair : ({x, y} : Set α).infsep = dist x y := by
  rw [infsep_pair_eq_toReal]; rw [edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg

/--
theorem `infsep_triple` / 定理 `infsep_triple`

English:
theorem infsep_triple
  given: (hxy : x != y) (hyz : y != z) (hxz : x != z)
  proof: by
  simp only [infsep, einfsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne, inf_eq_top_iff, and_self_iff,
    not_false_iff]

中文:
定理 infsep_triple
  条件: (hxy : x != y) (hyz : y != z) (hxz : x != z)
  证明: by
  simp only [infsep, einfsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne, inf_eq_top_iff, and_self_iff,
    not_false_iff]

Depends on / 依赖: ENNReal, ENNReal.toReal_inf, and_self_iff, dist_edist, edist_ne_top, einfsep_triple, inf_eq_top_iff, infsep, not_false_iff, toReal_inf
-/
theorem infsep_triple (hxy : x != y) (hyz : y != z) (hxz : x != z) :
    ({x, y, z} : Set α).infsep = dist x y ⊓ dist x z ⊓ dist y z := by
  simp only [infsep, einfsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne, inf_eq_top_iff, and_self_iff,
    not_false_iff]

/--
theorem `Nontrivial.infsep_anti` / 定理 `Nontrivial.infsep_anti`

English:
theorem Nontrivial.infsep_anti
  given: (hs : s.Nontrivial) (hst : s subseteq t)
  statement: t.infsep <= s.infsep
  proof: ENNReal.toReal_mono hs.einfsep_ne_top (einfsep_anti hst)

中文:
定理 Nontrivial.infsep_anti
  条件: (hs : s.Nontrivial) (hst : s subseteq t)
  结论: t.infsep <= s.infsep
  证明: ENNReal.toReal_mono hs.einfsep_ne_top (einfsep_anti hst)

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, einfsep_anti, einfsep_ne_top, hs.einfsep_ne_top, toReal_mono
-/
theorem Nontrivial.infsep_anti (hs : s.Nontrivial) (hst : s subseteq t) : t.infsep <= s.infsep :=
  ENNReal.toReal_mono hs.einfsep_ne_top (einfsep_anti hst)

/--
theorem `infsep_eq_iInf` / 定理 `infsep_eq_iInf`

English:
theorem infsep_eq_iInf
  given: [Decidable s.Nontrivial]
  proof: by
  split_ifs with hs
  · have hb : BddBelow (uncurry dist '' s.offDiag) := by
      refine ⟨0, fun d h => ?_⟩
      simp_rw [mem_image, Prod.exists, uncurry_apply_pair] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact dist_nonneg
    refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_inf

中文:
定理 infsep_eq_iInf
  条件: [Decidable s.Nontrivial]
  证明: by
  split_ifs with hs
  · have hb : BddBelow (uncurry dist '' s.offDiag) := by
      refine ⟨0, fun d h => ?_⟩
      simp_rw [mem_image, Prod.exists, uncurry_apply_pair] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact dist_nonneg
    refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_inf

Depends on / 依赖: BddBelow, Prod.exists, Prod.forall, and_imp, dist_nonneg, eq_of_forall_le_iff, hs.le_infsep_iff, imp_forall_iff, infsep_zero, le_ciInf_set_iff, le_infsep_iff, mem_image, mem_offDiag, not_nontrivial_iff, not_nontrivial_iff.mp, offDiag, offDiag_nonempty, offDiag_nonempty.mpr, s.offDiag, simp_rw
-/
theorem infsep_eq_iInf [Decidable s.Nontrivial] :
    s.infsep = if s.Nontrivial then ⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0 := by
  split_ifs with hs
  · have hb : BddBelow (uncurry dist '' s.offDiag) := by
      refine ⟨0, fun d h => ?_⟩
      simp_rw [mem_image, Prod.exists, uncurry_apply_pair] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact dist_nonneg
    refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, le_ciInf_set_iff (offDiag_nonempty.mpr hs) hb, imp_forall_iff,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · exact (not_nontrivial_iff.mp hs).infsep_zero

/--
theorem `Nontrivial.infsep_eq_iInf` / 定理 `Nontrivial.infsep_eq_iInf`

English:
theorem Nontrivial.infsep_eq_iInf
  given: (hs : s.Nontrivial)
  proof: by
  classical rw [Set.infsep_eq_iInf, if_pos hs]

中文:
定理 Nontrivial.infsep_eq_iInf
  条件: (hs : s.Nontrivial)
  证明: by
  classical rw [Set.infsep_eq_iInf, if_pos hs]

Depends on / 依赖: Set.infsep_eq_iInf, classical, if_pos, infsep_eq_iInf
-/
theorem Nontrivial.infsep_eq_iInf (hs : s.Nontrivial) :
    s.infsep = ⨅ d : s.offDiag, (uncurry dist) (d : α × α) := by
  classical rw [Set.infsep_eq_iInf, if_pos hs]

/--
theorem `infsep_of_fintype` / 定理 `infsep_of_fintype`

English:
theorem infsep_of_fintype
  given: [Decidable s.Nontrivial] [Fintype s]
  statement: s.infsep =
  proof: by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, mem_toFinset, mem_offDiag,
      Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

中文:
定理 infsep_of_fintype
  条件: [Decidable s.Nontrivial] [Fintype s]
  结论: s.infsep =
  证明: by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, mem_toFinset, mem_offDiag,
      Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

Depends on / 依赖: Finset, Finset.le_inf, Prod.forall, _iff, and_imp, eq_of_forall_le_iff, hs.infsep_zero, hs.le_infsep_iff, imp_forall_iff, infsep_zero, le_inf, le_infsep_iff, mem_offDiag, mem_toFinset, not_nontrivial_iff, simp_rw, split_ifs, uncurry_apply_pair
-/
theorem infsep_of_fintype [Decidable s.Nontrivial] [Fintype s] : s.infsep =
    if hs : s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, mem_toFinset, mem_offDiag,
      Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

/--
theorem `Nontrivial.infsep_of_fintype` / 定理 `Nontrivial.infsep_of_fintype`

English:
theorem Nontrivial.infsep_of_fintype
  given: [Fintype s] (hs : s.Nontrivial)
  proof: by
  classical rw [Set.infsep_of_fintype, dif_pos hs]

中文:
定理 Nontrivial.infsep_of_fintype
  条件: [Fintype s] (hs : s.Nontrivial)
  证明: by
  classical rw [Set.infsep_of_fintype, dif_pos hs]

Depends on / 依赖: Set.infsep_of_fintype, classical, dif_pos, infsep_of_fintype
-/
theorem Nontrivial.infsep_of_fintype [Fintype s] (hs : s.Nontrivial) :
    s.infsep = s.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical rw [Set.infsep_of_fintype, dif_pos hs]

/--
theorem `Finite.infsep` / 定理 `Finite.infsep`

English:
theorem Finite.infsep
  given: [Decidable s.Nontrivial] (hsf : s.Finite)
  proof: by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, Finite.mem_toFinset,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

中文:
定理 Finite.infsep
  条件: [Decidable s.Nontrivial] (hsf : s.Finite)
  证明: by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, Finite.mem_toFinset,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.le_inf, Prod.forall, _iff, and_imp, eq_of_forall_le_iff, hs.infsep_zero, hs.le_infsep_iff, imp_forall_iff, infsep_zero, le_inf, le_infsep_iff, mem_offDiag, mem_toFinset, not_nontrivial_iff, simp_rw, split_ifs, uncurry_apply_pair
-/
theorem Finite.infsep [Decidable s.Nontrivial] (hsf : s.Finite) :
    s.infsep =
      if hs : s.Nontrivial then hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, Finite.mem_toFinset,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

/--
theorem `Finite.infsep_of_nontrivial` / 定理 `Finite.infsep_of_nontrivial`

English:
theorem Finite.infsep_of_nontrivial
  given: (hsf : s.Finite) (hs : s.Nontrivial)
  proof: by
  classical simp_rw [hsf.infsep, dif_pos hs]

中文:
定理 Finite.infsep_of_nontrivial
  条件: (hsf : s.Finite) (hs : s.Nontrivial)
  证明: by
  classical simp_rw [hsf.infsep, dif_pos hs]

Depends on / 依赖: classical, dif_pos, hsf.infsep, infsep, simp_rw
-/
theorem Finite.infsep_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    s.infsep = hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical simp_rw [hsf.infsep, dif_pos hs]

/--
theorem `_root_.Finset.coe_infsep` / 定理 `_root_.Finset.coe_infsep`

English:
theorem _root_.Finset.coe_infsep
  given: (s : Finset α)
  statement: (s : Set α).infsep =
  proof: by
  have H : (s : Set α).Nontrivial ↔ s.offDiag.Nonempty := by
    rw [← Set.offDiag_nonempty]; rw [← Finset.coe_offDiag]; rw [Finset.coe_nonempty]
  split_ifs with hs
  · classical simp_rw [(H.mpr hs).infsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
  · exact (not_nontrivial_iff.mp (H

中文:
定理 _root_.Finset.coe_infsep
  条件: (s : Finset α)
  结论: (s : Set α).infsep =
  证明: by
  have H : (s : Set α).Nontrivial ↔ s.offDiag.Nonempty := by
    rw [← Set.offDiag_nonempty]; rw [← Finset.coe_offDiag]; rw [Finset.coe_nonempty]
  split_ifs with hs
  · classical simp_rw [(H.mpr hs).infsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
  · exact (not_nontrivial_iff.mp (H

Depends on / 依赖: Finset, Finset.coe_nonempty, Finset.coe_offDiag, Finset.toFinset_coe, H.mp.mt, H.mpr, Nonempty, Nontrivial, Set.offDiag_nonempty, classical, coe_nonempty, coe_offDiag, infsep_of_fintype, infsep_zero, not_nontrivial_iff, not_nontrivial_iff.mp, offDiag, offDiag_nonempty, s.offDiag.Nonempty, simp_rw
-/
theorem _root_.Finset.coe_infsep (s : Finset α) : (s : Set α).infsep =
    if hs : s.offDiag.Nonempty then s.offDiag.inf' hs (uncurry dist) else 0 := by
  have H : (s : Set α).Nontrivial ↔ s.offDiag.Nonempty := by
    rw [← Set.offDiag_nonempty]; rw [← Finset.coe_offDiag]; rw [Finset.coe_nonempty]
  split_ifs with hs
  · classical simp_rw [(H.mpr hs).infsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
  · exact (not_nontrivial_iff.mp (H.mp.mt hs)).infsep_zero

/--
theorem `_root_.Finset.coe_infsep_of_offDiag_nonempty` / 定理 `_root_.Finset.coe_infsep_of_offDiag_nonempty`

English:
theorem _root_.Finset.coe_infsep_of_offDiag_nonempty
  statement: {s : Finset α}
  proof: by
  rw [Finset.coe_infsep]; rw [dif_pos hs]

中文:
定理 _root_.Finset.coe_infsep_of_offDiag_nonempty
  结论: {s : Finset α}
  证明: by
  rw [Finset.coe_infsep]; rw [dif_pos hs]

Depends on / 依赖: Finset, Finset.coe_infsep, coe_infsep, dif_pos
-/
theorem _root_.Finset.coe_infsep_of_offDiag_nonempty {s : Finset α}
    (hs : s.offDiag.Nonempty) : (s : Set α).infsep = s.offDiag.inf' hs (uncurry dist) := by
  rw [Finset.coe_infsep]; rw [dif_pos hs]

/--
theorem `_root_.Finset.coe_infsep_of_offDiag_empty` / 定理 `_root_.Finset.coe_infsep_of_offDiag_empty`

English:
theorem _root_.Finset.coe_infsep_of_offDiag_empty
  proof: by
  rw [← Finset.not_nonempty_iff_eq_empty] at hs
  rw [Finset.coe_infsep]; rw [dif_neg hs]

中文:
定理 _root_.Finset.coe_infsep_of_offDiag_empty
  证明: by
  rw [← Finset.not_nonempty_iff_eq_empty] at hs
  rw [Finset.coe_infsep]; rw [dif_neg hs]

Depends on / 依赖: Finset, Finset.coe_infsep, Finset.not_nonempty_iff_eq_empty, coe_infsep, dif_neg, not_nonempty_iff_eq_empty
-/
theorem _root_.Finset.coe_infsep_of_offDiag_empty
    {s : Finset α} (hs : s.offDiag = ∅) : (s : Set α).infsep = 0 := by
  rw [← Finset.not_nonempty_iff_eq_empty] at hs
  rw [Finset.coe_infsep]; rw [dif_neg hs]

/--
theorem `Nontrivial.infsep_exists_of_finite` / 定理 `Nontrivial.infsep_exists_of_finite`

English:
theorem Nontrivial.infsep_exists_of_finite
  given: [Finite s] (hs : s.Nontrivial)
  proof: by
  cases nonempty_fintype s
  simp_rw [hs.infsep_of_fintype]
  rcases Finset.exists_mem_eq_inf' (s := s.offDiag.toFinset) (by simpa) (uncurry dist) with
    ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

中文:
定理 Nontrivial.infsep_exists_of_finite
  条件: [Finite s] (hs : s.Nontrivial)
  证明: by
  cases nonempty_fintype s
  simp_rw [hs.infsep_of_fintype]
  rcases Finset.exists_mem_eq_inf' (s := s.offDiag.toFinset) (by simpa) (uncurry dist) with
    ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

Depends on / 依赖: Finset, Finset.exists_mem_eq_inf, exists_mem_eq_inf, hs.infsep_of_fintype, infsep_of_fintype, mem_toFinset, nonempty_fintype, offDiag, s.offDiag.toFinset, simp_rw, toFinset, uncurry, w.fst, w.snd
-/
theorem Nontrivial.infsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    exists x in s, exists y in s, x != y ∧ s.infsep = dist x y := by
  cases nonempty_fintype s
  simp_rw [hs.infsep_of_fintype]
  rcases Finset.exists_mem_eq_inf' (s := s.offDiag.toFinset) (by simpa) (uncurry dist) with
    ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

/--
theorem `Finite.infsep_exists_of_nontrivial` / 定理 `Finite.infsep_exists_of_nontrivial`

English:
theorem Finite.infsep_exists_of_nontrivial
  given: (hsf : s.Finite) (hs : s.Nontrivial)
  proof: letI := hsf.fintype
  hs.infsep_exists_of_finite

中文:
定理 Finite.infsep_exists_of_nontrivial
  条件: (hsf : s.Finite) (hs : s.Nontrivial)
  证明: letI := hsf.fintype
  hs.infsep_exists_of_finite

Depends on / 依赖: fintype, hs.infsep_exists_of_finite, hsf.fintype, infsep_exists_of_finite
-/
theorem Finite.infsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    exists x in s, exists y in s, x != y ∧ s.infsep = dist x y :=
  letI := hsf.fintype
  hs.infsep_exists_of_finite

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace α] {s : Set α}

/--
theorem `infsep_zero_iff_subsingleton_of_finite` / 定理 `infsep_zero_iff_subsingleton_of_finite`

English:
theorem infsep_zero_iff_subsingleton_of_finite
  given: [Finite s]
  statement: s.infsep = 0 ↔ s.Subsingleton
  proof: by
  rw [infsep_zero]; rw [einfsep_eq_top_iff]; rw [or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim

中文:
定理 infsep_zero_iff_subsingleton_of_finite
  条件: [Finite s]
  结论: s.infsep = 0 ↔ s.Subsingleton
  证明: by
  rw [infsep_zero]; rw [einfsep_eq_top_iff]; rw [or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim

Depends on / 依赖: einfsep_eq_top_iff, einfsep_pos_of_finite, einfsep_pos_of_finite.ne, infsep_zero, or_iff_right_iff_imp
-/
theorem infsep_zero_iff_subsingleton_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsingleton := by
  rw [infsep_zero]; rw [einfsep_eq_top_iff]; rw [or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim

/--
theorem `infsep_pos_iff_nontrivial_of_finite` / 定理 `infsep_pos_iff_nontrivial_of_finite`

English:
theorem infsep_pos_iff_nontrivial_of_finite
  given: [Finite s]
  statement: 0 < s.infsep ↔ s.Nontrivial
  proof: by
  rw [infsep_pos]; rw [einfsep_lt_top_iff]; rw [and_iff_right_iff_imp]
  exact fun _ => einfsep_pos_of_finite

中文:
定理 infsep_pos_iff_nontrivial_of_finite
  条件: [Finite s]
  结论: 0 < s.infsep ↔ s.Nontrivial
  证明: by
  rw [infsep_pos]; rw [einfsep_lt_top_iff]; rw [and_iff_right_iff_imp]
  exact fun _ => einfsep_pos_of_finite

Depends on / 依赖: and_iff_right_iff_imp, einfsep_lt_top_iff, einfsep_pos_of_finite, infsep_pos
-/
theorem infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivial := by
  rw [infsep_pos]; rw [einfsep_lt_top_iff]; rw [and_iff_right_iff_imp]
  exact fun _ => einfsep_pos_of_finite

/--
theorem `Finite.infsep_zero_iff_subsingleton` / 定理 `Finite.infsep_zero_iff_subsingleton`

English:
theorem Finite.infsep_zero_iff_subsingleton
  given: (hs : s.Finite)
  statement: s.infsep = 0 ↔ s.Subsingleton
  proof: letI := hs.fintype
  infsep_zero_iff_subsingleton_of_finite

中文:
定理 Finite.infsep_zero_iff_subsingleton
  条件: (hs : s.Finite)
  结论: s.infsep = 0 ↔ s.Subsingleton
  证明: letI := hs.fintype
  infsep_zero_iff_subsingleton_of_finite

Depends on / 依赖: fintype, hs.fintype, infsep_zero_iff_subsingleton_of_finite
-/
theorem Finite.infsep_zero_iff_subsingleton (hs : s.Finite) : s.infsep = 0 ↔ s.Subsingleton :=
  letI := hs.fintype
  infsep_zero_iff_subsingleton_of_finite

/--
theorem `Finite.infsep_pos_iff_nontrivial` / 定理 `Finite.infsep_pos_iff_nontrivial`

English:
theorem Finite.infsep_pos_iff_nontrivial
  given: (hs : s.Finite)
  statement: 0 < s.infsep ↔ s.Nontrivial
  proof: letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite

中文:
定理 Finite.infsep_pos_iff_nontrivial
  条件: (hs : s.Finite)
  结论: 0 < s.infsep ↔ s.Nontrivial
  证明: letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite

Depends on / 依赖: fintype, hs.fintype, infsep_pos_iff_nontrivial_of_finite
-/
theorem Finite.infsep_pos_iff_nontrivial (hs : s.Finite) : 0 < s.infsep ↔ s.Nontrivial :=
  letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite

/--
theorem `_root_.Finset.infsep_zero_iff_subsingleton` / 定理 `_root_.Finset.infsep_zero_iff_subsingleton`

English:
theorem _root_.Finset.infsep_zero_iff_subsingleton
  given: (s : Finset α)
  proof: infsep_zero_iff_subsingleton_of_finite

中文:
定理 _root_.Finset.infsep_zero_iff_subsingleton
  条件: (s : Finset α)
  证明: infsep_zero_iff_subsingleton_of_finite

Depends on / 依赖: infsep_zero_iff_subsingleton_of_finite
-/
theorem _root_.Finset.infsep_zero_iff_subsingleton (s : Finset α) :
    (s : Set α).infsep = 0 ↔ (s : Set α).Subsingleton :=
  infsep_zero_iff_subsingleton_of_finite

/--
theorem `_root_.Finset.infsep_pos_iff_nontrivial` / 定理 `_root_.Finset.infsep_pos_iff_nontrivial`

English:
theorem _root_.Finset.infsep_pos_iff_nontrivial
  given: (s : Finset α)
  proof: infsep_pos_iff_nontrivial_of_finite

中文:
定理 _root_.Finset.infsep_pos_iff_nontrivial
  条件: (s : Finset α)
  证明: infsep_pos_iff_nontrivial_of_finite

Depends on / 依赖: infsep_pos_iff_nontrivial_of_finite
-/
theorem _root_.Finset.infsep_pos_iff_nontrivial (s : Finset α) :
    0 < (s : Set α).infsep ↔ (s : Set α).Nontrivial :=
  infsep_pos_iff_nontrivial_of_finite

end MetricSpace

end Infsep

end Set
