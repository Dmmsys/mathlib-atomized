/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Cofinal
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cofinality of an order

This file contains the definition of the cofinality `Order.cof α` of an order. This is the smallest
cardinality of a cofinal subset.
-/

public noncomputable section

open Function Cardinal Set Order

universe u v w

variable {α γ : Type u} {β : Type v}

/-! ### Cofinality of orders -/

namespace Order
section Preorder
variable [Preorder α]

variable (α) in
/-- The cofinality of a preorder is the smallest cardinality of a cofinal subset. -/
@[wikidata Q1283623]
/--
Definition of `cof` / `cof` 的定义

English:
definition cof
  signature: : Cardinal
  body: ⨅ s : {s : Set α // IsCofinal s}, #s

中文:
定义 cof
  签名: : 基数
  定义体: ⨅ s : {s : Set α // IsCofinal s}, #s

Depends on / 依赖: IsCofinal, equivShrink, symm.topologicalSpace, topologicalSpace
-/
def cof : Cardinal :=
  ⨅ s : {s : Set α // IsCofinal s}, #s

/--
theorem `cof_le` / 定理 `cof_le`

English:
theorem cof_le
  given: {s : Set α} (h : IsCofinal s)
  statement: cof α <= #s
  proof: ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩

中文:
定理 cof_le
  条件: {s : 集合 α} (h : IsCofinal s)
  结论: cof α <= #s
  证明: ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩

Depends on / 依赖: IsCofinal, ciInf_le
-/
theorem cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s :=
  ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩

/--
theorem `le_lift_cof_iff` / 定理 `le_lift_cof_iff`

English:
theorem le_lift_cof_iff
  given: {c : Cardinal.{max u v}}
  proof: by
  rw [cof]; rw [lift_iInf]; rw [le_ciInf_iff']
  simp

中文:
定理 le_lift_cof_iff
  条件: {c : 基数.{最大值 u v}}
  证明: by
  rw [cof]; rw [lift_iInf]; rw [le_ciInf_iff']
  simp

Depends on / 依赖: le_ciInf_iff, lift_iInf
-/
theorem le_lift_cof_iff {c : Cardinal.{max u v}} :
    c <= lift.{v} (cof α) ↔ forall s : Set α, IsCofinal s -> c <= lift.{v} #s := by
  rw [cof]; rw [lift_iInf]; rw [le_ciInf_iff']
  simp

/--
theorem `le_cof_iff` / 定理 `le_cof_iff`

English:
theorem le_cof_iff
  given: {c : Cardinal}
  statement: c <= cof α ↔ forall s : Set α, IsCofinal s -> c <= #s
  proof: by
  simpa using @le_lift_cof_iff.{u, u} α _ c

@[deprecated (since := "2026-02-18")] alias le_cof := le_cof_iff

中文:
定理 le_cof_iff
  条件: {c : 基数}
  结论: c <= cof α ↔ 对任意 s : 集合 α, IsCofinal s -> c <= #s
  证明: by
  simpa using @le_lift_cof_iff.{u, u} α _ c

@[deprecated (since := "2026-02-18")] alias le_cof := le_cof_iff

Depends on / 依赖: le_lift_cof_iff
-/
theorem le_cof_iff {c : Cardinal} : c <= cof α ↔ forall s : Set α, IsCofinal s -> c <= #s := by
  simpa using @le_lift_cof_iff.{u, u} α _ c

@[deprecated (since := "2026-02-18")] alias le_cof := le_cof_iff

variable (α) in
/--
theorem `exists_cof_eq` / 定理 `exists_cof_eq`

English:
theorem exists_cof_eq
  statement: exists s : Set α, IsCofinal s ∧ #s = cof α
  proof: by
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set α // IsCofinal s} => #s
  exact ⟨s.1, s.2, hs⟩

@[deprecated (since := "2026-05-25")] alias cof_eq := exists_cof_eq

中文:
定理 存在_cof_eq
  结论: 存在 s : 集合 α, IsCofinal s ∧ #s = cof α
  证明: by
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set α // IsCofinal s} => #s
  exact ⟨s.1, s.2, hs⟩

@[deprecated (since := "2026-05-25")] alias cof_eq := exists_cof_eq

Depends on / 依赖: IsCofinal, ciInf_mem
-/
theorem exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s = cof α := by
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set α // IsCofinal s} => #s
  exact ⟨s.1, s.2, hs⟩

@[deprecated (since := "2026-05-25")] alias cof_eq := exists_cof_eq

variable (α) in
/--
theorem `cof_le_cardinalMk` / 定理 `cof_le_cardinalMk`

English:
theorem cof_le_cardinalMk
  statement: cof α <= #α
  proof: .trans_eq mk_univ cof_le .univ

中文:
定理 cof_le_cardinalMk
  结论: cof α <= #α
  证明: .trans_eq mk_univ cof_le .univ

Depends on / 依赖: cof_le, mk_univ, trans_eq
-/
theorem cof_le_cardinalMk : cof α <= #α :=
.trans_eq mk_univ cof_le .univ

/--
theorem `cof_eq_zero_iff` / 定理 `cof_eq_zero_iff`

English:
theorem cof_eq_zero_iff
  statement: cof α = 0 ↔ IsEmpty α
  proof: by
  refine ⟨fun _ => ?_, fun _ => by simp [cof]⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  simp_all [mk_eq_zero_iff, isCofinal_empty_iff]

@[simp]

中文:
定理 cof_eq_zero_iff
  结论: cof α = 0 ↔ 是空 α
  证明: by
  refine ⟨fun _ => ?_, fun _ => by simp [cof]⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  simp_all [mk_eq_zero_iff, isCofinal_empty_iff]

@[simp]

Depends on / 依赖: exists_cof_eq, isCofinal_empty_iff, mk_eq_zero_iff
-/
theorem cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α := by
  refine ⟨fun _ => ?_, fun _ => by simp [cof]⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  simp_all [mk_eq_zero_iff, isCofinal_empty_iff]

@[simp]
/--
theorem `cof_eq_zero` / 定理 `cof_eq_zero`

English:
theorem cof_eq_zero
  given: [h : IsEmpty α]
  statement: cof α = 0
  proof: cof_eq_zero_iff.2 h

中文:
定理 cof_eq_zero
  条件: [h : 是空 α]
  结论: cof α = 0
  证明: cof_eq_zero_iff.2 h

Depends on / 依赖: cof_eq_zero_iff
-/
theorem cof_eq_zero [h : IsEmpty α] : cof α = 0 :=
  cof_eq_zero_iff.2 h

/--
theorem `cof_ne_zero_iff` / 定理 `cof_ne_zero_iff`

English:
theorem cof_ne_zero_iff
  statement: cof α != 0 ↔ Nonempty α
  proof: by
  simpa using cof_eq_zero_iff.not

@[simp]

中文:
定理 cof_ne_zero_iff
  结论: cof α != 0 ↔ 非空 α
  证明: by
  simpa using cof_eq_zero_iff.not

@[simp]

Depends on / 依赖: cof_eq_zero_iff, cof_eq_zero_iff.not
-/
theorem cof_ne_zero_iff : cof α != 0 ↔ Nonempty α := by
  simpa using cof_eq_zero_iff.not

@[simp]
/--
theorem `cof_ne_zero` / 定理 `cof_ne_zero`

English:
theorem cof_ne_zero
  given: [h : Nonempty α]
  statement: cof α != 0
  proof: cof_ne_zero_iff.2 h

中文:
定理 cof_ne_zero
  条件: [h : 非空 α]
  结论: cof α != 0
  证明: cof_ne_zero_iff.2 h

Depends on / 依赖: cof_ne_zero_iff
-/
theorem cof_ne_zero [h : Nonempty α] : cof α != 0 :=
  cof_ne_zero_iff.2 h

/--
theorem `cof_eq_one_iff` / 定理 `cof_eq_one_iff`

English:
theorem cof_eq_one_iff
  statement: cof α = 1 ↔ exists x : α, IsTop x
  proof: by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
    rw [h]; rw [mk_set_eq_one_iff] at hs'
    obtain ⟨t, rfl⟩ := hs'
    use t
    rwa [isCofinal_singleton_iff] at hs
  · apply le_antisymm
    · apply (cof_le (s := {t}) _).trans_eq (mk_singleton _)
      rwa [isCofinal_singleton_iff]
    · rw [Cardinal.one_le_iff_ne_zero, cof_ne_zero_iff]
      use t

@[simp]

中文:
定理 cof_eq_one_iff
  结论: cof α = 1 ↔ 存在 x : α, IsTop x
  证明: by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
    rw [h]; rw [mk_set_eq_one_iff] at hs'
    obtain ⟨t, rfl⟩ := hs'
    use t
    rwa [isCofinal_singleton_iff] at hs
  · apply le_antisymm
    · apply (cof_le (s := {t}) _).trans_eq (mk_singleton _)
      rwa [isCofinal_singleton_iff]
    · rw [Cardinal.one_le_iff_ne_zero, cof_ne_zero_iff]
      use t

@[simp]

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, cof_le, cof_ne_zero_iff, exists_cof_eq, isCofinal_singleton_iff, le_antisymm, mk_set_eq_one_iff, mk_singleton, one_le_iff_ne_zero, trans_eq
-/
theorem cof_eq_one_iff : cof α = 1 ↔ exists x : α, IsTop x := by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
    rw [h]; rw [mk_set_eq_one_iff] at hs'
    obtain ⟨t, rfl⟩ := hs'
    use t
    rwa [isCofinal_singleton_iff] at hs
  · apply le_antisymm
    · apply (cof_le (s := {t}) _).trans_eq (mk_singleton _)
      rwa [isCofinal_singleton_iff]
    · rw [Cardinal.one_le_iff_ne_zero, cof_ne_zero_iff]
      use t

@[simp]
/--
theorem `cof_eq_one` / 定理 `cof_eq_one`

English:
theorem cof_eq_one
  given: [OrderTop α]
  statement: cof α = 1
  proof: cof_eq_one_iff.2 ⟨⊤, isTop_top⟩

中文:
定理 cof_eq_one
  条件: [有顶序 α]
  结论: cof α = 1
  证明: cof_eq_one_iff.2 ⟨⊤, isTop_top⟩

Depends on / 依赖: cof_eq_one_iff, isTop_top
-/
theorem cof_eq_one [OrderTop α] : cof α = 1 :=
  cof_eq_one_iff.2 ⟨⊤, isTop_top⟩

/--
theorem `cof_ne_one_iff` / 定理 `cof_ne_one_iff`

English:
theorem cof_ne_one_iff
  statement: cof α != 1 ↔ NoTopOrder α
  proof: by
  rw [← not_iff_not]; rw [not_not]; rw [noTopOrder_iff]; rw [cof_eq_one_iff]
  simp

@[simp]

中文:
定理 cof_ne_one_iff
  结论: cof α != 1 ↔ 无顶序 α
  证明: by
  rw [← not_iff_not]; rw [not_not]; rw [noTopOrder_iff]; rw [cof_eq_one_iff]
  simp

@[simp]

Depends on / 依赖: cof_eq_one_iff, noTopOrder_iff, not_iff_not, not_not
-/
theorem cof_ne_one_iff : cof α != 1 ↔ NoTopOrder α := by
  rw [← not_iff_not]; rw [not_not]; rw [noTopOrder_iff]; rw [cof_eq_one_iff]
  simp

@[simp]
/--
theorem `cof_ne_one` / 定理 `cof_ne_one`

English:
theorem cof_ne_one
  given: [h : NoTopOrder α]
  statement: cof α != 1
  proof: cof_ne_one_iff.2 h

中文:
定理 cof_ne_one
  条件: [h : 无顶序 α]
  结论: cof α != 1
  证明: cof_ne_one_iff.2 h

Depends on / 依赖: cof_ne_one_iff
-/
theorem cof_ne_one [h : NoTopOrder α] : cof α != 1 :=
  cof_ne_one_iff.2 h

/--
theorem `cof_le_one_iff` / 定理 `cof_le_one_iff`

English:
theorem cof_le_one_iff
  given: [Nonempty α]
  statement: cof α <= 1 ↔ exists x : α, IsTop x
  proof: by
  rw [le_iff_lt_or_eq]; rw [Cardinal.lt_one_iff]; rw [cof_eq_one_iff]
  simp

中文:
定理 cof_le_one_iff
  条件: [非空 α]
  结论: cof α <= 1 ↔ 存在 x : α, IsTop x
  证明: by
  rw [le_iff_lt_or_eq]; rw [Cardinal.lt_one_iff]; rw [cof_eq_one_iff]
  simp

Depends on / 依赖: Cardinal, Cardinal.lt_one_iff, cof_eq_one_iff, le_iff_lt_or_eq, lt_one_iff
-/
theorem cof_le_one_iff [Nonempty α] : cof α <= 1 ↔ exists x : α, IsTop x := by
  rw [le_iff_lt_or_eq]; rw [Cardinal.lt_one_iff]; rw [cof_eq_one_iff]
  simp

/--
theorem `one_lt_cof_iff` / 定理 `one_lt_cof_iff`

English:
theorem one_lt_cof_iff
  given: [Nonempty α]
  statement: 1 < cof α ↔ NoTopOrder α
  proof: by
  rw [← not_iff_not]; rw [not_lt]; rw [noTopOrder_iff]; rw [cof_le_one_iff]
  simp

@[simp]

中文:
定理 one_lt_cof_iff
  条件: [非空 α]
  结论: 1 < cof α ↔ 无顶序 α
  证明: by
  rw [← not_iff_not]; rw [not_lt]; rw [noTopOrder_iff]; rw [cof_le_one_iff]
  simp

@[simp]

Depends on / 依赖: cof_le_one_iff, noTopOrder_iff, not_iff_not, not_lt
-/
theorem one_lt_cof_iff [Nonempty α] : 1 < cof α ↔ NoTopOrder α := by
  rw [← not_iff_not]; rw [not_lt]; rw [noTopOrder_iff]; rw [cof_le_one_iff]
  simp

@[simp]
/--
theorem `one_lt_cof` / 定理 `one_lt_cof`

English:
theorem one_lt_cof
  given: [Nonempty α] [h : NoTopOrder α]
  statement: 1 < cof α
  proof: one_lt_cof_iff.2 h

中文:
定理 one_lt_cof
  条件: [非空 α] [h : 无顶序 α]
  结论: 1 < cof α
  证明: one_lt_cof_iff.2 h

Depends on / 依赖: one_lt_cof_iff
-/
theorem one_lt_cof [Nonempty α] [h : NoTopOrder α] : 1 < cof α :=
  one_lt_cof_iff.2 h

end Preorder

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/--
theorem `lift_cof_congr_of_strictMono` / 定理 `lift_cof_congr_of_strictMono`

English:
theorem lift_cof_congr_of_strictMono
  given: {f : α -> β} (hf : StrictMono f) (hf' : IsCofinal (range f))
  proof: by
  apply le_antisymm <;> rw [le_lift_cof_iff] <;> intro s hs
  · have H (x : s) : exists y : α, x <= f y := by simpa using hf' x
    choose g hg using H
    refine (lift_le.2 <| cof_le (s := range g) fun a => ?_).trans mk_range_le_lift
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' (f a)
    obtain ⟨c, hc, hc'⟩ := hs (f b)
    refine ⟨_, Set.mem_range_self ⟨c, hc⟩, ?_⟩
    rw [← hf.le_iff_le]
    exact hb.trans (hc'.trans (hg ⟨c, hc⟩))
  · exact (lift_le.2 <| cof_le (hs.image hf.monotone hf')).trans mk_image_le_lift

中文:
定理 lift_cof_congr_of_strictMono
  条件: {f : α -> β} (hf : 严格递增 f) (hf' : IsCofinal (range f))
  证明: by
  apply le_antisymm <;> rw [le_lift_cof_iff] <;> intro s hs
  · have H (x : s) : exists y : α, x <= f y := by simpa using hf' x
    choose g hg using H
    refine (lift_le.2 <| cof_le (s := range g) fun a => ?_).trans mk_range_le_lift
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' (f a)
    obtain ⟨c, hc, hc'⟩ := hs (f b)
    refine ⟨_, Set.mem_range_self ⟨c, hc⟩, ?_⟩
    rw [← hf.le_iff_le]
    exact hb.trans (hc'.trans (hg ⟨c, hc⟩))
  · exact (lift_le.2 <| cof_le (hs.image hf.monotone hf')).trans mk_image_le_lift

Depends on / 依赖: Set.mem_range_self, cof_le, hb.trans, hf.le_iff_le, hf.monotone, hs.image, le_antisymm, le_iff_le, le_lift_cof_iff, lift_le, mem_range_self, mk_image_le_lift, mk_range_le_lift, monotone
-/
theorem lift_cof_congr_of_strictMono {f : α -> β} (hf : StrictMono f) (hf' : IsCofinal (range f)) :
    lift.{v} (cof α) = lift.{u} (cof β) := by
  apply le_antisymm <;> rw [le_lift_cof_iff] <;> intro s hs
  · have H (x : s) : exists y : α, x <= f y := by simpa using hf' x
    choose g hg using H
    refine (lift_le.2 <| cof_le (s := range g) fun a => ?_).trans mk_range_le_lift
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' (f a)
    obtain ⟨c, hc, hc'⟩ := hs (f b)
    refine ⟨_, Set.mem_range_self ⟨c, hc⟩, ?_⟩
    rw [← hf.le_iff_le]
    exact hb.trans (hc'.trans (hg ⟨c, hc⟩))
  · exact (lift_le.2 <| cof_le (hs.image hf.monotone hf')).trans mk_image_le_lift

/--
theorem `cof_congr_of_strictMono` / 定理 `cof_congr_of_strictMono`

English:
theorem cof_congr_of_strictMono
  given: {f : α -> γ} (hf : StrictMono f) (hf' : IsCofinal (range f))
  proof: by
  simpa using lift_cof_congr_of_strictMono hf hf'

中文:
定理 cof_congr_of_strictMono
  条件: {f : α -> γ} (hf : 严格递增 f) (hf' : IsCofinal (range f))
  证明: by
  simpa using lift_cof_congr_of_strictMono hf hf'

Depends on / 依赖: lift_cof_congr_of_strictMono
-/
theorem cof_congr_of_strictMono {f : α -> γ} (hf : StrictMono f) (hf' : IsCofinal (range f)) :
    cof α = cof γ := by
  simpa using lift_cof_congr_of_strictMono hf hf'

/--
theorem `cof_eq_of_isCofinal` / 定理 `cof_eq_of_isCofinal`

English:
theorem cof_eq_of_isCofinal
  given: {s : Set α} (hs : IsCofinal s)
  statement: cof s = cof α
  proof: cof_congr_of_strictMono (Subtype.strictMono_coe _) (by simpa)

@[simp]

中文:
定理 cof_eq_of_isCofinal
  条件: {s : 集合 α} (hs : IsCofinal s)
  结论: cof s = cof α
  证明: cof_congr_of_strictMono (Subtype.strictMono_coe _) (by simpa)

@[simp]

Depends on / 依赖: Subtype, Subtype.strictMono_coe, cof_congr_of_strictMono, strictMono_coe
-/
theorem cof_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : cof s = cof α :=
  cof_congr_of_strictMono (Subtype.strictMono_coe _) (by simpa)

@[simp]
/--
theorem `cof_lt_aleph0_iff` / 定理 `cof_lt_aleph0_iff`

English:
theorem cof_lt_aleph0_iff
  statement: cof α < ℵ₀ ↔ cof α <= 1
  proof: by
  refine ⟨fun h => ?_, (lt_of_le_of_lt · one_lt_aleph0)⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  have hf : s.Finite := by
    rw [Set.Finite]; rw [← mk_lt_aleph0_iff]
    exact hs'.trans_lt h
  obtain ⟨t, ht, ht'⟩ := hf.exists_subsingleton_isCofinal hs
  apply (cof_le ht').trans
  simpa

@[simp]

中文:
定理 cof_lt_aleph0_iff
  结论: cof α < ℵ₀ ↔ cof α <= 1
  证明: by
  refine ⟨fun h => ?_, (lt_of_le_of_lt · one_lt_aleph0)⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  have hf : s.Finite := by
    rw [Set.Finite]; rw [← mk_lt_aleph0_iff]
    exact hs'.trans_lt h
  obtain ⟨t, ht, ht'⟩ := hf.exists_subsingleton_isCofinal hs
  apply (cof_le ht').trans
  simpa

@[simp]

Depends on / 依赖: Finite, Set.Finite, cof_le, exists_cof_eq, exists_subsingleton_isCofinal, hf.exists_subsingleton_isCofinal, lt_of_le_of_lt, mk_lt_aleph0_iff, one_lt_aleph0, s.Finite, trans_lt
-/
theorem cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α <= 1 := by
  refine ⟨fun h => ?_, (lt_of_le_of_lt · one_lt_aleph0)⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  have hf : s.Finite := by
    rw [Set.Finite]; rw [← mk_lt_aleph0_iff]
    exact hs'.trans_lt h
  obtain ⟨t, ht, ht'⟩ := hf.exists_subsingleton_isCofinal hs
  apply (cof_le ht').trans
  simpa

@[simp]
/--
theorem `aleph0_le_cof_iff` / 定理 `aleph0_le_cof_iff`

English:
theorem aleph0_le_cof_iff
  statement: ℵ₀ <= cof α ↔ 1 < cof α
  proof: by
  simp [← not_lt]

中文:
定理 aleph0_le_cof_iff
  结论: ℵ₀ <= cof α ↔ 1 < cof α
  证明: by
  simp [← not_lt]

Depends on / 依赖: not_lt
-/
theorem aleph0_le_cof_iff : ℵ₀ <= cof α ↔ 1 < cof α := by
  simp [← not_lt]

/--
theorem `aleph0_le_cof` / 定理 `aleph0_le_cof`

English:
theorem aleph0_le_cof
  given: [Nonempty α] [NoMaxOrder α]
  statement: ℵ₀ <= cof α
  proof: by
  simp

@[simp]

中文:
定理 aleph0_le_cof
  条件: [非空 α] [NoMax序 α]
  结论: ℵ₀ <= cof α
  证明: by
  simp

@[simp]
-/
theorem aleph0_le_cof [Nonempty α] [NoMaxOrder α] : ℵ₀ <= cof α := by
  simp

@[simp]
/--
theorem `cof_eq_aleph0` / 定理 `cof_eq_aleph0`

English:
theorem cof_eq_aleph0
  given: [NoMaxOrder α] [Nonempty α] [Countable α]
  statement: cof α = ℵ₀
  proof: ((cof_le_cardinalMk _).trans mk_le_aleph0).antisymm (by simp)

中文:
定理 cof_eq_aleph0
  条件: [NoMax序 α] [非空 α] [可数 α]
  结论: cof α = ℵ₀
  证明: ((cof_le_cardinalMk _).trans mk_le_aleph0).antisymm (by simp)

Depends on / 依赖: antisymm, cof_le_cardinalMk, mk_le_aleph0
-/
theorem cof_eq_aleph0 [NoMaxOrder α] [Nonempty α] [Countable α] : cof α = ℵ₀ :=
  ((cof_le_cardinalMk _).trans mk_le_aleph0).antisymm (by simp)

/--
theorem `cof_nat` / 定理 `cof_nat`

English:
theorem cof_nat
  statement: cof Nat = ℵ₀
  proof: by simp

中文:
定理 cof_nat
  结论: cof 自然数 = ℵ₀
  证明: by simp
-/
theorem cof_nat : cof Nat = ℵ₀ := by simp

end LinearOrder
end Order

section Congr
variable [Preorder α] [Preorder β] [Preorder γ]

/--
theorem `GaloisConnection.cof_le_lift` / 定理 `GaloisConnection.cof_le_lift`

English:
theorem GaloisConnection.cof_le_lift
  given: {f : β -> α} {g : α -> β} (h : GaloisConnection f g)
  proof: by
  rw [le_lift_cof_iff]
  exact fun s hs => (lift_le.2 <| cof_le (h.map_isCofinal hs)).trans mk_image_le_lift

中文:
定理 GaloisConnection.cof_le_lift
  条件: {f : β -> α} {g : α -> β} (h : GaloisConnection f g)
  证明: by
  rw [le_lift_cof_iff]
  exact fun s hs => (lift_le.2 <| cof_le (h.map_isCofinal hs)).trans mk_image_le_lift

Depends on / 依赖: cof_le, h.map_isCofinal, le_lift_cof_iff, lift_le, map_isCofinal, mk_image_le_lift
-/
theorem GaloisConnection.cof_le_lift {f : β -> α} {g : α -> β} (h : GaloisConnection f g) :
    Cardinal.lift.{u} (Order.cof β) <= Cardinal.lift.{v} (Order.cof α) := by
  rw [le_lift_cof_iff]
  exact fun s hs => (lift_le.2 <| cof_le (h.map_isCofinal hs)).trans mk_image_le_lift

/--
theorem `GaloisConnection.cof_le` / 定理 `GaloisConnection.cof_le`

English:
theorem GaloisConnection.cof_le
  given: {f : γ -> α} {g : α -> γ} (h : GaloisConnection f g)
  proof: by
  simpa using h.cof_le_lift

中文:
定理 GaloisConnection.cof_le
  条件: {f : γ -> α} {g : α -> γ} (h : GaloisConnection f g)
  证明: by
  simpa using h.cof_le_lift

Depends on / 依赖: cof_le_lift, h.cof_le_lift
-/
theorem GaloisConnection.cof_le {f : γ -> α} {g : α -> γ} (h : GaloisConnection f g) :
    Order.cof γ <= Order.cof α := by
  simpa using h.cof_le_lift

/--
theorem `OrderIso.lift_cof_congr` / 定理 `OrderIso.lift_cof_congr`

English:
theorem OrderIso.lift_cof_congr
  given: (f : α ≃o β)
  proof: f.to_galoisConnection.cof_le_lift.antisymm (f.symm.to_galoisConnection.cof_le_lift)

@[deprecated (since := "2026-03-20")] alias OrderIso.lift_cof_eq := OrderIso.lift_cof_congr

中文:
定理 OrderIso.lift_cof_congr
  条件: (f : α ≃o β)
  证明: f.to_galoisConnection.cof_le_lift.antisymm (f.symm.to_galoisConnection.cof_le_lift)

@[deprecated (since := "2026-03-20")] alias OrderIso.lift_cof_eq := OrderIso.lift_cof_congr

Depends on / 依赖: antisymm, cof_le_lift, f.symm.to_galoisConnection.cof_le_lift, f.to_galoisConnection.cof_le_lift.antisymm, to_galoisConnection
-/
theorem OrderIso.lift_cof_congr (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β) :=
  f.to_galoisConnection.cof_le_lift.antisymm (f.symm.to_galoisConnection.cof_le_lift)

@[deprecated (since := "2026-03-20")] alias OrderIso.lift_cof_eq := OrderIso.lift_cof_congr

/--
theorem `OrderIso.cof_congr` / 定理 `OrderIso.cof_congr`

English:
theorem OrderIso.cof_congr
  given: (f : α ≃o γ)
  statement: Order.cof α = Order.cof γ
  proof: by
  simpa using f.lift_cof_congr

@[deprecated (since := "2026-03-20")] alias OrderIso.cof_eq := OrderIso.cof_congr

@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq_lift := OrderIso.lift_cof_congr
@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq := OrderIso.cof_congr

中文:
定理 OrderIso.cof_congr
  条件: (f : α ≃o γ)
  结论: Order.cof α = Order.cof γ
  证明: by
  simpa using f.lift_cof_congr

@[deprecated (since := "2026-03-20")] alias OrderIso.cof_eq := OrderIso.cof_congr

@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq_lift := OrderIso.lift_cof_congr
@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq := OrderIso.cof_congr

Depends on / 依赖: f.lift_cof_congr, lift_cof_congr
-/
theorem OrderIso.cof_congr (f : α ≃o γ) : Order.cof α = Order.cof γ := by
  simpa using f.lift_cof_congr

@[deprecated (since := "2026-03-20")] alias OrderIso.cof_eq := OrderIso.cof_congr

@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq_lift := OrderIso.lift_cof_congr
@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq := OrderIso.cof_congr

end Congr

/--
theorem `isCofinal_of_isCofinal_sUnion` / 定理 `isCofinal_of_isCofinal_sUnion`

English:
theorem isCofinal_of_isCofinal_sUnion
  statement: {α : Type*} [LinearOrder α] {s : Set (Set α)}
  proof: by
  contrapose! h₂
  simp_rw [not_isCofinal_iff] at h₂
  choose f hf using h₂
  refine (cof_le (s := range fun x => f x.1 x.2) fun a => ?_).trans mk_range_le
  obtain ⟨b, ⟨t, ht, hb⟩, hab⟩ := h₁ a
  simpa using ⟨t, ht, hab.trans (hf t ht b hb).le⟩

中文:
定理 isCofinal_of_isCofinal_sUnion
  结论: {α : 类型} [线性序 α] {s : 集合 (集合 α)}
  证明: by
  contrapose! h₂
  simp_rw [not_isCofinal_iff] at h₂
  choose f hf using h₂
  refine (cof_le (s := range fun x => f x.1 x.2) fun a => ?_).trans mk_range_le
  obtain ⟨b, ⟨t, ht, hb⟩, hab⟩ := h₁ a
  simpa using ⟨t, ht, hab.trans (hf t ht b hb).le⟩

Depends on / 依赖: cof_le, contrapose, hab.trans, mk_range_le, not_isCofinal_iff, simp_rw
-/
theorem isCofinal_of_isCofinal_sUnion {α : Type*} [LinearOrder α] {s : Set (Set α)}
    (h₁ : IsCofinal (⋃₀ s)) (h₂ : #s < Order.cof α) : exists x in s, IsCofinal x := by
  contrapose! h₂
  simp_rw [not_isCofinal_iff] at h₂
  choose f hf using h₂
  refine (cof_le (s := range fun x => f x.1 x.2) fun a => ?_).trans mk_range_le
  obtain ⟨b, ⟨t, ht, hb⟩, hab⟩ := h₁ a
  simpa using ⟨t, ht, hab.trans (hf t ht b hb).le⟩

/--
theorem `isCofinal_of_isCofinal_iUnion` / 定理 `isCofinal_of_isCofinal_iUnion`

English:
theorem isCofinal_of_isCofinal_iUnion
  statement: {α : Type*} {ι} [LinearOrder α] {s : ι -> Set α}
  proof: by
  rw [← sUnion_range] at h₁
  obtain ⟨_, ⟨i, rfl⟩, h⟩ := isCofinal_of_isCofinal_sUnion h₁ (mk_range_le.trans_lt h₂)
  exact ⟨i, h⟩

中文:
定理 isCofinal_of_isCofinal_iUnion
  结论: {α : 类型} {ι} [线性序 α] {s : ι -> 集合 α}
  证明: by
  rw [← sUnion_range] at h₁
  obtain ⟨_, ⟨i, rfl⟩, h⟩ := isCofinal_of_isCofinal_sUnion h₁ (mk_range_le.trans_lt h₂)
  exact ⟨i, h⟩

Depends on / 依赖: isCofinal_of_isCofinal_sUnion, mk_range_le, mk_range_le.trans_lt, sUnion_range, trans_lt
-/
theorem isCofinal_of_isCofinal_iUnion {α : Type*} {ι} [LinearOrder α] {s : ι -> Set α}
    (h₁ : IsCofinal (⋃ i, s i)) (h₂ : #ι < Order.cof α) : exists i, IsCofinal (s i) := by
  rw [← sUnion_range] at h₁
  obtain ⟨_, ⟨i, rfl⟩, h⟩ := isCofinal_of_isCofinal_sUnion h₁ (mk_range_le.trans_lt h₂)
  exact ⟨i, h⟩
