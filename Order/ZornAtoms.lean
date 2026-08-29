/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Order.Atoms

/-!
# Zorn lemma for (co)atoms

In this file we use Zorn's lemma to prove that a partial order is atomic if every nonempty chain
`c`, `⊥ ∉ c`, has a lower bound not equal to `⊥`. We also prove the order dual version of this
statement.
-/

public section


open Set

/--
theorem `IsCoatomic.of_isChain_bounded` / 定理 `IsCoatomic.of_isChain_bounded`

English:
theorem IsCoatomic.of_isChain_bounded
  statement: {α : Type*} [PartialOrder α] [OrderTop α]
  proof: by
  refine ⟨fun x => le_top.eq_or_lt.imp_right fun hx => ?_⟩
  have := zorn_le_nonempty₀ (Ico x ⊤) (fun c hxc hc y hy => ?_) x (left_mem_Ico.2 hx)
  · obtain ⟨y, hxy, hmax⟩ := this
    refine ⟨y, ⟨hmax.prop.2.ne, fun z hyz => le_top.eq_or_lt.resolve_right fun hz => ?_⟩, hxy⟩
exact hyz.ne hmax.eq_of

中文:
定理 IsCoatomic.of_isChain_bounded
  结论: {α : 类型} [PartialOrder α] [OrderTop α]
  证明: by
  refine ⟨fun x => le_top.eq_or_lt.imp_right fun hx => ?_⟩
  have := zorn_le_nonempty₀ (Ico x ⊤) (fun c hxc hc y hy => ?_) x (left_mem_Ico.2 hx)
  · obtain ⟨y, hxy, hmax⟩ := this
    refine ⟨y, ⟨hmax.prop.2.ne, fun z hyz => le_top.eq_or_lt.resolve_right fun hz => ?_⟩, hxy⟩
exact hyz.ne hmax.eq_of

Depends on / 依赖: eq_of_le, eq_or_lt, hmax.eq_of_le, hmax.prop, hxy.trans, hyz.le, hyz.ne, hz.lt_top, imp_right, le_top, le_top.eq_or_lt.imp_right, le_top.eq_or_lt.resolve_right, le_trans, left_mem_Ico, lt_top, resolve_right
-/
theorem IsCoatomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderTop α]
    (h : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> ⊤ ∉ c -> exists x != ⊤, x in upperBounds c) :
    IsCoatomic α := by
  refine ⟨fun x => le_top.eq_or_lt.imp_right fun hx => ?_⟩
  have := zorn_le_nonempty₀ (Ico x ⊤) (fun c hxc hc y hy => ?_) x (left_mem_Ico.2 hx)
  · obtain ⟨y, hxy, hmax⟩ := this
    refine ⟨y, ⟨hmax.prop.2.ne, fun z hyz => le_top.eq_or_lt.resolve_right fun hz => ?_⟩, hxy⟩
exact hyz.ne hmax.eq_of_le ⟨hxy.trans hyz.le, hz⟩ hyz.le
  rcases h c hc ⟨y, hy⟩ fun h => (hxc h).2.ne rfl with ⟨z, hz, hcz⟩
  exact ⟨z, ⟨le_trans (hxc hy).1 (hcz hy), hz.lt_top⟩, hcz⟩

/--
theorem `IsAtomic.of_isChain_bounded` / 定理 `IsAtomic.of_isChain_bounded`

English:
theorem IsAtomic.of_isChain_bounded
  statement: {α : Type*} [PartialOrder α] [OrderBot α]
  proof: isCoatomic_dual_iff_isAtomic.mp IsCoatomic.of_isChain_bounded fun c hc => h c hc.symm

中文:
定理 IsAtomic.of_isChain_bounded
  结论: {α : 类型} [PartialOrder α] [OrderBot α]
  证明: isCoatomic_dual_iff_isAtomic.mp IsCoatomic.of_isChain_bounded fun c hc => h c hc.symm

Depends on / 依赖: IsCoatomic, IsCoatomic.of_isChain_bounded, hc.symm, isCoatomic_dual_iff_isAtomic, isCoatomic_dual_iff_isAtomic.mp, of_isChain_bounded
-/
theorem IsAtomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderBot α]
    (h :
      forall c : Set α,
        IsChain (· <= ·) c -> c.Nonempty -> ⊥ ∉ c -> exists x != ⊥, x in lowerBounds c) :
    IsAtomic α :=
isCoatomic_dual_iff_isAtomic.mp IsCoatomic.of_isChain_bounded fun c hc => h c hc.symm
