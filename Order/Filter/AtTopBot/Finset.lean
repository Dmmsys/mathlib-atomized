/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Interval.Finset.Defs

/-!
# `Filter.atTop` and `Filter.atBot` filters and finite sets.
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

/--
theorem `tendsto_finset_range` / 定理 `tendsto_finset_range`

English:
theorem tendsto_finset_range
  statement: Tendsto Finset.range atTop atTop
  proof: Finset.range_mono.tendsto_atTop_atTop Finset.exists_nat_subset_range

中文:
定理 tendsto_finset_range
  结论: 收敛 有限集.range atTop atTop
  证明: Finset.range_mono.tendsto_atTop_atTop Finset.exists_nat_subset_range

Depends on / 依赖: Finset, Finset.exists_nat_subset_range, Finset.range_mono.tendsto_atTop_atTop, exists_nat_subset_range, range_mono, tendsto_atTop_atTop
-/
theorem tendsto_finset_range : Tendsto Finset.range atTop atTop :=
  Finset.range_mono.tendsto_atTop_atTop Finset.exists_nat_subset_range

/--
theorem `atTop_finset_eq_iInf` / 定理 `atTop_finset_eq_iInf`

English:
theorem atTop_finset_eq_iInf
  statement: (atTop : Filter (Finset α)) = ⨅ x : α, 𝓟 (Ici {x})
  proof: by
  refine le_antisymm (le_iInf fun i => le_principal_iff.2 <| mem_atTop ({i} : Finset α)) ?_
  refine
    le_iInf fun s =>
le_principal_iff.2 mem_iInf_of_iInter s.finite_toSet (fun i => mem_principal_self _) ?_
  simp only [subset_def, mem_iInter, SetCoe.forall, mem_Ici,
    Finset.mem_singleton, Finset.subset_iff, forall_eq]
  exact fun t => id

中文:
定理 atTop_finset_eq_iInf
  结论: (atTop : 滤子 (有限集 α)) = ⨅ x : α, 𝓟 (左闭右无界区间 {x})
  证明: by
  refine le_antisymm (le_iInf fun i => le_principal_iff.2 <| mem_atTop ({i} : Finset α)) ?_
  refine
    le_iInf fun s =>
le_principal_iff.2 mem_iInf_of_iInter s.finite_toSet (fun i => mem_principal_self _) ?_
  simp only [subset_def, mem_iInter, SetCoe.forall, mem_Ici,
    Finset.mem_singleton, Finset.subset_iff, forall_eq]
  exact fun t => id

Depends on / 依赖: Finset, Finset.mem_singleton, Finset.subset_iff, SetCoe, SetCoe.forall, finite_toSet, forall_eq, le_antisymm, le_iInf, le_principal_iff, mem_Ici, mem_atTop, mem_iInf_of_iInter, mem_iInter, mem_principal_self, mem_singleton, s.finite_toSet, subset_def, subset_iff
-/
theorem atTop_finset_eq_iInf : (atTop : Filter (Finset α)) = ⨅ x : α, 𝓟 (Ici {x}) := by
  refine le_antisymm (le_iInf fun i => le_principal_iff.2 <| mem_atTop ({i} : Finset α)) ?_
  refine
    le_iInf fun s =>
le_principal_iff.2 mem_iInf_of_iInter s.finite_toSet (fun i => mem_principal_self _) ?_
  simp only [subset_def, mem_iInter, SetCoe.forall, mem_Ici,
    Finset.mem_singleton, Finset.subset_iff, forall_eq]
  exact fun t => id

/--
theorem `tendsto_atTop_finset_of_monotone` / 定理 `tendsto_atTop_finset_of_monotone`

English:
theorem tendsto_atTop_finset_of_monotone
  statement: [Preorder β] {f : β -> Finset α} (h : Monotone f)
  proof: by
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro a
  rcases h' a with ⟨b, hb⟩
  exact (eventually_ge_atTop b).mono fun b' hb' => (Finset.singleton_subset_iff.2 hb).trans (h hb')

alias _root_.Monotone.tendsto_atTop_finset := tendsto_atTop_finset_of_monotone

中文:
定理 tendsto_atTop_finset_of_monotone
  结论: [预序 β] {f : β -> 有限集 α} (h : 递增 f)
  证明: by
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro a
  rcases h' a with ⟨b, hb⟩
  exact (eventually_ge_atTop b).mono fun b' hb' => (Finset.singleton_subset_iff.2 hb).trans (h hb')

alias _root_.Monotone.tendsto_atTop_finset := tendsto_atTop_finset_of_monotone

Depends on / 依赖: Finset, Finset.singleton_subset_iff, atTop_finset_eq_iInf, eventually_ge_atTop, singleton_subset_iff, tendsto_iInf, tendsto_principal
-/
theorem tendsto_atTop_finset_of_monotone [Preorder β] {f : β -> Finset α} (h : Monotone f)
    (h' : forall x : α, exists n, x in f n) : Tendsto f atTop atTop := by
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro a
  rcases h' a with ⟨b, hb⟩
  exact (eventually_ge_atTop b).mono fun b' hb' => (Finset.singleton_subset_iff.2 hb).trans (h hb')

alias _root_.Monotone.tendsto_atTop_finset := tendsto_atTop_finset_of_monotone

/--
theorem `tendsto_finset_image_atTop_atTop` / 定理 `tendsto_finset_image_atTop_atTop`

English:
theorem tendsto_finset_image_atTop_atTop
  statement: [DecidableEq β] {i : β -> γ} {j : γ -> β}
  proof: (Finset.image_mono j).tendsto_atTop_finset fun a =>
    ⟨{i a}, by simp only [Finset.image_singleton, h a, Finset.mem_singleton]⟩

中文:
定理 tendsto_finset_image_atTop_atTop
  结论: [DecidableEq β] {i : β -> γ} {j : γ -> β}
  证明: (Finset.image_mono j).tendsto_atTop_finset fun a =>
    ⟨{i a}, by simp only [Finset.image_singleton, h a, Finset.mem_singleton]⟩

Depends on / 依赖: Finset, Finset.image_mono, Finset.image_singleton, Finset.mem_singleton, image_mono, image_singleton, mem_singleton, tendsto_atTop_finset
-/
theorem tendsto_finset_image_atTop_atTop [DecidableEq β] {i : β -> γ} {j : γ -> β}
    (h : Function.LeftInverse j i) : Tendsto (Finset.image j) atTop atTop :=
  (Finset.image_mono j).tendsto_atTop_finset fun a =>
    ⟨{i a}, by simp only [Finset.image_singleton, h a, Finset.mem_singleton]⟩

/--
theorem `tendsto_finset_preimage_atTop_atTop` / 定理 `tendsto_finset_preimage_atTop_atTop`

English:
theorem tendsto_finset_preimage_atTop_atTop
  given: {f : α -> β} (hf : Function.Injective f)
  proof: (Finset.monotone_preimage hf).tendsto_atTop_finset fun x =>
⟨{f x}, Finset.mem_preimage.2 Finset.mem_singleton_self _⟩

中文:
定理 tendsto_finset_preimage_atTop_atTop
  条件: {f : α -> β} (hf : 函数.单射 f)
  证明: (Finset.monotone_preimage hf).tendsto_atTop_finset fun x =>
⟨{f x}, Finset.mem_preimage.2 Finset.mem_singleton_self _⟩

Depends on / 依赖: Finset, Finset.mem_preimage, Finset.mem_singleton_self, Finset.monotone_preimage, mem_preimage, mem_singleton_self, monotone_preimage, tendsto_atTop_finset
-/
theorem tendsto_finset_preimage_atTop_atTop {f : α -> β} (hf : Function.Injective f) :
    Tendsto (fun s : Finset β => s.preimage f (hf.injOn)) atTop atTop :=
  (Finset.monotone_preimage hf).tendsto_atTop_finset fun x =>
⟨{f x}, Finset.mem_preimage.2 Finset.mem_singleton_self _⟩

/--
lemma `tendsto_toLeft_atTop` / 引理 `tendsto_toLeft_atTop`

English:
lemma tendsto_toLeft_atTop
  proof: by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨t.disjSum ∅, fun b hb => H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

中文:
引理 tendsto_toLeft_atTop
  证明: by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨t.disjSum ∅, fun b hb => H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

Depends on / 依赖: Filter, Filter.mem_map, Finset, Finset.coe_subset, Set.mem_preimage, Set.subset_def, coe_subset, disjSum, mem_atTop_sets, mem_map, mem_preimage, subset_def, t.disjSum
-/
lemma tendsto_toLeft_atTop :
    Tendsto (Finset.toLeft (α := α) (β := β)) atTop atTop := by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨t.disjSum ∅, fun b hb => H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

/--
lemma `tendsto_toRight_atTop` / 引理 `tendsto_toRight_atTop`

English:
lemma tendsto_toRight_atTop
  proof: by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨.disjSum ∅ t, fun b hb => H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

中文:
引理 tendsto_toRight_atTop
  证明: by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨.disjSum ∅ t, fun b hb => H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

Depends on / 依赖: Filter, Filter.mem_map, Finset, Finset.coe_subset, Set.mem_preimage, Set.subset_def, coe_subset, disjSum, mem_atTop_sets, mem_map, mem_preimage, subset_def
-/
lemma tendsto_toRight_atTop :
    Tendsto (Finset.toRight (α := α) (β := β)) atTop atTop := by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨.disjSum ∅ t, fun b hb => H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

/--
theorem `tendsto_finset_powerset_atTop_atTop` / 定理 `tendsto_finset_powerset_atTop_atTop`

English:
theorem tendsto_finset_powerset_atTop_atTop
  statement: Tendsto (Finset.powerset (α := α)) atTop atTop
  proof: by
  classical
  refine tendsto_atTop_atTop.mpr fun t => ⟨t.sup id, fun _ hu _ hv => ?_⟩
exact Finset.mem_powerset.mpr (Finset.le_sup_of_le hv fun _ h => h).trans hu

中文:
定理 tendsto_finset_powerset_atTop_atTop
  结论: 收敛 (有限集.powerset (α := α)) atTop atTop
  证明: by
  classical
  refine tendsto_atTop_atTop.mpr fun t => ⟨t.sup id, fun _ hu _ hv => ?_⟩
exact Finset.mem_powerset.mpr (Finset.le_sup_of_le hv fun _ h => h).trans hu

Depends on / 依赖: Finset, Finset.le_sup_of_le, Finset.mem_powerset.mpr, classical, le_sup_of_le, mem_powerset, t.sup, tendsto_atTop_atTop, tendsto_atTop_atTop.mpr
-/
theorem tendsto_finset_powerset_atTop_atTop : Tendsto (Finset.powerset (α := α)) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.mpr fun t => ⟨t.sup id, fun _ hu _ hv => ?_⟩
exact Finset.mem_powerset.mpr (Finset.le_sup_of_le hv fun _ h => h).trans hu

/--
theorem `tendsto_finset_Iic_atTop_atTop` / 定理 `tendsto_finset_Iic_atTop_atTop`

English:
theorem tendsto_finset_Iic_atTop_atTop
  given: [Preorder α] [LocallyFiniteOrderBot α]
  proof: by
  rcases isEmpty_or_nonempty α with _ | _
  · exact tendsto_of_isEmpty
  by_cases h : IsDirectedOrder α
  · refine tendsto_atTop_atTop.mpr fun s => ?_
    obtain ⟨a, ha⟩ := Finset.exists_le s
    exact ⟨a, fun b hb c hc => by simpa using (ha c hc).trans hb⟩
  · obtain h := Filter.atTop_neBot_iff.not.mpr (fun h' => h h'.2)
    simp [not_ne_iff.mp <| Filter.neBot_iff.not.mp h]

中文:
定理 tendsto_finset_Iic_atTop_atTop
  条件: [预序 α] [LocallyFiniteOrderBot α]
  证明: by
  rcases isEmpty_or_nonempty α with _ | _
  · exact tendsto_of_isEmpty
  by_cases h : IsDirectedOrder α
  · refine tendsto_atTop_atTop.mpr fun s => ?_
    obtain ⟨a, ha⟩ := Finset.exists_le s
    exact ⟨a, fun b hb c hc => by simpa using (ha c hc).trans hb⟩
  · obtain h := Filter.atTop_neBot_iff.not.mpr (fun h' => h h'.2)
    simp [not_ne_iff.mp <| Filter.neBot_iff.not.mp h]

Depends on / 依赖: Filter, Filter.atTop_neBot_iff.not.mpr, Filter.neBot_iff.not.mp, Finset, Finset.exists_le, IsDirectedOrder, atTop_neBot_iff, exists_le, isEmpty_or_nonempty, neBot_iff, not_ne_iff, not_ne_iff.mp, tendsto_atTop_atTop, tendsto_atTop_atTop.mpr, tendsto_of_isEmpty
-/
theorem tendsto_finset_Iic_atTop_atTop [Preorder α] [LocallyFiniteOrderBot α] :
    Tendsto (Finset.Iic (α := α)) atTop atTop := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact tendsto_of_isEmpty
  by_cases h : IsDirectedOrder α
  · refine tendsto_atTop_atTop.mpr fun s => ?_
    obtain ⟨a, ha⟩ := Finset.exists_le s
    exact ⟨a, fun b hb c hc => by simpa using (ha c hc).trans hb⟩
  · obtain h := Filter.atTop_neBot_iff.not.mpr (fun h' => h h'.2)
    simp [not_ne_iff.mp <| Filter.neBot_iff.not.mp h]

/--
theorem `tendsto_finset_Ici_atBot_atTop` / 定理 `tendsto_finset_Ici_atBot_atTop`

English:
theorem tendsto_finset_Ici_atBot_atTop
  given: [Preorder α] [LocallyFiniteOrderTop α]
  proof: tendsto_finset_Iic_atTop_atTop (α := αᵒᵈ)

中文:
定理 tendsto_finset_Ici_atBot_atTop
  条件: [预序 α] [LocallyFiniteOrderTop α]
  证明: tendsto_finset_Iic_atTop_atTop (α := αᵒᵈ)
-/
theorem tendsto_finset_Ici_atBot_atTop [Preorder α] [LocallyFiniteOrderTop α] :
    Tendsto (Finset.Ici (α := α)) atBot atTop :=
  tendsto_finset_Iic_atTop_atTop (α := αᵒᵈ)

section Card

/--
lemma `eventually_finset_atTop_subset` / 引理 `eventually_finset_atTop_subset`

English:
lemma eventually_finset_atTop_subset
  given: (i : Finset α)
  statement: forallᶠ s : Finset α in atTop, i subseteq s
  proof: eventually_ge_atTop _

中文:
引理 eventually_finset_atTop_subset
  条件: (i : 有限集 α)
  结论: 对任意ᶠ s : 有限集 α in atTop, i subseteq s
  证明: eventually_ge_atTop _

Depends on / 依赖: eventually_ge_atTop
-/
lemma eventually_finset_atTop_subset (i : Finset α) : forallᶠ s : Finset α in atTop, i subseteq s :=
  eventually_ge_atTop _

/--
lemma `eventually_finset_mem_atTop` / 引理 `eventually_finset_mem_atTop`

English:
lemma eventually_finset_mem_atTop
  given: (i : α)
  statement: forallᶠ s : Finset α in atTop, i in s
  proof: by
  simpa using eventually_finset_atTop_subset {i}

中文:
引理 eventually_finset_mem_atTop
  条件: (i : α)
  结论: 对任意ᶠ s : 有限集 α in atTop, i in s
  证明: by
  simpa using eventually_finset_atTop_subset {i}

Depends on / 依赖: eventually_finset_atTop_subset
-/
lemma eventually_finset_mem_atTop (i : α) : forallᶠ s : Finset α in atTop, i in s := by
  simpa using eventually_finset_atTop_subset {i}

/--
lemma `map_card_atTop` / 引理 `map_card_atTop`

English:
lemma map_card_atTop
  given: [Infinite α]
  proof: by
  rw [map_atTop_eq]; rw [atTop]
  refine Function.Surjective.iInf_congr Finset.card Finset.exists_card_eq fun s => congr(𝓟 $(?_))
  ext
  refine ⟨Infinite.exists_superset_card_eq _ _, ?_⟩
  aesop (add safe apply Finset.card_le_card)

中文:
引理 map_card_atTop
  条件: [无限 α]
  证明: by
  rw [map_atTop_eq]; rw [atTop]
  refine Function.Surjective.iInf_congr Finset.card Finset.exists_card_eq fun s => congr(𝓟 $(?_))
  ext
  refine ⟨Infinite.exists_superset_card_eq _ _, ?_⟩
  aesop (add safe apply Finset.card_le_card)

Depends on / 依赖: Finset, Finset.card, Finset.card_le_card, Finset.exists_card_eq, Function, Function.Surjective.iInf_congr, Infinite, Infinite.exists_superset_card_eq, Surjective, card_le_card, exists_card_eq, exists_superset_card_eq, iInf_congr, map_atTop_eq
-/
lemma map_card_atTop [Infinite α] :
    map (Finset.card (α := α)) atTop = atTop := by
  rw [map_atTop_eq]; rw [atTop]
  refine Function.Surjective.iInf_congr Finset.card Finset.exists_card_eq fun s => congr(𝓟 $(?_))
  ext
  refine ⟨Infinite.exists_superset_card_eq _ _, ?_⟩
  aesop (add safe apply Finset.card_le_card)

/--
lemma `map_card_atTop_of_fintype` / 引理 `map_card_atTop_of_fintype`

English:
lemma map_card_atTop_of_fintype
  given: [Fintype α]
  proof: by
  simp [OrderTop.atTop_eq]

中文:
引理 map_card_atTop_of_fintype
  条件: [有限类型 α]
  证明: by
  simp [OrderTop.atTop_eq]

Depends on / 依赖: OrderTop, OrderTop.atTop_eq, atTop_eq
-/
lemma map_card_atTop_of_fintype [Fintype α] :
    map (Finset.card : Finset α -> Nat) atTop = pure (Fintype.card α) := by
  simp [OrderTop.atTop_eq]

/--
lemma `tendsto_card_atTop_atTop` / 引理 `tendsto_card_atTop_atTop`

English:
lemma tendsto_card_atTop_atTop
  given: [Infinite α]
  proof: by
  rw [Tendsto]; rw [map_card_atTop]

中文:
引理 tendsto_card_atTop_atTop
  条件: [无限 α]
  证明: by
  rw [Tendsto]; rw [map_card_atTop]

Depends on / 依赖: Tendsto, map_card_atTop
-/
lemma tendsto_card_atTop_atTop [Infinite α] :
    Tendsto (Finset.card (α := α)) atTop atTop := by
  rw [Tendsto]; rw [map_card_atTop]

/--
lemma `tendsto_card_atTop_pure_of_fintype` / 引理 `tendsto_card_atTop_pure_of_fintype`

English:
lemma tendsto_card_atTop_pure_of_fintype
  given: [Fintype α]
  proof: by
  rw [Tendsto]; rw [map_card_atTop_of_fintype]

中文:
引理 tendsto_card_atTop_pure_of_fintype
  条件: [有限类型 α]
  证明: by
  rw [Tendsto]; rw [map_card_atTop_of_fintype]

Depends on / 依赖: Tendsto, map_card_atTop_of_fintype
-/
lemma tendsto_card_atTop_pure_of_fintype [Fintype α] :
    Tendsto (Finset.card : Finset α -> Nat) atTop (pure (Fintype.card α)) := by
  rw [Tendsto]; rw [map_card_atTop_of_fintype]

/--
lemma `tendsto_comp_card_atTop_iff` / 引理 `tendsto_comp_card_atTop_iff`

English:
lemma tendsto_comp_card_atTop_iff
  given: [Infinite α] {f : Nat -> β} {l : Filter β}
  proof: by
  rw [← map_card_atTop (α := α)]; rw [tendsto_map'_iff]
  rfl

中文:
引理 tendsto_comp_card_atTop_iff
  条件: [无限 α] {f : 自然数 -> β} {l : 滤子 β}
  证明: by
  rw [← map_card_atTop (α := α)]; rw [tendsto_map'_iff]
  rfl

Depends on / 依赖: _iff, map_card_atTop, tendsto_map
-/
lemma tendsto_comp_card_atTop_iff [Infinite α] {f : Nat -> β} {l : Filter β} :
    Tendsto (fun s : Finset α => f s.card) atTop l ↔ Tendsto f atTop l := by
  rw [← map_card_atTop (α := α)]; rw [tendsto_map'_iff]
  rfl

/--
lemma `tendsto_comp_card_atTop_iff_of_fintype` / 引理 `tendsto_comp_card_atTop_iff_of_fintype`

English:
lemma tendsto_comp_card_atTop_iff_of_fintype
  given: [Fintype α] {f : Nat -> β} {l : Filter β}
  proof: by
  rw [← map_card_atTop_of_fintype]; rw [tendsto_map'_iff]
  rfl

中文:
引理 tendsto_comp_card_atTop_iff_of_fintype
  条件: [有限类型 α] {f : 自然数 -> β} {l : 滤子 β}
  证明: by
  rw [← map_card_atTop_of_fintype]; rw [tendsto_map'_iff]
  rfl

Depends on / 依赖: _iff, map_card_atTop_of_fintype, tendsto_map
-/
lemma tendsto_comp_card_atTop_iff_of_fintype [Fintype α] {f : Nat -> β} {l : Filter β} :
    Tendsto (fun s : Finset α => f s.card) atTop l ↔ Tendsto f (pure (Fintype.card α)) l := by
  rw [← map_card_atTop_of_fintype]; rw [tendsto_map'_iff]
  rfl

end Card

end Filter
