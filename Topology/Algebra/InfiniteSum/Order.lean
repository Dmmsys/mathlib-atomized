/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Infinite sum or product in an order

This file provides lemmas about the interaction of infinite sums and products and order operations.
-/

public section

open Finset Filter Function

variable {ι κ α : Type*} {L : SummationFilter ι}

section Preorder

variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι -> α}

@[to_additive]
/--
lemma `hasProd_le_of_prod_le` / 引理 `hasProd_le_of_prod_le`

English:
lemma hasProd_le_of_prod_le
  statement: [ClosedIicTopology α] [L.NeBot]
  proof: le_of_tendsto' hf h

@[to_additive]

中文:
引理 hasProd_le_of_prod_le
  结论: [ClosedIicTopology α] [L.NeBot]
  证明: le_of_tendsto' hf h

@[to_additive]

Depends on / 依赖: le_of_tendsto
-/
lemma hasProd_le_of_prod_le [ClosedIicTopology α] [L.NeBot]
    (hf : HasProd f a L) (h : forall s, ∏ i in s, f i <= c) : a <= c :=
  le_of_tendsto' hf h

@[to_additive]
/--
theorem `le_hasProd_of_le_prod` / 定理 `le_hasProd_of_le_prod`

English:
theorem le_hasProd_of_le_prod
  statement: [ClosedIciTopology α] [L.NeBot]
  proof: ge_of_tendsto' hf h

@[to_additive]

中文:
定理 le_hasProd_of_le_prod
  结论: [ClosedIciTopology α] [L.NeBot]
  证明: ge_of_tendsto' hf h

@[to_additive]

Depends on / 依赖: ge_of_tendsto
-/
theorem le_hasProd_of_le_prod [ClosedIciTopology α] [L.NeBot]
    (hf : HasProd f a L) (h : forall s, c <= ∏ i in s, f i) : c <= a :=
  ge_of_tendsto' hf h

@[to_additive]
/--
theorem `Multipliable.tprod_le_of_prod_range_le` / 定理 `Multipliable.tprod_le_of_prod_range_le`

English:
theorem Multipliable.tprod_le_of_prod_range_le
  statement: [ClosedIicTopology α] {f : Nat -> α}
  proof: le_of_tendsto' hf.hasProd.tendsto_prod_nat h

中文:
定理 Multipliable.tprod_le_of_prod_range_le
  结论: [ClosedIicTopology α] {f : 自然数 -> α}
  证明: le_of_tendsto' hf.hasProd.tendsto_prod_nat h
-/
protected theorem Multipliable.tprod_le_of_prod_range_le [ClosedIicTopology α] {f : Nat -> α}
    (hf : Multipliable f) (h : forall n, ∏ i in range n, f i <= c) : ∏' n, f n <= c :=
  le_of_tendsto' hf.hasProd.tendsto_prod_nat h

end Preorder

section OrderedCommMonoid

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [OrderClosedTopology α] {f g : ι -> α}
  {a a₁ a₂ : α}

@[to_additive]
/--
theorem `hasProd_le` / 定理 `hasProd_le`

English:
theorem hasProd_le
  given: (h : forall i, f i <= g i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) [L.NeBot]
  proof: le_of_tendsto_of_tendsto' hf hg fun _ => prod_le_prod' fun i _ => h i

@[to_additive]

中文:
定理 hasProd_le
  条件: (h : 对任意 i, f i <= g i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) [L.NeBot]
  证明: le_of_tendsto_of_tendsto' hf hg fun _ => prod_le_prod' fun i _ => h i

@[to_additive]

Depends on / 依赖: le_of_tendsto_of_tendsto, prod_le_prod
-/
theorem hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) [L.NeBot] :
    a₁ <= a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ => prod_le_prod' fun i _ => h i

@[to_additive]
/--
theorem `hasProd_mono` / 定理 `hasProd_mono`

English:
theorem hasProd_mono
  given: (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) (h : f <= g) [L.NeBot]
  statement: a₁ <= a₂
  proof: hasProd_le h hf hg

@[to_additive]

中文:
定理 hasProd_mono
  条件: (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) (h : f <= g) [L.NeBot]
  结论: a₁ <= a₂
  证明: hasProd_le h hf hg

@[to_additive]

Depends on / 依赖: hasProd_le
-/
theorem hasProd_mono (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) (h : f <= g) [L.NeBot] : a₁ <= a₂ :=
  hasProd_le h hf hg

@[to_additive]
/--
theorem `hasProd_le_inj` / 定理 `hasProd_le_inj`

English:
theorem hasProd_le_inj
  statement: {g : κ -> α} (e : ι -> κ) (he : Injective e)
  proof: by
  rw [← hasProd_extend_one he] at hf
  refine hasProd_le (fun c => ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c in Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h

@[to_additive]

中文:
定理 hasProd_le_inj
  结论: {g : κ -> α} (e : ι -> κ) (he : Injective e)
  证明: by
  rw [← hasProd_extend_one he] at hf
  refine hasProd_le (fun c => ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c in Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h

@[to_additive]

Depends on / 依赖: Set.range, extend_apply, hasProd_extend_one, hasProd_le, he.extend_apply
-/
theorem hasProd_le_inj {g : κ -> α} (e : ι -> κ) (he : Injective e)
    (hs : forall c, c ∉ Set.range e -> 1 <= g c) (h : forall i, f i <= g (e i)) (hf : HasProd f a₁)
    (hg : HasProd g a₂) : a₁ <= a₂ := by
  rw [← hasProd_extend_one he] at hf
  refine hasProd_le (fun c => ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c in Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h

@[to_additive]
/--
theorem `Multipliable.tprod_le_tprod_of_inj` / 定理 `Multipliable.tprod_le_tprod_of_inj`

English:
theorem Multipliable.tprod_le_tprod_of_inj
  statement: {g : κ -> α} (e : ι -> κ) (he : Injective e)
  proof: hasProd_le_inj _ he hs h hf.hasProd hg.hasProd

@[to_additive]

中文:
定理 Multipliable.tprod_le_tprod_of_inj
  结论: {g : κ -> α} (e : ι -> κ) (he : Injective e)
  证明: hasProd_le_inj _ he hs h hf.hasProd hg.hasProd

@[to_additive]
-/
protected theorem Multipliable.tprod_le_tprod_of_inj {g : κ -> α} (e : ι -> κ) (he : Injective e)
    (hs : forall c, c ∉ Set.range e -> 1 <= g c) (h : forall i, f i <= g (e i)) (hf : Multipliable f)
    (hg : Multipliable g) : tprod f <= tprod g :=
  hasProd_le_inj _ he hs h hf.hasProd hg.hasProd

@[to_additive]
/--
lemma `Multipliable.tprod_subtype_le` / 引理 `Multipliable.tprod_subtype_le`

English:
lemma Multipliable.tprod_subtype_le
  statement: {κ γ : Type*} [CommGroup γ] [PartialOrder γ]
  proof: by
  apply Multipliable.tprod_le_tprod_of_inj _
    (Subtype.coe_injective)
    (by simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, h, implies_true])
    (by simp only [le_refl, implies_true])
    (by apply hf.subtype)
  apply hf

@[to_additive]

中文:
引理 Multipliable.tprod_subtype_le
  结论: {κ γ : 类型} [CommGroup γ] [PartialOrder γ]
  证明: by
  apply Multipliable.tprod_le_tprod_of_inj _
    (Subtype.coe_injective)
    (by simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, h, implies_true])
    (by simp only [le_refl, implies_true])
    (by apply hf.subtype)
  apply hf

@[to_additive]
-/
protected lemma Multipliable.tprod_subtype_le {κ γ : Type*} [CommGroup γ] [PartialOrder γ]
    [IsOrderedMonoid γ] [UniformSpace γ] [IsUniformGroup γ] [OrderClosedTopology γ]
    [CompleteSpace γ] (f : κ -> γ) (β : Set κ) (h : forall a : κ, 1 <= f a) (hf : Multipliable f) :
    (∏' (b : β), f b) <= (∏' (a : κ), f a) := by
  apply Multipliable.tprod_le_tprod_of_inj _
    (Subtype.coe_injective)
    (by simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, h, implies_true])
    (by simp only [le_refl, implies_true])
    (by apply hf.subtype)
  apply hf

@[to_additive]
/--
theorem `prod_le_hasProd` / 定理 `prod_le_hasProd`

English:
theorem prod_le_hasProd
  statement: [L.NeBot] [L.LeAtTop] (s : Finset ι) (hs : forall i, i ∉ s -> 1 <= f i)
  proof: by
refine ge_of_tendsto hf .filter_mono L.le_atTop eventually_atTop.2 ?_
  exact ⟨s, fun _t hst => prod_le_prod_of_subset_of_one_le' hst fun i _ hbs => hs i hbs⟩

@[to_additive]

中文:
定理 prod_le_hasProd
  结论: [L.NeBot] [L.LeAtTop] (s : Finset ι) (hs : 对任意 i, i ∉ s -> 1 <= f i)
  证明: by
refine ge_of_tendsto hf .filter_mono L.le_atTop eventually_atTop.2 ?_
  exact ⟨s, fun _t hst => prod_le_prod_of_subset_of_one_le' hst fun i _ hbs => hs i hbs⟩

@[to_additive]

Depends on / 依赖: L.le_atTop, eventually_atTop, filter_mono, ge_of_tendsto, le_atTop, prod_le_prod_of_subset_of_one_le
-/
theorem prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (hs : forall i, i ∉ s -> 1 <= f i)
    (hf : HasProd f a L) : ∏ i in s, f i <= a := by
refine ge_of_tendsto hf .filter_mono L.le_atTop eventually_atTop.2 ?_
  exact ⟨s, fun _t hst => prod_le_prod_of_subset_of_one_le' hst fun i _ hbs => hs i hbs⟩

@[to_additive]
/--
theorem `isLUB_hasProd` / 定理 `isLUB_hasProd`

English:
theorem isLUB_hasProd
  given: (h : forall i, 1 <= f i) (hf : HasProd f a)
  proof: by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]

中文:
定理 isLUB_hasProd
  条件: (h : 对任意 i, 1 <= f i) (hf : HasProd f a)
  证明: by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_mono_set_of_one_le, isLUB_of_tendsto_atTop, prod_mono_set_of_one_le
-/
theorem isLUB_hasProd (h : forall i, 1 <= f i) (hf : HasProd f a) :
    IsLUB (Set.range fun s => ∏ i in s, f i) a := by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
/--
theorem `le_hasProd` / 定理 `le_hasProd`

English:
theorem le_hasProd
  given: [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι) (hb : forall j, j != i -> 1 <= f j)
  proof: calc
    f i = ∏ i in {i}, f i := by rw [prod_singleton]
    _ <= a := prod_le_hasProd _ (by simpa) hf

@[to_additive]

中文:
定理 le_hasProd
  条件: [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι) (hb : 对任意 j, j != i -> 1 <= f j)
  证明: calc
    f i = ∏ i in {i}, f i := by rw [prod_singleton]
    _ <= a := prod_le_hasProd _ (by simpa) hf

@[to_additive]

Depends on / 依赖: prod_le_hasProd, prod_singleton
-/
theorem le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι) (hb : forall j, j != i -> 1 <= f j) :
    f i <= a :=
  calc
    f i = ∏ i in {i}, f i := by rw [prod_singleton]
    _ <= a := prod_le_hasProd _ (by simpa) hf

@[to_additive]
/--
theorem `lt_hasProd` / 定理 `lt_hasProd`

English:
theorem lt_hasProd
  statement: [L.NeBot] [L.LeAtTop] [MulRightStrictMono α] (hf : HasProd f a L) (i : ι)
  proof: by
  classical
  calc
    f i < f j * f i := lt_mul_of_one_lt_left' (f i) hj
    _ = ∏ k in {j, i}, f k := by rw [Finset.prod_pair hij]
    _ <= a := prod_le_hasProd _ (fun k hk => hi k (hk ∘ mem_insert_of_mem ∘ mem_singleton.mpr)) hf

@[to_additive]

中文:
定理 lt_hasProd
  结论: [L.NeBot] [L.LeAtTop] [MulRightStrictMono α] (hf : HasProd f a L) (i : ι)
  证明: by
  classical
  calc
    f i < f j * f i := lt_mul_of_one_lt_left' (f i) hj
    _ = ∏ k in {j, i}, f k := by rw [Finset.prod_pair hij]
    _ <= a := prod_le_hasProd _ (fun k hk => hi k (hk ∘ mem_insert_of_mem ∘ mem_singleton.mpr)) hf

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_pair, classical, lt_mul_of_one_lt_left, mem_insert_of_mem, mem_singleton, mem_singleton.mpr, prod_le_hasProd, prod_pair
-/
theorem lt_hasProd [L.NeBot] [L.LeAtTop] [MulRightStrictMono α] (hf : HasProd f a L) (i : ι)
    (hi : forall (j : ι), j != i -> 1 <= f j) (j : ι) (hij : j != i) (hj : 1 < f j) :
    f i < a := by
  classical
  calc
    f i < f j * f i := lt_mul_of_one_lt_left' (f i) hj
    _ = ∏ k in {j, i}, f k := by rw [Finset.prod_pair hij]
    _ <= a := prod_le_hasProd _ (fun k hk => hi k (hk ∘ mem_insert_of_mem ∘ mem_singleton.mpr)) hf

@[to_additive]
/--
theorem `Multipliable.prod_le_tprod` / 定理 `Multipliable.prod_le_tprod`

English:
theorem Multipliable.prod_le_tprod
  statement: [L.NeBot] [L.LeAtTop] {f : ι -> α} (s : Finset ι)
  proof: prod_le_hasProd s hs hf.hasProd

@[to_additive]

中文:
定理 Multipliable.prod_le_tprod
  结论: [L.NeBot] [L.LeAtTop] {f : ι -> α} (s : Finset ι)
  证明: prod_le_hasProd s hs hf.hasProd

@[to_additive]
-/
protected theorem Multipliable.prod_le_tprod [L.NeBot] [L.LeAtTop] {f : ι -> α} (s : Finset ι)
    (hs : forall i, i ∉ s -> 1 <= f i) (hf : Multipliable f L) :
    ∏ i in s, f i <= ∏'[L] i, f i :=
  prod_le_hasProd s hs hf.hasProd

@[to_additive]
/--
theorem `Multipliable.le_tprod` / 定理 `Multipliable.le_tprod`

English:
theorem Multipliable.le_tprod
  statement: [L.NeBot] [L.LeAtTop] (hf : Multipliable f L) (i : ι)
  proof: le_hasProd hf.hasProd i hb

@[to_additive (attr := gcongr)]

中文:
定理 Multipliable.le_tprod
  结论: [L.NeBot] [L.LeAtTop] (hf : Multipliable f L) (i : ι)
  证明: le_hasProd hf.hasProd i hb

@[to_additive (attr := gcongr)]
-/
protected theorem Multipliable.le_tprod [L.NeBot] [L.LeAtTop] (hf : Multipliable f L) (i : ι)
    (hb : forall j != i, 1 <= f j) : f i <= ∏'[L] i, f i :=
  le_hasProd hf.hasProd i hb

@[to_additive (attr := gcongr)]
/--
theorem `Multipliable.tprod_le_tprod` / 定理 `Multipliable.tprod_le_tprod`

English:
theorem Multipliable.tprod_le_tprod
  statement: [L.NeBot] (h : forall i, f i <= g i) (hf : Multipliable f L)
  proof: hasProd_le h hf.hasProd hg.hasProd

@[to_additive (attr := mono)]

中文:
定理 Multipliable.tprod_le_tprod
  结论: [L.NeBot] (h : 对任意 i, f i <= g i) (hf : Multipliable f L)
  证明: hasProd_le h hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
-/
protected theorem Multipliable.tprod_le_tprod [L.NeBot] (h : forall i, f i <= g i) (hf : Multipliable f L)
    (hg : Multipliable g L) : ∏'[L] i, f i <= ∏'[L] i, g i :=
  hasProd_le h hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
/--
theorem `Multipliable.tprod_mono` / 定理 `Multipliable.tprod_mono`

English:
theorem Multipliable.tprod_mono
  statement: [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
  proof: hf.tprod_le_tprod h hg

omit [IsOrderedMonoid α] in
@[to_additive]

中文:
定理 Multipliable.tprod_mono
  结论: [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
  证明: hf.tprod_le_tprod h hg

omit [IsOrderedMonoid α] in
@[to_additive]
-/
protected theorem Multipliable.tprod_mono [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
    (h : f <= g) : ∏'[L] n, f n <= ∏'[L] n, g n :=
  hf.tprod_le_tprod h hg

omit [IsOrderedMonoid α] in
@[to_additive]
/--
theorem `Multipliable.tprod_le_of_prod_le` / 定理 `Multipliable.tprod_le_of_prod_le`

English:
theorem Multipliable.tprod_le_of_prod_le
  statement: [L.NeBot] (hf : Multipliable f L)
  proof: hasProd_le_of_prod_le hf.hasProd h

omit [IsOrderedMonoid α] in
@[to_additive]

中文:
定理 Multipliable.tprod_le_of_prod_le
  结论: [L.NeBot] (hf : Multipliable f L)
  证明: hasProd_le_of_prod_le hf.hasProd h

omit [IsOrderedMonoid α] in
@[to_additive]
-/
protected theorem Multipliable.tprod_le_of_prod_le [L.NeBot] (hf : Multipliable f L)
    (h : forall s, ∏ i in s, f i <= a₂) : ∏'[L] i, f i <= a₂ :=
  hasProd_le_of_prod_le hf.hasProd h

omit [IsOrderedMonoid α] in
@[to_additive]
/--
theorem `tprod_le_of_prod_le'` / 定理 `tprod_le_of_prod_le'`

English:
theorem tprod_le_of_prod_le'
  given: (ha₂ : 1 <= a₂) (h : forall s, ∏ i in s, f i <= a₂)
  proof: by
  by_cases hL : L.NeBot
  · by_cases hf : Multipliable f L
    · exact hf.tprod_le_of_prod_le h
    · rwa [tprod_eq_one_of_not_multipliable hf]
  · by_cases hf : f.mulSupport.Finite
    · simpa [tprod_bot hL, finprod_eq_prod _ hf] using h _
    · rwa [tprod_bot hL, finprod_of_infinite_mulSupport 

中文:
定理 tprod_le_of_prod_le'
  条件: (ha₂ : 1 <= a₂) (h : 对任意 s, ∏ i in s, f i <= a₂)
  证明: by
  by_cases hL : L.NeBot
  · by_cases hf : Multipliable f L
    · exact hf.tprod_le_of_prod_le h
    · rwa [tprod_eq_one_of_not_multipliable hf]
  · by_cases hf : f.mulSupport.Finite
    · simpa [tprod_bot hL, finprod_eq_prod _ hf] using h _
    · rwa [tprod_bot hL, finprod_of_infinite_mulSupport 

Depends on / 依赖: Finite, L.NeBot, Multipliable, f.mulSupport.Finite, finprod_eq_prod, finprod_of_infinite_mulSupport, hf.tprod_le_of_prod_le, mulSupport, tprod_bot, tprod_eq_one_of_not_multipliable, tprod_le_of_prod_le
-/
theorem tprod_le_of_prod_le' (ha₂ : 1 <= a₂) (h : forall s, ∏ i in s, f i <= a₂) :
    ∏'[L] i, f i <= a₂ := by
  by_cases hL : L.NeBot
  · by_cases hf : Multipliable f L
    · exact hf.tprod_le_of_prod_le h
    · rwa [tprod_eq_one_of_not_multipliable hf]
  · by_cases hf : f.mulSupport.Finite
    · simpa [tprod_bot hL, finprod_eq_prod _ hf] using h _
    · rwa [tprod_bot hL, finprod_of_infinite_mulSupport hf]

@[to_additive]
/--
theorem `HasProd.one_le` / 定理 `HasProd.one_le`

English:
theorem HasProd.one_le
  given: [L.NeBot] (h : forall i, 1 <= g i) (ha : HasProd g a L)
  statement: 1 <= a
  proof: hasProd_le h hasProd_one ha

@[to_additive]

中文:
定理 HasProd.one_le
  条件: [L.NeBot] (h : 对任意 i, 1 <= g i) (ha : HasProd g a L)
  结论: 1 <= a
  证明: hasProd_le h hasProd_one ha

@[to_additive]

Depends on / 依赖: hasProd_le, hasProd_one
-/
theorem HasProd.one_le [L.NeBot] (h : forall i, 1 <= g i) (ha : HasProd g a L) : 1 <= a :=
  hasProd_le h hasProd_one ha

@[to_additive]
/--
theorem `HasProd.le_one` / 定理 `HasProd.le_one`

English:
theorem HasProd.le_one
  given: [L.NeBot] (h : forall i, g i <= 1) (ha : HasProd g a L)
  statement: a <= 1
  proof: hasProd_le h ha hasProd_one

@[to_additive tsum_nonneg]

中文:
定理 HasProd.le_one
  条件: [L.NeBot] (h : 对任意 i, g i <= 1) (ha : HasProd g a L)
  结论: a <= 1
  证明: hasProd_le h ha hasProd_one

@[to_additive tsum_nonneg]

Depends on / 依赖: hasProd_le, hasProd_one
-/
theorem HasProd.le_one [L.NeBot] (h : forall i, g i <= 1) (ha : HasProd g a L) : a <= 1 :=
  hasProd_le h ha hasProd_one

@[to_additive tsum_nonneg]
/--
theorem `one_le_tprod` / 定理 `one_le_tprod`

English:
theorem one_le_tprod
  given: (h : forall i, 1 <= g i)
  statement: 1 <= ∏'[L] i, g i
  proof: by
  by_cases hg : Multipliable g L
  · by_cases hL : L.NeBot
    · exact hg.hasProd.one_le h
    · simpa [tprod_bot hL] using one_le_finprod' h
  · rw [tprod_eq_one_of_not_multipliable hg]

@[to_additive]

中文:
定理 one_le_tprod
  条件: (h : 对任意 i, 1 <= g i)
  结论: 1 <= ∏'[L] i, g i
  证明: by
  by_cases hg : Multipliable g L
  · by_cases hL : L.NeBot
    · exact hg.hasProd.one_le h
    · simpa [tprod_bot hL] using one_le_finprod' h
  · rw [tprod_eq_one_of_not_multipliable hg]

@[to_additive]

Depends on / 依赖: L.NeBot, Multipliable, hasProd, hg.hasProd.one_le, one_le, one_le_finprod, tprod_bot, tprod_eq_one_of_not_multipliable
-/
theorem one_le_tprod (h : forall i, 1 <= g i) : 1 <= ∏'[L] i, g i := by
  by_cases hg : Multipliable g L
  · by_cases hL : L.NeBot
    · exact hg.hasProd.one_le h
    · simpa [tprod_bot hL] using one_le_finprod' h
  · rw [tprod_eq_one_of_not_multipliable hg]

@[to_additive]
/--
theorem `tprod_le_one` / 定理 `tprod_le_one`

English:
theorem tprod_le_one
  given: (h : forall i, f i <= 1)
  statement: ∏'[L] i, f i <= 1
  proof: by
  by_cases hf : Multipliable f L
  · by_cases hL : L.NeBot
    · exact hf.hasProd.le_one h
    · simp only [tprod_bot hL]
      exact finprod_induction (· <= 1) le_rfl (fun _ _ => mul_le_one') h
  · rw [tprod_eq_one_of_not_multipliable hf]

@[to_additive]

中文:
定理 tprod_le_one
  条件: (h : 对任意 i, f i <= 1)
  结论: ∏'[L] i, f i <= 1
  证明: by
  by_cases hf : Multipliable f L
  · by_cases hL : L.NeBot
    · exact hf.hasProd.le_one h
    · simp only [tprod_bot hL]
      exact finprod_induction (· <= 1) le_rfl (fun _ _ => mul_le_one') h
  · rw [tprod_eq_one_of_not_multipliable hf]

@[to_additive]

Depends on / 依赖: L.NeBot, Multipliable, finprod_induction, hasProd, hf.hasProd.le_one, le_one, le_rfl, mul_le_one, tprod_bot, tprod_eq_one_of_not_multipliable
-/
theorem tprod_le_one (h : forall i, f i <= 1) : ∏'[L] i, f i <= 1 := by
  by_cases hf : Multipliable f L
  · by_cases hL : L.NeBot
    · exact hf.hasProd.le_one h
    · simp only [tprod_bot hL]
      exact finprod_induction (· <= 1) le_rfl (fun _ _ => mul_le_one') h
  · rw [tprod_eq_one_of_not_multipliable hf]

@[to_additive]
/--
theorem `hasProd_one_iff_of_one_le` / 定理 `hasProd_one_iff_of_one_le`

English:
theorem hasProd_one_iff_of_one_le
  statement: {ι α : Type*} {L : SummationFilter ι} [CommMonoid α]
  proof: by
  refine ⟨fun hf' => ?_, ?_⟩
  · ext i
    exact (hf i).antisymm' (le_hasProd hf' _ fun j _ => hf j)
  · rintro rfl
    exact hasProd_one

中文:
定理 hasProd_one_iff_of_one_le
  结论: {ι α : 类型} {L : SummationFilter ι} [CommMonoid α]
  证明: by
  refine ⟨fun hf' => ?_, ?_⟩
  · ext i
    exact (hf i).antisymm' (le_hasProd hf' _ fun j _ => hf j)
  · rintro rfl
    exact hasProd_one

Depends on / 依赖: antisymm, hasProd_one, le_hasProd
-/
theorem hasProd_one_iff_of_one_le {ι α : Type*} {L : SummationFilter ι} [CommMonoid α]
  [PartialOrder α] [IsOrderedMonoid α] [TopologicalSpace α] [OrderClosedTopology α]
  {f : ι -> α} [L.LeAtTop] [L.NeBot] (hf : forall i, 1 <= f i) :
    HasProd f 1 L ↔ f = 1 := by
  refine ⟨fun hf' => ?_, ?_⟩
  · ext i
    exact (hf i).antisymm' (le_hasProd hf' _ fun j _ => hf j)
  · rintro rfl
    exact hasProd_one

end OrderedCommMonoid

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [IsTopologicalGroup α]
  [OrderClosedTopology α] {f g : ι -> α} {a₁ a₂ : α} {i : ι}

@[to_additive]
/--
theorem `hasProd_lt` / 定理 `hasProd_lt`

English:
theorem hasProd_lt
  statement: [L.NeBot] [L.LeAtTop] (h : f <= g) (hi : f i < g i) (hf : HasProd f a₁ L)
  proof: by
  classical
  have : update f i 1 <= update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 1 / f i * a₁ <= 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive (attr := 

中文:
定理 hasProd_lt
  结论: [L.NeBot] [L.LeAtTop] (h : f <= g) (hi : f i < g i) (hf : HasProd f a₁ L)
  证明: by
  classical
  have : update f i 1 <= update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 1 / f i * a₁ <= 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive (attr := 

Depends on / 依赖: classical, hasProd_le, hf.update, hg.update, mul_inv_cancel_left, mul_lt_mul_of_lt_of_le, one_div, rfl.le, update, update_le_update_iff, update_le_update_iff.mpr
-/
theorem hasProd_lt [L.NeBot] [L.LeAtTop] (h : f <= g) (hi : f i < g i) (hf : HasProd f a₁ L)
    (hg : HasProd g a₂ L) : a₁ < a₂ := by
  classical
  have : update f i 1 <= update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 1 / f i * a₁ <= 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive (attr := mono)]
/--
theorem `hasProd_strict_mono` / 定理 `hasProd_strict_mono`

English:
theorem hasProd_strict_mono
  given: (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g)
  statement: a₁ < a₂
  proof: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg

@[to_additive]

中文:
定理 hasProd_strict_mono
  条件: (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g)
  结论: a₁ < a₂
  证明: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg

@[to_additive]

Depends on / 依赖: Pi.lt_def.mp, hasProd_lt, lt_def
-/
theorem hasProd_strict_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg

@[to_additive]
/--
theorem `Multipliable.tprod_lt_tprod` / 定理 `Multipliable.tprod_lt_tprod`

English:
theorem Multipliable.tprod_lt_tprod
  statement: [L.NeBot] [L.LeAtTop]
  proof: hasProd_lt h hi hf.hasProd hg.hasProd

@[to_additive (attr := mono)]

中文:
定理 Multipliable.tprod_lt_tprod
  结论: [L.NeBot] [L.LeAtTop]
  证明: hasProd_lt h hi hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
-/
protected theorem Multipliable.tprod_lt_tprod [L.NeBot] [L.LeAtTop]
    (h : f <= g) (hi : f i < g i) (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] n, f n < ∏'[L] n, g n :=
  hasProd_lt h hi hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
/--
theorem `Multipliable.tprod_strict_mono` / 定理 `Multipliable.tprod_strict_mono`

English:
theorem Multipliable.tprod_strict_mono
  statement: [L.NeBot] [L.LeAtTop]
  proof: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hf.tprod_lt_tprod hle hi hg

@[to_additive Summable.tsum_pos]

中文:
定理 Multipliable.tprod_strict_mono
  结论: [L.NeBot] [L.LeAtTop]
  证明: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hf.tprod_lt_tprod hle hi hg

@[to_additive Summable.tsum_pos]
-/
protected theorem Multipliable.tprod_strict_mono [L.NeBot] [L.LeAtTop]
    (hf : Multipliable f L) (hg : Multipliable g L)
    (h : f < g) : ∏'[L] n, f n < ∏'[L] n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hf.tprod_lt_tprod hle hi hg

@[to_additive Summable.tsum_pos]
/--
theorem `Multipliable.one_lt_tprod` / 定理 `Multipliable.one_lt_tprod`

English:
theorem Multipliable.one_lt_tprod
  statement: [L.LeAtTop] [L.NeBot] (hsum : Multipliable g L)
  proof: by
  rw [← tprod_one (L := L)]
  exact multipliable_one.tprod_lt_tprod hg hi hsum

中文:
定理 Multipliable.one_lt_tprod
  结论: [L.LeAtTop] [L.NeBot] (hsum : Multipliable g L)
  证明: by
  rw [← tprod_one (L := L)]
  exact multipliable_one.tprod_lt_tprod hg hi hsum
-/
protected theorem Multipliable.one_lt_tprod [L.LeAtTop] [L.NeBot] (hsum : Multipliable g L)
    (hg : forall i, 1 <= g i) (i : ι) (hi : 1 < g i) : 1 < ∏'[L] i, g i := by
  rw [← tprod_one (L := L)]
  exact multipliable_one.tprod_lt_tprod hg hi hsum

end OrderedCommGroup

section WithZero

variable [CommMonoidWithZero α] [TopologicalSpace α] [Preorder α] [ZeroLEOneClass α]
  [PosMulMono α] [ClosedIciTopology α]

/--
theorem `HasProd.nonneg` / 定理 `HasProd.nonneg`

English:
theorem HasProd.nonneg
  given: [L.NeBot] {f : ι -> α} (hf : forall i, 0 <= f i) {a : α} (h : HasProd f a L)
  proof: ge_of_tendsto' h fun s => s.prod_nonneg fun i _ => hf i

中文:
定理 HasProd.nonneg
  条件: [L.NeBot] {f : ι -> α} (hf : 对任意 i, 0 <= f i) {a : α} (h : HasProd f a L)
  证明: ge_of_tendsto' h fun s => s.prod_nonneg fun i _ => hf i

Depends on / 依赖: ge_of_tendsto, prod_nonneg, s.prod_nonneg
-/
theorem HasProd.nonneg [L.NeBot] {f : ι -> α} (hf : forall i, 0 <= f i) {a : α} (h : HasProd f a L) :
    0 <= a :=
  ge_of_tendsto' h fun s => s.prod_nonneg fun i _ => hf i

/--
theorem `tprod_nonneg` / 定理 `tprod_nonneg`

English:
theorem tprod_nonneg
  given: {f : ι -> α} (hf : forall i, 0 <= f i)
  proof: by
  by_cases h : Multipliable f L
  · by_cases hbot : L.NeBot
    · exact h.hasProd.nonneg hf
    · simpa [tprod_bot hbot] using finprod_nonneg hf
  · simp [tprod_eq_one_of_not_multipliable h]

中文:
定理 tprod_nonneg
  条件: {f : ι -> α} (hf : 对任意 i, 0 <= f i)
  证明: by
  by_cases h : Multipliable f L
  · by_cases hbot : L.NeBot
    · exact h.hasProd.nonneg hf
    · simpa [tprod_bot hbot] using finprod_nonneg hf
  · simp [tprod_eq_one_of_not_multipliable h]

Depends on / 依赖: L.NeBot, Multipliable, finprod_nonneg, h.hasProd.nonneg, hasProd, nonneg, tprod_bot, tprod_eq_one_of_not_multipliable
-/
theorem tprod_nonneg {f : ι -> α} (hf : forall i, 0 <= f i) :
    0 <= ∏'[L] x, f x := by
  by_cases h : Multipliable f L
  · by_cases hbot : L.NeBot
    · exact h.hasProd.nonneg hf
    · simpa [tprod_bot hbot] using finprod_nonneg hf
  · simp [tprod_eq_one_of_not_multipliable h]

end WithZero

section CanonicallyOrderedMul

variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
  [CanonicallyOrderedMul α] [TopologicalSpace α]
  [OrderClosedTopology α] {f : ι -> α} {a : α}

@[to_additive]
/--
theorem `le_hasProd'` / 定理 `le_hasProd'`

English:
theorem le_hasProd'
  given: (hf : HasProd f a) (i : ι)
  statement: f i <= a
  proof: le_hasProd hf i fun _ _ => one_le

@[to_additive]

中文:
定理 le_hasProd'
  条件: (hf : HasProd f a) (i : ι)
  结论: f i <= a
  证明: le_hasProd hf i fun _ _ => one_le

@[to_additive]

Depends on / 依赖: le_hasProd, one_le
-/
theorem le_hasProd' (hf : HasProd f a) (i : ι) : f i <= a :=
  le_hasProd hf i fun _ _ => one_le

@[to_additive]
/--
theorem `Multipliable.le_tprod'` / 定理 `Multipliable.le_tprod'`

English:
theorem Multipliable.le_tprod'
  given: (hf : Multipliable f) (i : ι)
  statement: f i <= ∏' i, f i
  proof: hf.le_tprod i fun _ _ => one_le

@[to_additive]

中文:
定理 Multipliable.le_tprod'
  条件: (hf : Multipliable f) (i : ι)
  结论: f i <= ∏' i, f i
  证明: hf.le_tprod i fun _ _ => one_le

@[to_additive]
-/
protected theorem Multipliable.le_tprod' (hf : Multipliable f) (i : ι) : f i <= ∏' i, f i :=
  hf.le_tprod i fun _ _ => one_le

@[to_additive]
/--
theorem `hasProd_one_iff` / 定理 `hasProd_one_iff`

English:
theorem hasProd_one_iff
  statement: HasProd f 1 ↔ forall x, f x = 1
  proof: (hasProd_one_iff_of_one_le fun _ => one_le).trans funext_iff

@[to_additive]

中文:
定理 hasProd_one_iff
  结论: HasProd f 1 ↔ 对任意 x, f x = 1
  证明: (hasProd_one_iff_of_one_le fun _ => one_le).trans funext_iff

@[to_additive]

Depends on / 依赖: funext_iff, hasProd_one_iff_of_one_le, one_le
-/
theorem hasProd_one_iff : HasProd f 1 ↔ forall x, f x = 1 :=
  (hasProd_one_iff_of_one_le fun _ => one_le).trans funext_iff

@[to_additive]
/--
theorem `Multipliable.tprod_eq_one_iff` / 定理 `Multipliable.tprod_eq_one_iff`

English:
theorem Multipliable.tprod_eq_one_iff
  given: (hf : Multipliable f)
  proof: by
  rw [← hasProd_one_iff]; rw [hf.hasProd_iff]

@[to_additive]

中文:
定理 Multipliable.tprod_eq_one_iff
  条件: (hf : Multipliable f)
  证明: by
  rw [← hasProd_one_iff]; rw [hf.hasProd_iff]

@[to_additive]
-/
protected theorem Multipliable.tprod_eq_one_iff (hf : Multipliable f) :
    ∏' i, f i = 1 ↔ forall x, f x = 1 := by
  rw [← hasProd_one_iff]; rw [hf.hasProd_iff]

@[to_additive]
/--
theorem `Multipliable.tprod_ne_one_iff` / 定理 `Multipliable.tprod_ne_one_iff`

English:
theorem Multipliable.tprod_ne_one_iff
  given: (hf : Multipliable f)
  proof: by
  rw [Ne]; rw [hf.tprod_eq_one_iff]; rw [not_forall]

omit [IsOrderedMonoid α] in
@[to_additive]

中文:
定理 Multipliable.tprod_ne_one_iff
  条件: (hf : Multipliable f)
  证明: by
  rw [Ne]; rw [hf.tprod_eq_one_iff]; rw [not_forall]

omit [IsOrderedMonoid α] in
@[to_additive]
-/
protected theorem Multipliable.tprod_ne_one_iff (hf : Multipliable f) :
    ∏' i, f i != 1 ↔ exists x, f x != 1 := by
  rw [Ne]; rw [hf.tprod_eq_one_iff]; rw [not_forall]

omit [IsOrderedMonoid α] in
@[to_additive]
/--
theorem `isLUB_hasProd'` / 定理 `isLUB_hasProd'`

English:
theorem isLUB_hasProd'
  given: (hf : HasProd f a)
  statement: IsLUB (Set.range fun s => ∏ i in s, f i) a
  proof: by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf

中文:
定理 isLUB_hasProd'
  条件: (hf : HasProd f a)
  结论: IsLUB (Set.range fun s => ∏ i in s, f i) a
  证明: by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf

Depends on / 依赖: Finset, Finset.prod_mono_set, isLUB_of_tendsto_atTop, prod_mono_set
-/
theorem isLUB_hasProd' (hf : HasProd f a) : IsLUB (Set.range fun s => ∏ i in s, f i) a := by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf

end CanonicallyOrderedMul

section LinearOrder

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

@[to_additive]
/--
theorem `hasProd_of_isLUB_of_one_le` / 定理 `hasProd_of_isLUB_of_one_le`

English:
theorem hasProd_of_isLUB_of_one_le
  statement: [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
  proof: tendsto_atTop_isLUB (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]

中文:
定理 hasProd_of_isLUB_of_one_le
  结论: [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
  证明: tendsto_atTop_isLUB (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_mono_set_of_one_le, prod_mono_set_of_one_le, tendsto_atTop_isLUB
-/
theorem hasProd_of_isLUB_of_one_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    [TopologicalSpace α]
    [OrderTopology α] {f : ι -> α} (i : α) (h : forall i, 1 <= f i)
    (hf : IsLUB (Set.range fun s => ∏ i in s, f i) i) : HasProd f i :=
  tendsto_atTop_isLUB (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
/--
theorem `hasProd_of_isGLB_of_le_one` / 定理 `hasProd_of_isGLB_of_le_one`

English:
theorem hasProd_of_isGLB_of_le_one
  statement: [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
  proof: tendsto_atTop_isGLB (Finset.prod_anti_set_of_le_one' h₀) hf

@[to_additive]

中文:
定理 hasProd_of_isGLB_of_le_one
  结论: [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
  证明: tendsto_atTop_isGLB (Finset.prod_anti_set_of_le_one' h₀) hf

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_anti_set_of_le_one, prod_anti_set_of_le_one, tendsto_atTop_isGLB
-/
theorem hasProd_of_isGLB_of_le_one [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    [TopologicalSpace α]
    [OrderTopology α] {f : ι -> α} (i : α) (h₀ : forall i, f i <= 1)
    (hf : IsGLB (Set.range fun s => ∏ i in s, f i) i) : HasProd f i :=
  tendsto_atTop_isGLB (Finset.prod_anti_set_of_le_one' h₀) hf

@[to_additive]
/--
theorem `hasProd_of_isLUB` / 定理 `hasProd_of_isLUB`

English:
theorem hasProd_of_isLUB
  statement: [CommMonoid α] [LinearOrder α]
  proof: tendsto_atTop_isLUB (Finset.prod_mono_set' f) hf

@[to_additive]

中文:
定理 hasProd_of_isLUB
  结论: [CommMonoid α] [LinearOrder α]
  证明: tendsto_atTop_isLUB (Finset.prod_mono_set' f) hf

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_mono_set, prod_mono_set, tendsto_atTop_isLUB
-/
theorem hasProd_of_isLUB [CommMonoid α] [LinearOrder α]
    [CanonicallyOrderedMul α] [TopologicalSpace α]
    [OrderTopology α] {f : ι -> α} (b : α) (hf : IsLUB (Set.range fun s => ∏ i in s, f i) b) :
    HasProd f b :=
  tendsto_atTop_isLUB (Finset.prod_mono_set' f) hf

@[to_additive]
/--
theorem `multipliable_mabs_iff` / 定理 `multipliable_mabs_iff`

English:
theorem multipliable_mabs_iff
  statement: [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
  proof: let s := { x | 1 <= f x }
  have h1 : forall x : s, mabs (f x) = f x := fun x => mabs_of_one_le x.2
  have h2 : forall x : ↑sᶜ, mabs (f x) = (f x)⁻¹ := fun x => mabs_of_lt_one (not_le.1 x.2)
  calc (Multipliable fun x => mabs (f x)) ↔
      (Multipliable fun x : s => mabs (f x)) ∧ Multipliable fun x

中文:
定理 multipliable_mabs_iff
  结论: [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
  证明: let s := { x | 1 <= f x }
  have h1 : forall x : s, mabs (f x) = f x := fun x => mabs_of_one_le x.2
  have h2 : forall x : ↑sᶜ, mabs (f x) = (f x)⁻¹ := fun x => mabs_of_lt_one (not_le.1 x.2)
  calc (Multipliable fun x => mabs (f x)) ↔
      (Multipliable fun x : s => mabs (f x)) ∧ Multipliable fun x

Depends on / 依赖: Multipliable, mabs_of_lt_one, mabs_of_one_le, multipliable_inv_, multipliable_subtype_and_compl, multipliable_subtype_and_compl.symm, not_le
-/
theorem multipliable_mabs_iff [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
    [UniformSpace α] [IsUniformGroup α]
    [CompleteSpace α] {f : ι -> α} : (Multipliable fun x => mabs (f x)) ↔ Multipliable f :=
  let s := { x | 1 <= f x }
  have h1 : forall x : s, mabs (f x) = f x := fun x => mabs_of_one_le x.2
  have h2 : forall x : ↑sᶜ, mabs (f x) = (f x)⁻¹ := fun x => mabs_of_lt_one (not_le.1 x.2)
  calc (Multipliable fun x => mabs (f x)) ↔
      (Multipliable fun x : s => mabs (f x)) ∧ Multipliable fun x : ↑sᶜ => mabs (f x) :=
        multipliable_subtype_and_compl.symm
  _ ↔ (Multipliable fun x : s => f x) ∧ Multipliable fun x : ↑sᶜ => (f x)⁻¹ := by simp only [h1, h2]
  _ ↔ Multipliable f := by simp only [multipliable_inv_iff, multipliable_subtype_and_compl]

alias ⟨Summable.of_abs, Summable.abs⟩ := summable_abs_iff

/--
theorem `Finite.of_summable_const` / 定理 `Finite.of_summable_const`

English:
theorem Finite.of_summable_const
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: by
  have H : forall s : Finset ι, #s • b <= ∑' _ : ι, b := fun s => by
    simpa using sum_le_hasSum s (fun a _ => hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : forall s : Finset ι, #s <= n := fun s => by
    simpa [nsmul_le_nsmul_iff_left hb] using (H s).trans hn


中文:
定理 Finite.of_summable_const
  结论: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  证明: by
  have H : forall s : Finset ι, #s • b <= ∑' _ : ι, b := fun s => by
    simpa using sum_le_hasSum s (fun a _ => hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : forall s : Finset ι, #s <= n := fun s => by
    simpa [nsmul_le_nsmul_iff_left hb] using (H s).trans hn


Depends on / 依赖: Archimedean, Archimedean.arch, Finset, Fintype, fintypeOfFinsetCardLe, hasSum, hb.le, hf.hasSum, infer_instance, nsmul_le_nsmul_iff_left, sum_le_hasSum
-/
theorem Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [TopologicalSpace α] [Archimedean α]
    [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι => b) :
    Finite ι := by
  have H : forall s : Finset ι, #s • b <= ∑' _ : ι, b := fun s => by
    simpa using sum_le_hasSum s (fun a _ => hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : forall s : Finset ι, #s <= n := fun s => by
    simpa [nsmul_le_nsmul_iff_left hb] using (H s).trans hn
  have : Fintype ι := fintypeOfFinsetCardLe n this
  infer_instance

/--
theorem `Set.Finite.of_summable_const` / 定理 `Set.Finite.of_summable_const`

English:
theorem Set.Finite.of_summable_const
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: finite_univ_iff.2 .of_summable_const hb hf

中文:
定理 Set.Finite.of_summable_const
  结论: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  证明: finite_univ_iff.2 .of_summable_const hb hf

Depends on / 依赖: finite_univ_iff, of_summable_const
-/
theorem Set.Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [TopologicalSpace α]
    [Archimedean α] [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι => b) :
    (Set.univ : Set ι).Finite :=
finite_univ_iff.2 .of_summable_const hb hf

end LinearOrder

section LinearOrderedCommRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
  [TopologicalSpace α] [OrderTopology α] {f : ι -> α} {x : α}

nonrec theorem HasProd.abs (hfx : HasProd f x) : HasProd (|f ·|) |x| := by
  simpa only [HasProd, ← abs_prod] using hfx.abs

/--
theorem `Multipliable.abs` / 定理 `Multipliable.abs`

English:
theorem Multipliable.abs
  given: (hf : Multipliable f)
  statement: Multipliable (|f ·|)
  proof: let ⟨x, hx⟩ := hf; ⟨|x|, hx.abs⟩

中文:
定理 Multipliable.abs
  条件: (hf : Multipliable f)
  结论: Multipliable (|f ·|)
  证明: let ⟨x, hx⟩ := hf; ⟨|x|, hx.abs⟩

Depends on / 依赖: hx.abs
-/
theorem Multipliable.abs (hf : Multipliable f) : Multipliable (|f ·|) :=
  let ⟨x, hx⟩ := hf; ⟨|x|, hx.abs⟩

/--
theorem `Multipliable.abs_tprod` / 定理 `Multipliable.abs_tprod`

English:
theorem Multipliable.abs_tprod
  given: (hf : Multipliable f)
  statement: |∏' i, f i| = ∏' i, |f i|
  proof: hf.hasProd.abs.tprod_eq.symm

中文:
定理 Multipliable.abs_tprod
  条件: (hf : Multipliable f)
  结论: |∏' i, f i| = ∏' i, |f i|
  证明: hf.hasProd.abs.tprod_eq.symm
-/
protected theorem Multipliable.abs_tprod (hf : Multipliable f) : |∏' i, f i| = ∏' i, |f i| :=
  hf.hasProd.abs.tprod_eq.symm

end LinearOrderedCommRing

/--
theorem `Summable.tendsto_atTop_of_pos` / 定理 `Summable.tendsto_atTop_of_pos`

English:
theorem Summable.tendsto_atTop_of_pos
  statement: [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: inv_inv f ▸ Filter.Tendsto.inv_tendsto_nhdsGT_zero
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero
      Eventually.of_forall fun _ => inv_pos.2 (hf' _)

中文:
定理 Summable.tendsto_atTop_of_pos
  结论: [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  证明: inv_inv f ▸ Filter.Tendsto.inv_tendsto_nhdsGT_zero
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero
      Eventually.of_forall fun _ => inv_pos.2 (hf' _)

Depends on / 依赖: Eventually, Eventually.of_forall, Filter, Filter.Tendsto.inv_tendsto_nhdsGT_zero, Tendsto, hf.tendsto_atTop_zero, inv_inv, inv_pos, inv_tendsto_nhdsGT_zero, of_forall, tendsto_atTop_zero, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem Summable.tendsto_atTop_of_pos [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [OrderTopology α]
    {f : Nat -> α} (hf : Summable f⁻¹) (hf' : forall n, 0 < f n) : Tendsto f atTop atTop :=
inv_inv f ▸ Filter.Tendsto.inv_tendsto_nhdsGT_zero
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero
      Eventually.of_forall fun _ => inv_pos.2 (hf' _)

namespace Mathlib.Meta.Positivity

open Qq Lean Meta Finset

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for infinite sums.

This extension only proves non-negativity, strict positivity is more delicate for infinite sums and
requires more assumptions. -/
@[positivity tsum _]
meta def evalTsum : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@tsum _ $ι $instCommMonoid $instTopSpace $f $L) =>
    lambdaBoundedTelescope f 1 fun args (body : Q($α)) => do
      let #[(i : Q($ι))] := args | failure
      let rbody ← core zα pα body
      let pbody ← rbody.toNonneg
      let pr : Q(forall i, 0 <= $f i) ← mkLambdaFVars #[i] pbody
      let mα' ← synthInstanceQ q(AddCommMonoid $α)
      let oα' ← synthInstanceQ q(Preorder $α)
      let pα' ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instOrderClosed ← synthInstanceQ q(OrderClosedTopology $α)
      assertInstancesCommute
      return .nonnegative
        q(@tsum_nonneg $ι $α $L $mα' $oα' $pα' $instTopSpace $instOrderClosed $f $pr)
  | _ => throwError "not tsum"

end Mathlib.Meta.Positivity
