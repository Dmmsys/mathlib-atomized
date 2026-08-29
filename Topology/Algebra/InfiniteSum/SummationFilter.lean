/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.LiminfLimsup


/-!
# Summation filters

We define a `SummationFilter` on `β` to be a filter on the finite subsets of `β`. These are used
in defining summability: if `L` is a summation filter, we define the `L`-sum of `f` to be the
limit along `L` of the sums over finsets (if this limit exists). This file only develops the basic
machinery of summation filters - the key definitions `HasSum`, `tsum` and `summable` (and their
product variants) are in the file `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`.
-/

@[expose] public section

open Set Filter Function

variable {α β γ : Type*}

/--
Definition of `SummationFilter` / `SummationFilter` 的定义

English:
structure SummationFilter
  parameters: (β)
  axioms and operations (1):
    - filter : Filter (Finset β)

中文:
结构 SummationFilter
  参数: (β)
  公理与运算 (1 个):
    - filter : Filter (Finset β)
-/
structure SummationFilter (β) where
  /-- The filter -/
  filter : Filter (Finset β)

namespace SummationFilter

/--
Definition of `LeAtTop` / `LeAtTop` 的定义

English:
class LeAtTop
  parameters: (L : SummationFilter β)
  axioms and operations (1):
    - le_atTop : L.filter <= atTop

中文:
类 LeAtTop
  参数: (L : SummationFilter β)
  公理与运算 (1 个):
    - le_atTop : L.filter <= atTop
-/
class LeAtTop (L : SummationFilter β) : Prop where
  le_atTop : L.filter <= atTop

export LeAtTop (le_atTop)

/--
Definition of `NeBot` / `NeBot` 的定义

English:
class NeBot
  parameters: (L : SummationFilter β)
  axioms and operations (1):
    - ne_bot : L.filter.NeBot

中文:
类 NeBot
  参数: (L : SummationFilter β)
  公理与运算 (1 个):
    - ne_bot : L.filter.NeBot
-/
class NeBot (L : SummationFilter β) : Prop where
  ne_bot : L.filter.NeBot

/-- Makes the `NeBot` instance visible to the typeclass machinery. -/
instance (L : SummationFilter β) [L.NeBot] : L.filter.NeBot := NeBot.ne_bot

/--
lemma `neBot_or_eq_bot` / 引理 `neBot_or_eq_bot`

English:
lemma neBot_or_eq_bot
  given: (L : SummationFilter β)
  statement: L.NeBot ∨ L.filter = ⊥
  proof: by
  by_cases h : L.filter = ⊥
  · exact .inr h
  · exact .inl ⟨⟨h⟩⟩

中文:
引理 neBot_or_eq_bot
  条件: (L : SummationFilter β)
  结论: L.NeBot ∨ L.filter = ⊥
  证明: by
  by_cases h : L.filter = ⊥
  · exact .inr h
  · exact .inl ⟨⟨h⟩⟩

Depends on / 依赖: L.filter, filter
-/
lemma neBot_or_eq_bot (L : SummationFilter β) : L.NeBot ∨ L.filter = ⊥ := by
  by_cases h : L.filter = ⊥
  · exact .inr h
  · exact .inl ⟨⟨h⟩⟩

section support

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (L : SummationFilter β)
  body: {b | forallᶠ s in L.filter, b in s}

中文:
定义 support
  签名: (L : SummationFilter β)
  定义体: {b | forallᶠ s in L.filter, b in s}

Depends on / 依赖: L.filter, filter
-/
def support (L : SummationFilter β) : Set β := {b | forallᶠ s in L.filter, b in s}

/--
lemma `support_eq_limsInf` / 引理 `support_eq_limsInf`

English:
lemma support_eq_limsInf
  given: (L : SummationFilter β)
  proof: by
  refine eq_of_forall_ge_iff fun c => ?_
  simpa [support, limsInf, ofPred_subset] using
⟨fun hL b hb x hx => hL x hb.mp .of_forall fun c hc => hc hx,
fun hL x hx => singleton_subset_iff.mp hL _ by simpa using hx⟩

中文:
引理 support_eq_limsInf
  条件: (L : SummationFilter β)
  证明: by
  refine eq_of_forall_ge_iff fun c => ?_
  simpa [support, limsInf, ofPred_subset] using
⟨fun hL b hb x hx => hL x hb.mp .of_forall fun c hc => hc hx,
fun hL x hx => singleton_subset_iff.mp hL _ by simpa using hx⟩

Depends on / 依赖: eq_of_forall_ge_iff, hb.mp, limsInf, ofPred_subset, of_forall, singleton_subset_iff, singleton_subset_iff.mp, support
-/
lemma support_eq_limsInf (L : SummationFilter β) :
    support L = limsInf (L.filter.map (↑)) := by
  refine eq_of_forall_ge_iff fun c => ?_
  simpa [support, limsInf, ofPred_subset] using
⟨fun hL b hb x hx => hL x hb.mp .of_forall fun c hc => hc hx,
fun hL x hx => singleton_subset_iff.mp hL _ by simpa using hx⟩

/--
lemma `support_eq_univ_iff` / 引理 `support_eq_univ_iff`

English:
lemma support_eq_univ_iff
  given: {L : SummationFilter β}
  proof: by
  simp only [support, Set.eq_univ_iff_forall, Set.mem_ofPred]
  refine ⟨fun h s hs => ?_, fun h b => .filter_mono h ?_⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    have := (Filter.biInter_finset_mem t).mpr fun b hb => h b
    exact Filter.mem_of_superset this fun r hr => ht r (by simpa using! 

中文:
引理 support_eq_univ_iff
  条件: {L : SummationFilter β}
  证明: by
  simp only [support, Set.eq_univ_iff_forall, Set.mem_ofPred]
  refine ⟨fun h s hs => ?_, fun h b => .filter_mono h ?_⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    have := (Filter.biInter_finset_mem t).mpr fun b hb => h b
    exact Filter.mem_of_superset this fun r hr => ht r (by simpa using! 

Depends on / 依赖: Filter, Filter.biInter_finset_mem, Filter.mem_of_superset, Set.eq_univ_iff_forall, Set.mem_ofPred, biInter_finset_mem, eq_univ_iff_forall, eventually_ge_atTop, filter_mono, filter_upwards, mem_atTop_sets, mem_atTop_sets.mp, mem_ofPred, mem_of_superset, support
-/
lemma support_eq_univ_iff {L : SummationFilter β} :
    L.support = univ ↔ L.filter <= atTop := by
  simp only [support, Set.eq_univ_iff_forall, Set.mem_ofPred]
  refine ⟨fun h s hs => ?_, fun h b => .filter_mono h ?_⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    have := (Filter.biInter_finset_mem t).mpr fun b hb => h b
    exact Filter.mem_of_superset this fun r hr => ht r (by simpa using! hr)
  · filter_upwards [eventually_ge_atTop {b}] using by simp

/--
lemma `support_eq_univ` / 引理 `support_eq_univ`

English:
lemma support_eq_univ
  given: (L : SummationFilter β) [L.LeAtTop]
  statement: L.support = univ
  proof: support_eq_univ_iff.mpr L.le_atTop

中文:
引理 support_eq_univ
  条件: (L : SummationFilter β) [L.LeAtTop]
  结论: L.support = univ
  证明: support_eq_univ_iff.mpr L.le_atTop
-/
@[simp] lemma support_eq_univ (L : SummationFilter β) [L.LeAtTop] : L.support = univ :=
  support_eq_univ_iff.mpr L.le_atTop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: β] (L
  body: ⟨support_eq_univ_iff.mp Subsingleton.elim ..⟩

中文:
实例 [IsEmpty
  签名: β] (L
  定义体: ⟨support_eq_univ_iff.mp Subsingleton.elim ..⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, support_eq_univ_iff, support_eq_univ_iff.mp
-/
instance [IsEmpty β] (L : SummationFilter β) : L.LeAtTop :=
⟨support_eq_univ_iff.mp Subsingleton.elim ..⟩

/--
lemma `leAtTop_of_not_NeBot` / 引理 `leAtTop_of_not_NeBot`

English:
lemma leAtTop_of_not_NeBot
  given: (L : SummationFilter β) (hL : ¬L.NeBot)
  statement: L.LeAtTop
  proof: by
  have hLs : L.support = Set.univ := by
    simp [SummationFilter.support, L.neBot_or_eq_bot.resolve_left hL]
  exact ⟨L.support_eq_univ_iff.mp hLs⟩

中文:
引理 leAtTop_of_not_NeBot
  条件: (L : SummationFilter β) (hL : ¬L.NeBot)
  结论: L.LeAtTop
  证明: by
  have hLs : L.support = Set.univ := by
    simp [SummationFilter.support, L.neBot_or_eq_bot.resolve_left hL]
  exact ⟨L.support_eq_univ_iff.mp hLs⟩

Depends on / 依赖: L.neBot_or_eq_bot.resolve_left, L.support, L.support_eq_univ_iff.mp, Set.univ, SummationFilter, SummationFilter.support, neBot_or_eq_bot, resolve_left, support, support_eq_univ_iff
-/
lemma leAtTop_of_not_NeBot (L : SummationFilter β) (hL : ¬L.NeBot) : L.LeAtTop := by
  have hLs : L.support = Set.univ := by
    simp [SummationFilter.support, L.neBot_or_eq_bot.resolve_left hL]
  exact ⟨L.support_eq_univ_iff.mp hLs⟩

/-- Decidability instance: useful when working with `Finset` sums / products. -/
instance (L : SummationFilter β) [L.LeAtTop] : DecidablePred (· in L.support) :=
  fun b => isTrue (by simp)

end support

section has_support

/--
Definition of `HasSupport` / `HasSupport` 的定义

English:
class HasSupport
  parameters: (L : SummationFilter β)
  axioms and operations (1):
    - eventually_le_support : forallᶠ s in L.filter, ↑s subseteq L.support

中文:
类 HasSupport
  参数: (L : SummationFilter β)
  公理与运算 (1 个):
    - eventually_le_support : 对任意ᶠ s in L.filter, ↑s subseteq L.support
-/
class HasSupport (L : SummationFilter β) : Prop where
  eventually_le_support : forallᶠ s in L.filter, ↑s subseteq L.support

export HasSupport (eventually_le_support)

instance (L : SummationFilter β) [L.LeAtTop] : HasSupport L := ⟨by simp⟩

/--
lemma `eventually_mem_or_not_mem` / 引理 `eventually_mem_or_not_mem`

English:
lemma eventually_mem_or_not_mem
  given: (L : SummationFilter β) [HasSupport L] (b : β)
  proof: by
  rw [or_iff_not_imp_left]
  intro hb
  filter_upwards [L.eventually_le_support] with a ha using notMem_subset ha hb

中文:
引理 eventually_mem_or_not_mem
  条件: (L : SummationFilter β) [HasSupport L] (b : β)
  证明: by
  rw [or_iff_not_imp_left]
  intro hb
  filter_upwards [L.eventually_le_support] with a ha using notMem_subset ha hb

Depends on / 依赖: L.eventually_le_support, eventually_le_support, filter_upwards, notMem_subset, or_iff_not_imp_left
-/
lemma eventually_mem_or_not_mem (L : SummationFilter β) [HasSupport L] (b : β) :
    (forallᶠ s in L.filter, b in s) ∨ (forallᶠ s in L.filter, b ∉ s) := by
  rw [or_iff_not_imp_left]
  intro hb
  filter_upwards [L.eventually_le_support] with a ha using notMem_subset ha hb

end has_support

section map_comap

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (L : SummationFilter β) (f : β ↪ γ)
  body: L.filter.map (Finset.map f)

中文:
定义 map
  签名: (L : SummationFilter β) (f : β ↪ γ)
  定义体: L.filter.map (Finset.map f)
-/
@[simps] def map (L : SummationFilter β) (f : β ↪ γ) : SummationFilter γ where
  filter := L.filter.map (Finset.map f)

/--
lemma `support_map` / 引理 `support_map`

English:
lemma support_map
  given: (L : SummationFilter β) [L.NeBot] (f : β ↪ γ)
  proof: by
  ext c
  rcases em (c in range f) with ⟨b, rfl⟩ | hc
  · simp [support]
  · exact ⟨fun hc' => have := hc'.exists; by grind, by grind⟩

中文:
引理 support_map
  条件: (L : SummationFilter β) [L.NeBot] (f : β ↪ γ)
  证明: by
  ext c
  rcases em (c in range f) with ⟨b, rfl⟩ | hc
  · simp [support]
  · exact ⟨fun hc' => have := hc'.exists; by grind, by grind⟩
-/
@[simp] lemma support_map (L : SummationFilter β) [L.NeBot] (f : β ↪ γ) :
    (L.map f).support = f '' L.support := by
  ext c
  rcases em (c in range f) with ⟨b, rfl⟩ | hc
  · simp [support]
  · exact ⟨fun hc' => have := hc'.exists; by grind, by grind⟩

/-- If `L` has well-defined support, then so does its map along an embedding. -/
instance (L : SummationFilter β) [HasSupport L] (f : β ↪ γ) : HasSupport (L.map f) := by
  constructor
  obtain (h | h) := L.neBot_or_eq_bot
  · simp only [map_filter, eventually_map, Finset.coe_map, image_subset_iff, support_map]
    filter_upwards [L.eventually_le_support] with a using by grind
  · simp [h]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (L : SummationFilter β) (f : γ ↪ β)
  body: L.filter.map (fun s => s.preimage f f.injective.injOn)

中文:
定义 comap
  签名: (L : SummationFilter β) (f : γ ↪ β)
  定义体: L.filter.map (fun s => s.preimage f f.injective.injOn)
-/
@[simps] noncomputable def comap (L : SummationFilter β) (f : γ ↪ β) : SummationFilter γ where
  filter := L.filter.map (fun s => s.preimage f f.injective.injOn)

/--
lemma `support_comap` / 引理 `support_comap`

English:
lemma support_comap
  given: (L : SummationFilter β) (f : γ ↪ β)
  proof: by
  simp [support]

中文:
引理 support_comap
  条件: (L : SummationFilter β) (f : γ ↪ β)
  证明: by
  simp [support]
-/
@[simp] lemma support_comap (L : SummationFilter β) (f : γ ↪ β) :
    (L.comap f).support = f ⁻¹' L.support := by
  simp [support]

/-- If `L` has well-defined support, then so does its comap along an embedding. -/
instance (L : SummationFilter β) [HasSupport L] (f : γ ↪ β) : HasSupport (L.comap f) := by
  constructor
  simp only [support_comap, comap_filter, eventually_map, Finset.coe_preimage]
  filter_upwards [L.eventually_le_support] with a using Set.preimage_mono

instance (L : SummationFilter β) [LeAtTop L] (f : γ ↪ β) : LeAtTop (L.comap f) :=
  ⟨by rw [← support_eq_univ_iff]; simp⟩

end map_comap

section examples
/-!
## Examples of summation filters
-/
variable (β)

/--
Definition of `unconditional` / `unconditional` 的定义

English:
definition unconditional
  signature: : SummationFilter β where
  body: atTop

中文:
定义 unconditional
  签名: : SummationFilter β where
  定义体: atTop
-/
@[simps] def unconditional : SummationFilter β where
  filter := atTop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unconditional β).LeAtTop
  body: ⟨le_rfl⟩

中文:
实例 :
  签名: (unconditional β).LeAtTop
  定义体: ⟨le_rfl⟩

Depends on / 依赖: le_rfl
-/
instance : (unconditional β).LeAtTop := ⟨le_rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unconditional β).NeBot
  body: ⟨atTop_neBot⟩

中文:
实例 :
  签名: (unconditional β).NeBot
  定义体: ⟨atTop_neBot⟩

Depends on / 依赖: atTop_neBot
-/
instance : (unconditional β).NeBot := ⟨atTop_neBot⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: β] : IsCountablyGenerated (unconditional β).filter
  body: atTop.isCountablyGenerated

中文:
实例 [Countable
  签名: β] : IsCountablyGenerated (unconditional β).filter
  定义体: atTop.isCountablyGenerated

Depends on / 依赖: atTop.isCountablyGenerated, isCountablyGenerated
-/
instance [Countable β] : IsCountablyGenerated (unconditional β).filter :=
  atTop.isCountablyGenerated

/--
lemma `comap_unconditional` / 引理 `comap_unconditional`

English:
lemma comap_unconditional
  given: {β} (f : γ ↪ β)
  proof: by
  classical
  simp only [unconditional, comap]
  congr 1 with s
  simp only [mem_map, mem_atTop_sets, mem_preimage]
  constructor <;> rintro ⟨t, ht⟩
  · refine ⟨t.preimage f (by simp), fun x hx => ?_⟩
    simpa [Finset.union_eq_right.mpr hx] using ht (t union x.map f) t.subset_union_left
  · exac

中文:
引理 comap_unconditional
  条件: {β} (f : γ ↪ β)
  证明: by
  classical
  simp only [unconditional, comap]
  congr 1 with s
  simp only [mem_map, mem_atTop_sets, mem_preimage]
  constructor <;> rintro ⟨t, ht⟩
  · refine ⟨t.preimage f (by simp), fun x hx => ?_⟩
    simpa [Finset.union_eq_right.mpr hx] using ht (t union x.map f) t.subset_union_left
  · exac
-/
@[simp] lemma comap_unconditional {β} (f : γ ↪ β) :
    (unconditional β).comap f = unconditional γ := by
  classical
  simp only [unconditional, comap]
  congr 1 with s
  simp only [mem_map, mem_atTop_sets, mem_preimage]
  constructor <;> rintro ⟨t, ht⟩
  · refine ⟨t.preimage f (by simp), fun x hx => ?_⟩
    simpa [Finset.union_eq_right.mpr hx] using ht (t union x.map f) t.subset_union_left
  · exact ⟨_, fun b hb => ht _ (Finset.map_subset_iff_subset_preimage.mp hb)⟩

/--
lemma `eq_unconditional_of_finite` / 引理 `eq_unconditional_of_finite`

English:
lemma eq_unconditional_of_finite
  statement: {β} [Finite β]
  proof: by
  have := Fintype.ofFinite β
  have hAtTop : (atTop : Filter (Finset β)) = pure Finset.univ := by
    rw [(isTop_iff_eq_top.mpr rfl).atTop_eq (a := Finset.univ)]; rw [← Finset.top_eq_univ]; rw [Ici_top]; rw [principal_singleton]
  have hL := L.le_atTop
have hL' : ∅ ∉ L.filter := empty_mem_iff_bot

中文:
引理 eq_unconditional_of_finite
  结论: {β} [Finite β]
  证明: by
  have := Fintype.ofFinite β
  have hAtTop : (atTop : Filter (Finset β)) = pure Finset.univ := by
    rw [(isTop_iff_eq_top.mpr rfl).atTop_eq (a := Finset.univ)]; rw [← Finset.top_eq_univ]; rw [Ici_top]; rw [principal_singleton]
  have hL := L.le_atTop
have hL' : ∅ ∉ L.filter := empty_mem_iff_bot

Depends on / 依赖: Filter, Finset, Finset.top_eq_univ, Finset.univ, Fintype, Fintype.ofFinite, Ici_top, L.filter, L.le_atTop, NeBot.ne_bot.ne, atTop_eq, contrapose, empty_mem_iff_bot, empty_mem_iff_bot.not.mpr, eq_of_le_of_ge, filter, hAtTop, inter_singleton_eq, isTop_iff_eq_top, isTop_iff_eq_top.mpr
-/
lemma eq_unconditional_of_finite {β} [Finite β]
    (L : SummationFilter β) [L.LeAtTop] [L.NeBot] : L = unconditional β := by
  have := Fintype.ofFinite β
  have hAtTop : (atTop : Filter (Finset β)) = pure Finset.univ := by
    rw [(isTop_iff_eq_top.mpr rfl).atTop_eq (a := Finset.univ)]; rw [← Finset.top_eq_univ]; rw [Ici_top]; rw [principal_singleton]
  have hL := L.le_atTop
have hL' : ∅ ∉ L.filter := empty_mem_iff_bot.not.mpr NeBot.ne_bot.ne'
  cases L with | mk F =>
  simp only [unconditional, hAtTop] at *
  congr 1
  refine eq_of_le_of_ge hL (pure_le_iff.mpr ?_)
  contrapose! hL'
  obtain ⟨s, hs, hs'⟩ := hL'
  simpa [inter_singleton_eq_empty.mpr hs'] using inter_mem hs (le_pure_iff.mp hL)

section conditionalTop

variable [Preorder β] [LocallyFiniteOrder β]

/--
Definition of `conditional` / `conditional` 的定义

English:
definition conditional
  signature: : SummationFilter β where
  body: (atBot ×ˢ atTop).map (fun p => Finset.Icc p.1 p.2)

中文:
定义 conditional
  签名: : SummationFilter β where
  定义体: (atBot ×ˢ atTop).map (fun p => Finset.Icc p.1 p.2)
-/
@[simps] def conditional : SummationFilter β where
  filter := (atBot ×ˢ atTop).map (fun p => Finset.Icc p.1 p.2)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (conditional β).LeAtTop
  body: ⟨support_eq_univ_iff.mp by
  simpa [eq_univ_iff_forall, support, -eventually_and]
    using! fun x => prod_mem_prod (eventually_le_atBot x) (eventually_ge_atTop x)⟩

中文:
实例 :
  签名: (conditional β).LeAtTop
  定义体: ⟨support_eq_univ_iff.mp by
  simpa [eq_univ_iff_forall, support, -eventually_and]
    using! fun x => prod_mem_prod (eventually_le_atBot x) (eventually_ge_atTop x)⟩

Depends on / 依赖: eq_univ_iff_forall, eventually_and, eventually_ge_atTop, eventually_le_atBot, prod_mem_prod, support, support_eq_univ_iff, support_eq_univ_iff.mp
-/
instance : (conditional β).LeAtTop := ⟨support_eq_univ_iff.mp by
  simpa [eq_univ_iff_forall, support, -eventually_and]
    using! fun x => prod_mem_prod (eventually_le_atBot x) (eventually_ge_atTop x)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: β] [IsDirectedOrder β] [IsCodirectedOrder β] : (conditional β).NeBot
  body: ⟨by rw [conditional_filter]; infer_instance⟩

中文:
实例 [Nonempty
  签名: β] [IsDirectedOrder β] [IsCodirectedOrder β] : (conditional β).NeBot
  定义体: ⟨by rw [conditional_filter]; infer_instance⟩

Depends on / 依赖: conditional_filter, infer_instance
-/
instance [Nonempty β] [IsDirectedOrder β] [IsCodirectedOrder β] : (conditional β).NeBot :=
  ⟨by rw [conditional_filter]; infer_instance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCountablyGenerated
  signature: (atTop : Filter β)] [IsCountablyGenerated (atBot : Filter β)] :
  body: map.isCountablyGenerated ..

中文:
实例 [IsCountablyGenerated
  签名: (atTop : Filter β)] [IsCountablyGenerated (atBot : Filter β)] :
  定义体: map.isCountablyGenerated ..

Depends on / 依赖: isCountablyGenerated, map.isCountablyGenerated
-/
instance [IsCountablyGenerated (atTop : Filter β)] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (conditional β).filter :=
  map.isCountablyGenerated ..

/-- When `β` has a bottom element, `conditional β` is given by limits over finite intervals
`{y | y ≤ x}` as `x → atTop`. -/
@[simp high] -- want this to be prioritized over `conditional_filter` when they both apply
/--
lemma `conditional_filter_eq_map_Iic` / 引理 `conditional_filter_eq_map_Iic`

English:
lemma conditional_filter_eq_map_Iic
  given: {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderBot γ]
  proof: by
  simp [isBot_bot.atBot_eq, comp_def, Finset.Icc_bot]

中文:
引理 conditional_filter_eq_map_Iic
  条件: {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderBot γ]
  证明: by
  simp [isBot_bot.atBot_eq, comp_def, Finset.Icc_bot]

Depends on / 依赖: Finset, Finset.Icc_bot, Icc_bot, atBot_eq, comp_def, isBot_bot, isBot_bot.atBot_eq
-/
lemma conditional_filter_eq_map_Iic {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderBot γ] :
    (conditional γ).filter = atTop.map Finset.Iic := by
  simp [isBot_bot.atBot_eq, comp_def, Finset.Icc_bot]

/-- When `β` has a top element, `conditional β` is given by limits over finite intervals
`{y | x ≤ y}` as `x → atBot`. -/
@[simp high] -- want this to be prioritized over `conditional_filter` when they both apply
/--
lemma `conditional_filter_eq_map_Ici` / 引理 `conditional_filter_eq_map_Ici`

English:
lemma conditional_filter_eq_map_Ici
  given: {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderTop γ]
  proof: by
  simp [isTop_top.atTop_eq, comp_def, Finset.Icc_top]

中文:
引理 conditional_filter_eq_map_Ici
  条件: {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderTop γ]
  证明: by
  simp [isTop_top.atTop_eq, comp_def, Finset.Icc_top]

Depends on / 依赖: Finset, Finset.Icc_top, Icc_top, atTop_eq, comp_def, isTop_top, isTop_top.atTop_eq
-/
lemma conditional_filter_eq_map_Ici {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderTop γ] :
    (conditional γ).filter = atBot.map Finset.Ici := by
  simp [isTop_top.atTop_eq, comp_def, Finset.Icc_top]

/-- Conditional summation over `ℕ` is given by limits of sums over `Finset.range n` as `n → ∞`. -/
@[simp high + 1] -- want this to be prioritized over `conditional_filter_eq_map_Ici`
/--
lemma `conditional_filter_eq_map_range` / 引理 `conditional_filter_eq_map_range`

English:
lemma conditional_filter_eq_map_range
  statement: (conditional Nat).filter = atTop.map Finset.range
  proof: by
  have (n : Nat) : Finset.Iic n = Finset.range (n + 1) := by ext x; simp [Nat.lt_succ_iff]
  simp only [conditional_filter_eq_map_Iic, funext this]
  apply le_antisymm <;>
      rw [← Tendsto] <;>
      simp only [tendsto_atTop', mem_map, mem_atTop_sets, mem_preimage] <;>
      rintro s ⟨a, ha⟩
 

中文:
引理 conditional_filter_eq_map_range
  结论: (conditional 自然数).filter = atTop.map Finset.range
  证明: by
  have (n : Nat) : Finset.Iic n = Finset.range (n + 1) := by ext x; simp [Nat.lt_succ_iff]
  simp only [conditional_filter_eq_map_Iic, funext this]
  apply le_antisymm <;>
      rw [← Tendsto] <;>
      simp only [tendsto_atTop', mem_map, mem_atTop_sets, mem_preimage] <;>
      rintro s ⟨a, ha⟩
 

Depends on / 依赖: Finset, Finset.Iic, Finset.range, Nat.lt_succ_iff, Tendsto, conditional_filter_eq_map_Iic, convert, le_antisymm, lt_succ_iff, mem_atTop_sets, mem_map, mem_preimage, tendsto_atTop
-/
lemma conditional_filter_eq_map_range : (conditional Nat).filter = atTop.map Finset.range := by
  have (n : Nat) : Finset.Iic n = Finset.range (n + 1) := by ext x; simp [Nat.lt_succ_iff]
  simp only [conditional_filter_eq_map_Iic, funext this]
  apply le_antisymm <;>
      rw [← Tendsto] <;>
      simp only [tendsto_atTop', mem_map, mem_atTop_sets, mem_preimage] <;>
      rintro s ⟨a, ha⟩
  · exact ⟨a + 1, fun b hb => ha (b + 1) (by lia)⟩
  · exact ⟨a + 1, fun b hb => by convert! ha (b - 1) (by lia); lia⟩

end conditionalTop

end examples

end SummationFilter
