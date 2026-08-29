/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.SupClosed

/-!
# Measurable spaces and measurable functions

This file provides properties of measurable spaces and the functions and isomorphisms between them.
The definition of a measurable space is in `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`.

A measurable space is a set equipped with a σ-algebra, a collection of subsets closed under
complementation and countable union. A function between measurable spaces is measurable if
the preimage of each measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order σ-algebras by writing `m₁ ≤ m₂`
if every set which is `m₁`-measurable is also `m₂`-measurable (that is, `m₁` is a subset of `m₂`).
In particular, any collection of subsets of `α` generates a smallest σ-algebra which contains
all of them. A function `f : α → β` induces a Galois connection between the lattices of σ-algebras
on `α` and `β`.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is defined in terms of the
Galois connection induced by `f`.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, dynkin system, π-λ theorem, π-system
-/

@[expose] public section

open Set MeasureTheory

universe uι

variable {α β γ : Type*} {ι : Sort uι} {s : Set α}

namespace MeasurableSpace

section Functors

variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α -> β} {g : β -> α}

/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : Set β` whose preimage under `f` is measurable. -/
@[instance_reducible]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (m : MeasurableSpace α)
  body: MeasurableSet[m] f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl _ hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using! m.measurableSet_iUnion _ hf

中文:
定义 map
  签名: (f : α -> β) (m : 可测空间 α)
  定义体: MeasurableSet[m] f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl _ hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using! m.measurableSet_iUnion _ hf
-/
protected def map (f : α -> β) (m : MeasurableSpace α) : MeasurableSpace β where
MeasurableSet' s := MeasurableSet[m] f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl _ hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using! m.measurableSet_iUnion _ hf

/--
lemma `map_def` / 引理 `map_def`

English:
lemma map_def
  given: {s : Set β}
  statement: MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s)
  proof: Iff.rfl

@[simp]

中文:
引理 map_def
  条件: {s : 集合 β}
  结论: 可测集[m.map f] s ↔ 可测集[m] (f ⁻¹' s)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: m.map id = m
  proof: MeasurableSpace.ext fun _ => Iff.rfl

@[simp]

中文:
定理 map_id
  结论: m.map id = m
  证明: MeasurableSpace.ext fun _ => Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, MeasurableSpace, MeasurableSpace.ext
-/
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun _ => Iff.rfl

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {f : α -> β} {g : β -> γ}
  statement: (m.map f).map g = m.map (g ∘ f)
  proof: MeasurableSpace.ext fun _ => Iff.rfl

中文:
定理 map_comp
  条件: {f : α -> β} {g : β -> γ}
  结论: (m.map f).map g = m.map (g ∘ f)
  证明: MeasurableSpace.ext fun _ => Iff.rfl

Depends on / 依赖: Iff.rfl, MeasurableSpace, MeasurableSpace.ext
-/
theorem map_comp {f : α -> β} {g : β -> γ} : (m.map f).map g = m.map (g ∘ f) :=
  MeasurableSpace.ext fun _ => Iff.rfl

/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
@[instance_reducible]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : α -> β) (m : MeasurableSpace β)
  body: exists s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun _ ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measura

中文:
定义 comap
  签名: (f : α -> β) (m : 可测空间 β)
  定义体: exists s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun _ ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measura
-/
protected def comap (f : α -> β) (m : MeasurableSpace β) : MeasurableSpace α where
  MeasurableSet' s := exists s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun _ ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurableSet_iUnion _ fun i => (hs' i).left, by simp [hs']⟩

/--
lemma `measurableSet_comap` / 引理 `measurableSet_comap`

English:
lemma measurableSet_comap
  given: {m : MeasurableSpace β}
  proof: .rfl

中文:
引理 measurableSet_comap
  条件: {m : 可测空间 β}
  证明: .rfl
-/
lemma measurableSet_comap {m : MeasurableSpace β} :
    MeasurableSet[m.comap f] s ↔ exists s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s := .rfl

/--
theorem `comap_eq_generateFrom` / 定理 `comap_eq_generateFrom`

English:
theorem comap_eq_generateFrom
  given: (m : MeasurableSpace β) (f : α -> β)
  proof: (@generateFrom_measurableSet _ (.comap f m)).symm

@[simp]

中文:
定理 comap_eq_generateFrom
  条件: (m : 可测空间 β) (f : α -> β)
  证明: (@generateFrom_measurableSet _ (.comap f m)).symm

@[simp]

Depends on / 依赖: generateFrom_measurableSet
-/
theorem comap_eq_generateFrom (m : MeasurableSpace β) (f : α -> β) :
    m.comap f = generateFrom { t | exists s, MeasurableSet s ∧ f ⁻¹' s = t } :=
  (@generateFrom_measurableSet _ (.comap f m)).symm

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: m.comap id = m
  proof: MeasurableSpace.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩

@[simp]

中文:
定理 comap_id
  结论: m.comap id = m
  证明: MeasurableSpace.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩

@[simp]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.ext
-/
theorem comap_id : m.comap id = m :=
  MeasurableSpace.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩

@[simp]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: {f : β -> α} {g : γ -> β}
  statement: (m.comap f).comap g = m.comap (f ∘ g)
  proof: MeasurableSpace.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

中文:
定理 comap_comp
  条件: {f : β -> α} {g : γ -> β}
  结论: (m.comap f).comap g = m.comap (f ∘ g)
  证明: MeasurableSpace.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

Depends on / 依赖: MeasurableSpace, MeasurableSpace.ext
-/
theorem comap_comp {f : β -> α} {g : γ -> β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  MeasurableSpace.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

/--
theorem `comap_le_iff_le_map` / 定理 `comap_le_iff_le_map`

English:
theorem comap_le_iff_le_map
  given: {f : α -> β}
  statement: m'.comap f <= m ↔ m' <= m.map f
  proof: ⟨fun h _s hs => h _ ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ => heq ▸ h _ ht⟩

中文:
定理 comap_le_iff_le_map
  条件: {f : α -> β}
  结论: m'.comap f <= m ↔ m' <= m.map f
  证明: ⟨fun h _s hs => h _ ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ => heq ▸ h _ ht⟩
-/
theorem comap_le_iff_le_map {f : α -> β} : m'.comap f <= m ↔ m' <= m.map f :=
  ⟨fun h _s hs => h _ ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ => heq ▸ h _ ht⟩

/--
theorem `gc_comap_map` / 定理 `gc_comap_map`

English:
theorem gc_comap_map
  given: (f : α -> β)
  proof: fun _ _ =>
  comap_le_iff_le_map

中文:
定理 gc_comap_map
  条件: (f : α -> β)
  证明: fun _ _ =>
  comap_le_iff_le_map
-/
theorem gc_comap_map (f : α -> β) :
    GaloisConnection (MeasurableSpace.comap f) (MeasurableSpace.map f) := fun _ _ =>
  comap_le_iff_le_map

/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: (h : m₁ <= m₂)
  statement: m₁.map f <= m₂.map f
  proof: (gc_comap_map f).monotone_u h

@[gcongr]

中文:
定理 map_mono
  条件: (h : m₁ <= m₂)
  结论: m₁.map f <= m₂.map f
  证明: (gc_comap_map f).monotone_u h

@[gcongr]

Depends on / 依赖: gc_comap_map, monotone_u
-/
theorem map_mono (h : m₁ <= m₂) : m₁.map f <= m₂.map f :=
  (gc_comap_map f).monotone_u h

@[gcongr]
/--
theorem `monotone_map` / 定理 `monotone_map`

English:
theorem monotone_map
  statement: Monotone (MeasurableSpace.map f)
  proof: fun _ _ => map_mono

中文:
定理 monotone_map
  结论: 递增 (可测空间.map f)
  证明: fun _ _ => map_mono

Depends on / 依赖: map_mono
-/
theorem monotone_map : Monotone (MeasurableSpace.map f) := fun _ _ => map_mono

/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: (h : m₁ <= m₂)
  statement: m₁.comap g <= m₂.comap g
  proof: (gc_comap_map g).monotone_l h

@[gcongr]

中文:
定理 comap_mono
  条件: (h : m₁ <= m₂)
  结论: m₁.comap g <= m₂.comap g
  证明: (gc_comap_map g).monotone_l h

@[gcongr]

Depends on / 依赖: gc_comap_map, monotone_l
-/
theorem comap_mono (h : m₁ <= m₂) : m₁.comap g <= m₂.comap g :=
  (gc_comap_map g).monotone_l h

@[gcongr]
/--
theorem `monotone_comap` / 定理 `monotone_comap`

English:
theorem monotone_comap
  statement: Monotone (MeasurableSpace.comap g)
  proof: fun _ _ h => comap_mono h

@[simp]

中文:
定理 monotone_comap
  结论: 递增 (可测空间.comap g)
  证明: fun _ _ h => comap_mono h

@[simp]

Depends on / 依赖: comap_mono
-/
theorem monotone_comap : Monotone (MeasurableSpace.comap g) := fun _ _ h => comap_mono h

@[simp]
/--
theorem `comap_bot` / 定理 `comap_bot`

English:
theorem comap_bot
  statement: (⊥ : MeasurableSpace α).comap g = ⊥
  proof: (gc_comap_map g).l_bot

@[simp]

中文:
定理 comap_bot
  结论: (⊥ : 可测空间 α).comap g = ⊥
  证明: (gc_comap_map g).l_bot

@[simp]

Depends on / 依赖: gc_comap_map, l_bot
-/
theorem comap_bot : (⊥ : MeasurableSpace α).comap g = ⊥ :=
  (gc_comap_map g).l_bot

@[simp]
/--
theorem `comap_sup` / 定理 `comap_sup`

English:
theorem comap_sup
  statement: (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g
  proof: (gc_comap_map g).l_sup

@[simp]

中文:
定理 comap_sup
  结论: (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g
  证明: (gc_comap_map g).l_sup

@[simp]

Depends on / 依赖: gc_comap_map, l_sup
-/
theorem comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g :=
  (gc_comap_map g).l_sup

@[simp]
/--
theorem `comap_iSup` / 定理 `comap_iSup`

English:
theorem comap_iSup
  given: {m : ι -> MeasurableSpace α}
  statement: (⨆ i, m i).comap g = ⨆ i, (m i).comap g
  proof: (gc_comap_map g).l_iSup

@[simp]

中文:
定理 comap_iSup
  条件: {m : ι -> 可测空间 α}
  结论: (⨆ i, m i).comap g = ⨆ i, (m i).comap g
  证明: (gc_comap_map g).l_iSup

@[simp]

Depends on / 依赖: gc_comap_map, l_iSup
-/
theorem comap_iSup {m : ι -> MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_iSup

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  statement: (⊤ : MeasurableSpace α).map f = ⊤
  proof: (gc_comap_map f).u_top

@[simp]

中文:
定理 map_top
  结论: (⊤ : 可测空间 α).map f = ⊤
  证明: (gc_comap_map f).u_top

@[simp]

Depends on / 依赖: gc_comap_map, u_top
-/
theorem map_top : (⊤ : MeasurableSpace α).map f = ⊤ :=
  (gc_comap_map f).u_top

@[simp]
/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  statement: (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f
  proof: (gc_comap_map f).u_inf

@[simp]

中文:
定理 map_inf
  结论: (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f
  证明: (gc_comap_map f).u_inf

@[simp]

Depends on / 依赖: gc_comap_map, u_inf
-/
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf

@[simp]
/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  given: {m : ι -> MeasurableSpace α}
  statement: (⨅ i, m i).map f = ⨅ i, (m i).map f
  proof: (gc_comap_map f).u_iInf

中文:
定理 map_iInf
  条件: {m : ι -> 可测空间 α}
  结论: (⨅ i, m i).map f = ⨅ i, (m i).map f
  证明: (gc_comap_map f).u_iInf

Depends on / 依赖: gc_comap_map, u_iInf
-/
theorem map_iInf {m : ι -> MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_iInf

/--
theorem `comap_map_le` / 定理 `comap_map_le`

English:
theorem comap_map_le
  statement: (m.map f).comap f <= m
  proof: (gc_comap_map f).l_u_le _

中文:
定理 comap_map_le
  结论: (m.map f).comap f <= m
  证明: (gc_comap_map f).l_u_le _

Depends on / 依赖: gc_comap_map, l_u_le
-/
theorem comap_map_le : (m.map f).comap f <= m :=
  (gc_comap_map f).l_u_le _

/--
theorem `le_map_comap` / 定理 `le_map_comap`

English:
theorem le_map_comap
  statement: m <= (m.comap g).map g
  proof: (gc_comap_map g).le_u_l _

中文:
定理 le_map_comap
  结论: m <= (m.comap g).map g
  证明: (gc_comap_map g).le_u_l _

Depends on / 依赖: gc_comap_map, le_u_l
-/
theorem le_map_comap : m <= (m.comap g).map g :=
  (gc_comap_map g).le_u_l _

/--
theorem `map_comap_eq_of_surjective` / 定理 `map_comap_eq_of_surjective`

English:
theorem map_comap_eq_of_surjective
  given: (hg : Function.Surjective g)
  statement: (m.comap g).map g = m
  proof: by
  refine le_antisymm (fun S hS => ?_) le_map_comap
  rw [map_def]; rw [measurableSet_comap] at hS
  aesop

中文:
定理 map_comap_eq_of_surjective
  条件: (hg : 函数.满射 g)
  结论: (m.comap g).map g = m
  证明: by
  refine le_antisymm (fun S hS => ?_) le_map_comap
  rw [map_def]; rw [measurableSet_comap] at hS
  aesop

Depends on / 依赖: le_antisymm, le_map_comap, map_def, measurableSet_comap
-/
theorem map_comap_eq_of_surjective (hg : Function.Surjective g) : (m.comap g).map g = m := by
  refine le_antisymm (fun S hS => ?_) le_map_comap
  rw [map_def]; rw [measurableSet_comap] at hS
  aesop

end Functors

/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: {m} (b : β)
  statement: MeasurableSpace.map (fun _a : α => b) m = ⊤
  proof: eq_top_iff.2 fun s _ => by rw [map_def]; by_cases h : b in s <;> simp [h]

中文:
定理 map_const
  条件: {m} (b : β)
  结论: 可测空间.map (fun _a : α => b) m = ⊤
  证明: eq_top_iff.2 fun s _ => by rw [map_def]; by_cases h : b in s <;> simp [h]
-/
@[simp] theorem map_const {m} (b : β) : MeasurableSpace.map (fun _a : α => b) m = ⊤ :=
eq_top_iff.2 fun s _ => by rw [map_def]; by_cases h : b in s <;> simp [h]

/--
theorem `comap_const` / 定理 `comap_const`

English:
theorem comap_const
  given: {m} (b : β)
  statement: MeasurableSpace.comap (fun _a : α => b) m = ⊥
  proof: eq_bot_iff.2 by rintro _ ⟨s, -, rfl⟩; by_cases b in s <;> simp [*]

中文:
定理 comap_const
  条件: {m} (b : β)
  结论: 可测空间.comap (fun _a : α => b) m = ⊥
  证明: eq_bot_iff.2 by rintro _ ⟨s, -, rfl⟩; by_cases b in s <;> simp [*]
-/
@[simp] theorem comap_const {m} (b : β) : MeasurableSpace.comap (fun _a : α => b) m = ⊥ :=
eq_bot_iff.2 by rintro _ ⟨s, -, rfl⟩; by_cases b in s <;> simp [*]

/--
theorem `comap_generateFrom` / 定理 `comap_generateFrom`

English:
theorem comap_generateFrom
  given: {f : α -> β} {s : Set (Set β)}
  proof: le_antisymm
    (comap_le_iff_le_map.2 <|
generateFrom_le fun _t hts => GenerateMeasurable.basic _ mem_image_of_mem _ hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)

中文:
定理 comap_generateFrom
  条件: {f : α -> β} {s : 集合 (集合 β)}
  证明: le_antisymm
    (comap_le_iff_le_map.2 <|
generateFrom_le fun _t hts => GenerateMeasurable.basic _ mem_image_of_mem _ hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)

Depends on / 依赖: GenerateMeasurable, GenerateMeasurable.basic, comap_le_iff_le_map, generateFrom_le, le_antisymm, mem_image_of_mem
-/
theorem comap_generateFrom {f : α -> β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
generateFrom_le fun _t hts => GenerateMeasurable.basic _ mem_image_of_mem _ hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/--
theorem `measurable_iff_le_map` / 定理 `measurable_iff_le_map`

English:
theorem measurable_iff_le_map
  given: {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α -> β}
  proof: Iff.rfl

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map

中文:
定理 measurable_iff_le_map
  条件: {m₁ : 可测空间 α} {m₂ : 可测空间 β} {f : α -> β}
  证明: Iff.rfl

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map

Depends on / 依赖: Iff.rfl
-/
theorem measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α -> β} :
    Measurable f ↔ m₂ <= m₁.map f :=
  Iff.rfl

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map

/--
theorem `measurable_iff_comap_le` / 定理 `measurable_iff_comap_le`

English:
theorem measurable_iff_comap_le
  given: {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α -> β}
  proof: comap_le_iff_le_map.symm

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le

中文:
定理 measurable_iff_comap_le
  条件: {m₁ : 可测空间 α} {m₂ : 可测空间 β} {f : α -> β}
  证明: comap_le_iff_le_map.symm

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le

Depends on / 依赖: comap_le_iff_le_map, comap_le_iff_le_map.symm
-/
theorem measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α -> β} :
    Measurable f ↔ m₂.comap f <= m₁ :=
  comap_le_iff_le_map.symm

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le

/--
lemma `MeasurableSpace.comap_le_comap_of_eq_comp` / 引理 `MeasurableSpace.comap_le_comap_of_eq_comp`

English:
lemma MeasurableSpace.comap_le_comap_of_eq_comp
  statement: {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  proof: by
  rw [heq]; rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono mh.comap_le

中文:
引理 可测空间.comap_le_comap_of_eq_comp
  结论: {mβ : 可测空间 β} {mγ : 可测空间 γ}
  证明: by
  rw [heq]; rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono mh.comap_le

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap_comp, MeasurableSpace.comap_mono, comap_comp, comap_le, comap_mono, mh.comap_le
-/
lemma MeasurableSpace.comap_le_comap_of_eq_comp {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {f : α -> β} {g : α -> γ} (h : β -> γ) (mh : Measurable h) (heq : g = h ∘ f) :
    mγ.comap g <= mβ.comap f := by
  rw [heq]; rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono mh.comap_le

/--
theorem `comap_measurable` / 定理 `comap_measurable`

English:
theorem comap_measurable
  given: {m : MeasurableSpace β} (f : α -> β)
  statement: Measurable[m.comap f] f
  proof: fun s hs => ⟨s, hs, rfl⟩

中文:
定理 comap_measurable
  条件: {m : 可测空间 β} (f : α -> β)
  结论: 可测[m.comap f] f
  证明: fun s hs => ⟨s, hs, rfl⟩
-/
theorem comap_measurable {m : MeasurableSpace β} (f : α -> β) : Measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩

/--
lemma `measurable_comap_iff` / 引理 `measurable_comap_iff`

English:
lemma measurable_comap_iff
  statement: {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  proof: by
  simp [measurable_iff_comap_le]

中文:
引理 measurable_comap_iff
  结论: {mα : 可测空间 α} {mγ : 可测空间 γ}
  证明: by
  simp [measurable_iff_comap_le]

Depends on / 依赖: measurable_iff_comap_le
-/
lemma measurable_comap_iff {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
    {f : α -> β} {g : β -> γ} : Measurable[mα, mγ.comap g] f ↔ Measurable (g ∘ f) := by
  simp [measurable_iff_comap_le]

/--
lemma `measurable_comap_iff_right` / 引理 `measurable_comap_iff_right`

English:
lemma measurable_comap_iff_right
  statement: {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {g : α -> β}
  proof: by
  rw [measurable_iff_le_map]; rw [measurable_iff_le_map]; rw [← map_comp]; rw [map_comap_eq_of_surjective hg]

中文:
引理 measurable_comap_iff_right
  结论: {mβ : 可测空间 β} {mγ : 可测空间 γ} {g : α -> β}
  证明: by
  rw [measurable_iff_le_map]; rw [measurable_iff_le_map]; rw [← map_comp]; rw [map_comap_eq_of_surjective hg]

Depends on / 依赖: map_comap_eq_of_surjective, map_comp, measurable_iff_le_map
-/
lemma measurable_comap_iff_right {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {g : α -> β}
    {f : β -> γ} (hg : Function.Surjective g) : Measurable f ↔ Measurable[mβ.comap g] (f ∘ g) := by
  rw [measurable_iff_le_map]; rw [measurable_iff_le_map]; rw [← map_comp]; rw [map_comap_eq_of_surjective hg]

/--
theorem `Measurable.mono` / 定理 `Measurable.mono`

English:
theorem Measurable.mono
  statement: {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α -> β}
  proof: fun _t ht => ha _ hf hb _ ht

中文:
定理 可测.mono
  结论: {ma ma' : 可测空间 α} {mb mb' : 可测空间 β} {f : α -> β}
  证明: fun _t ht => ha _ hf hb _ ht
-/
theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α -> β}
    (hf : @Measurable α β ma mb f) (ha : ma <= ma') (hb : mb' <= mb) : @Measurable α β ma' mb' f :=
fun _t ht => ha _ hf hb _ ht

/--
lemma `Measurable.iSup'` / 引理 `Measurable.iSup'`

English:
lemma Measurable.iSup'
  statement: {mα : ι -> MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β} (i₀ : ι)
  proof: h.mono (le_iSup mα i₀) le_rfl

中文:
引理 可测.iSup'
  结论: {mα : ι -> 可测空间 α} {_ : 可测空间 β} {f : α -> β} (i₀ : ι)
  证明: h.mono (le_iSup mα i₀) le_rfl

Depends on / 依赖: h.mono, le_iSup, le_rfl
-/
lemma Measurable.iSup' {mα : ι -> MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β} (i₀ : ι)
    (h : Measurable[mα i₀] f) :
    Measurable[⨆ i, mα i] f :=
  h.mono (le_iSup mα i₀) le_rfl

/--
lemma `Measurable.sup_of_left` / 引理 `Measurable.sup_of_left`

English:
lemma Measurable.sup_of_left
  statement: {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β}
  proof: h.mono le_sup_left le_rfl

中文:
引理 可测.sup_of_left
  结论: {mα mα' : 可测空间 α} {_ : 可测空间 β} {f : α -> β}
  证明: h.mono le_sup_left le_rfl

Depends on / 依赖: h.mono, le_rfl, le_sup_left
-/
lemma Measurable.sup_of_left {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β}
    (h : Measurable[mα] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_left le_rfl

/--
lemma `Measurable.sup_of_right` / 引理 `Measurable.sup_of_right`

English:
lemma Measurable.sup_of_right
  statement: {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β}
  proof: h.mono le_sup_right le_rfl

中文:
引理 可测.sup_of_right
  结论: {mα mα' : 可测空间 α} {_ : 可测空间 β} {f : α -> β}
  证明: h.mono le_sup_right le_rfl

Depends on / 依赖: h.mono, le_rfl, le_sup_right
-/
lemma Measurable.sup_of_right {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β}
    (h : Measurable[mα'] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_right le_rfl

/--
theorem `measurable_id''` / 定理 `measurable_id''`

English:
theorem measurable_id''
  given: {m mα : MeasurableSpace α} (hm : m <= mα)
  statement: @Measurable α α mα m id
  proof: measurable_id.mono le_rfl hm

中文:
定理 measurable_id''
  条件: {m mα : 可测空间 α} (hm : m <= mα)
  结论: @可测 α α mα m id
  证明: measurable_id.mono le_rfl hm

Depends on / 依赖: le_rfl, measurable_id, measurable_id.mono
-/
theorem measurable_id'' {m mα : MeasurableSpace α} (hm : m <= mα) : @Measurable α α mα m id :=
  measurable_id.mono le_rfl hm

/--
theorem `measurable_from_top` / 定理 `measurable_from_top`

English:
theorem measurable_from_top
  given: [MeasurableSpace β] {f : α -> β}
  statement: Measurable[⊤] f
  proof: fun _ _ => trivial

中文:
定理 measurable_from_top
  条件: [可测空间 β] {f : α -> β}
  结论: 可测[⊤] f
  证明: fun _ _ => trivial
-/
theorem measurable_from_top [MeasurableSpace β] {f : α -> β} : Measurable[⊤] f := fun _ _ => trivial

/--
theorem `measurable_generateFrom` / 定理 `measurable_generateFrom`

English:
theorem measurable_generateFrom
  statement: [MeasurableSpace α] {s : Set (Set β)} {f : α -> β}
  proof: Measurable.of_le_map generateFrom_le h

中文:
定理 measurable_generateFrom
  结论: [可测空间 α] {s : 集合 (集合 β)} {f : α -> β}
  证明: Measurable.of_le_map generateFrom_le h

Depends on / 依赖: Measurable, Measurable.of_le_map, generateFrom_le, of_le_map
-/
theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α -> β}
    (h : forall t in s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
Measurable.of_le_map generateFrom_le h

/--
theorem `measurableSet_generateFrom_of_mem_supClosure` / 定理 `measurableSet_generateFrom_of_mem_supClosure`

English:
theorem measurableSet_generateFrom_of_mem_supClosure
  statement: {s : Set (Set α)} {t : Set α}
  proof: by
  rcases ht with ⟨P, hP, PC, rfl⟩
  rw [Finset.sup'_eq_sup]; rw [Finset.sup_id_set_eq_sUnion]
  exact MeasurableSet.sUnion (Finset.countable_toSet P)
    (fun s hs => measurableSet_generateFrom (PC hs))

中文:
定理 measurableSet_generateFrom_of_mem_supClosure
  结论: {s : 集合 (集合 α)} {t : 集合 α}
  证明: by
  rcases ht with ⟨P, hP, PC, rfl⟩
  rw [Finset.sup'_eq_sup]; rw [Finset.sup_id_set_eq_sUnion]
  exact MeasurableSet.sUnion (Finset.countable_toSet P)
    (fun s hs => measurableSet_generateFrom (PC hs))

Depends on / 依赖: Finset, Finset.countable_toSet, Finset.sup, Finset.sup_id_set_eq_sUnion, MeasurableSet, MeasurableSet.sUnion, _eq_sup, countable_toSet, measurableSet_generateFrom, sUnion, sup_id_set_eq_sUnion
-/
theorem measurableSet_generateFrom_of_mem_supClosure {s : Set (Set α)} {t : Set α}
    (ht : t in supClosure s) : MeasurableSet[generateFrom s] t := by
  rcases ht with ⟨P, hP, PC, rfl⟩
  rw [Finset.sup'_eq_sup]; rw [Finset.sup_id_set_eq_sUnion]
  exact MeasurableSet.sUnion (Finset.countable_toSet P)
    (fun s hs => measurableSet_generateFrom (PC hs))

variable {f g : α -> β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β]

@[nontriviality]
/--
theorem `Subsingleton.measurable` / 定理 `Subsingleton.measurable`

English:
theorem Subsingleton.measurable
  given: [Subsingleton α]
  statement: Measurable f
  proof: fun _ _ =>
  @Subsingleton.measurableSet α _ _ _

@[nontriviality, fun_prop]

中文:
定理 子单例.measurable
  条件: [子单例 α]
  结论: 可测 f
  证明: fun _ _ =>
  @Subsingleton.measurableSet α _ _ _

@[nontriviality, fun_prop]
-/
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun _ _ =>
  @Subsingleton.measurableSet α _ _ _

@[nontriviality, fun_prop]
/--
theorem `measurable_of_subsingleton_codomain` / 定理 `measurable_of_subsingleton_codomain`

English:
theorem measurable_of_subsingleton_codomain
  given: [Subsingleton β] (f : α -> β)
  statement: Measurable f
  proof: fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

@[to_additive (attr := fun_prop)]

中文:
定理 measurable_of_subsingleton_codomain
  条件: [子单例 β] (f : α -> β)
  结论: 可测 f
  证明: fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

@[to_additive (attr := fun_prop)]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, MeasurableSet.univ, Subsingleton, Subsingleton.set_cases, set_cases
-/
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α -> β) : Measurable f :=
  fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

@[to_additive (attr := fun_prop)]
/--
theorem `measurable_one` / 定理 `measurable_one`

English:
theorem measurable_one
  given: [One α]
  statement: Measurable (1 : β -> α)
  proof: @measurable_const _ _ _ _ 1

中文:
定理 measurable_one
  条件: [幺 α]
  结论: 可测 (1 : β -> α)
  证明: @measurable_const _ _ _ _ 1

Depends on / 依赖: measurable_const
-/
theorem measurable_one [One α] : Measurable (1 : β -> α) :=
  @measurable_const _ _ _ _ 1

/--
theorem `measurable_of_empty` / 定理 `measurable_of_empty`

English:
theorem measurable_of_empty
  given: [IsEmpty α] (f : α -> β)
  statement: Measurable f
  proof: Subsingleton.measurable

中文:
定理 measurable_of_empty
  条件: [是空 α] (f : α -> β)
  结论: 可测 f
  证明: Subsingleton.measurable

Depends on / 依赖: Subsingleton, Subsingleton.measurable, measurable
-/
theorem measurable_of_empty [IsEmpty α] (f : α -> β) : Measurable f :=
  Subsingleton.measurable

/--
theorem `measurable_of_empty_codomain` / 定理 `measurable_of_empty_codomain`

English:
theorem measurable_of_empty_codomain
  given: [IsEmpty β] (f : α -> β)
  statement: Measurable f
  proof: measurable_of_subsingleton_codomain f

中文:
定理 measurable_of_empty_codomain
  条件: [是空 β] (f : α -> β)
  结论: 可测 f
  证明: measurable_of_subsingleton_codomain f

Depends on / 依赖: measurable_of_subsingleton_codomain
-/
theorem measurable_of_empty_codomain [IsEmpty β] (f : α -> β) : Measurable f :=
  measurable_of_subsingleton_codomain f

/--
theorem `measurable_const'` / 定理 `measurable_const'`

English:
theorem measurable_const'
  given: {f : β -> α} (hf : forall x y, f x = f y)
  statement: Measurable f
  proof: by
  nontriviality β
  inhabit β
  convert! @measurable_const α β _ _ (f default) using 2
  apply hf

@[fun_prop]

中文:
定理 measurable_const'
  条件: {f : β -> α} (hf : 对任意 x y, f x = f y)
  结论: 可测 f
  证明: by
  nontriviality β
  inhabit β
  convert! @measurable_const α β _ _ (f default) using 2
  apply hf

@[fun_prop]

Depends on / 依赖: convert, inhabit, measurable_const, nontriviality
-/
theorem measurable_const' {f : β -> α} (hf : forall x y, f x = f y) : Measurable f := by
  nontriviality β
  inhabit β
  convert! @measurable_const α β _ _ (f default) using 2
  apply hf

@[fun_prop]
/--
theorem `measurable_natCast` / 定理 `measurable_natCast`

English:
theorem measurable_natCast
  given: [NatCast α] (n : Nat)
  statement: Measurable (n : β -> α)
  proof: @measurable_const α _ _ _ n

@[fun_prop]

中文:
定理 measurable_natCast
  条件: [自然数嵌入 α] (n : 自然数)
  结论: 可测 (n : β -> α)
  证明: @measurable_const α _ _ _ n

@[fun_prop]

Depends on / 依赖: measurable_const
-/
theorem measurable_natCast [NatCast α] (n : Nat) : Measurable (n : β -> α) :=
  @measurable_const α _ _ _ n

@[fun_prop]
/--
theorem `measurable_intCast` / 定理 `measurable_intCast`

English:
theorem measurable_intCast
  given: [IntCast α] (n : Int)
  statement: Measurable (n : β -> α)
  proof: @measurable_const α _ _ _ n

中文:
定理 measurable_intCast
  条件: [整数嵌入 α] (n : 整数)
  结论: 可测 (n : β -> α)
  证明: @measurable_const α _ _ _ n

Depends on / 依赖: measurable_const
-/
theorem measurable_intCast [IntCast α] (n : Int) : Measurable (n : β -> α) :=
  @measurable_const α _ _ _ n

/--
theorem `measurable_of_countable` / 定理 `measurable_of_countable`

English:
theorem measurable_of_countable
  given: [Countable α] [MeasurableSingletonClass α] (f : α -> β)
  proof: fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet

中文:
定理 measurable_of_countable
  条件: [可数 α] [MeasurableSingleton类 α] (f : α -> β)
  证明: fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet
-/
theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α -> β) :
    Measurable f := fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet

/--
theorem `measurable_of_finite` / 定理 `measurable_of_finite`

English:
theorem measurable_of_finite
  given: [Finite α] [MeasurableSingletonClass α] (f : α -> β)
  statement: Measurable f
  proof: measurable_of_countable f

中文:
定理 measurable_of_finite
  条件: [有限 α] [MeasurableSingleton类 α] (f : α -> β)
  结论: 可测 f
  证明: measurable_of_countable f

Depends on / 依赖: measurable_of_countable
-/
theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α -> β) : Measurable f :=
  measurable_of_countable f

end TypeclassMeasurableSpace

variable {m : MeasurableSpace α}

@[fun_prop]
/--
theorem `Measurable.iterate` / 定理 `Measurable.iterate`

English:
theorem Measurable.iterate
  given: {f : α -> α} (hf : Measurable f)
  statement: forall n, Measurable f^[n]

中文:
定理 可测.iterate
  条件: {f : α -> α} (hf : 可测 f)
  结论: 对任意 n, 可测 f^[n]
-/
theorem Measurable.iterate {f : α -> α} (hf : Measurable f) : forall n, Measurable f^[n]
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate hf n).comp hf

variable {mβ : MeasurableSpace β}

@[measurability]
/--
theorem `measurableSet_preimage` / 定理 `measurableSet_preimage`

English:
theorem measurableSet_preimage
  given: {t : Set β} (hf : Measurable f) (ht : MeasurableSet t)
  proof: hf ht

中文:
定理 measurableSet_preimage
  条件: {t : 集合 β} (hf : 可测 f) (ht : 可测集 t)
  证明: hf ht
-/
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

/--
theorem `MeasurableSet.preimage` / 定理 `MeasurableSet.preimage`

English:
theorem MeasurableSet.preimage
  given: {t : Set β} (ht : MeasurableSet t) (hf : Measurable f)
  proof: hf ht

@[fun_prop]

中文:
定理 可测集.原像
  条件: {t : 集合 β} (ht : 可测集 t) (hf : 可测 f)
  证明: hf ht

@[fun_prop]
-/
protected theorem MeasurableSet.preimage {t : Set β} (ht : MeasurableSet t) (hf : Measurable f) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

@[fun_prop]
/--
theorem `Measurable.piecewise` / 定理 `Measurable.piecewise`

English:
theorem Measurable.piecewise
  statement: {_ : DecidablePred (· in s)} (hs : MeasurableSet s)
  proof: fun t ht => by simpa [piecewise_preimage] using hs.ite (hf ht) (hg ht)

中文:
定理 可测.piecewise
  结论: {_ : DecidablePred (· in s)} (hs : 可测集 s)
  证明: fun t ht => by simpa [piecewise_preimage] using hs.ite (hf ht) (hg ht)
-/
protected theorem Measurable.piecewise {_ : DecidablePred (· in s)} (hs : MeasurableSet s)
    (hf : Measurable f) (hg : Measurable g) : Measurable (piecewise s f g) :=
  fun t ht => by simpa [piecewise_preimage] using hs.ite (hf ht) (hg ht)

/--
theorem `Measurable.ite` / 定理 `Measurable.ite`

English:
theorem Measurable.ite
  statement: {p : α -> Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
  proof: Measurable.piecewise hp hf hg

@[fun_prop]

中文:
定理 可测.ite
  结论: {p : α -> 命题} {_ : DecidablePred p} (hp : 可测集 { a : α | p a })
  证明: Measurable.piecewise hp hf hg

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.piecewise, piecewise
-/
theorem Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg

@[fun_prop]
/--
theorem `Measurable.indicator` / 定理 `Measurable.indicator`

English:
theorem Measurable.indicator
  given: [Zero β] (hf : Measurable f) (hs : MeasurableSet s)
  proof: hf.piecewise hs measurable_const

中文:
定理 可测.indicator
  条件: [零 β] (hf : 可测 f) (hs : 可测集 s)
  证明: hf.piecewise hs measurable_const

Depends on / 依赖: hf.piecewise, measurable_const, piecewise
-/
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const

/--
lemma `measurable_indicator_const_iff` / 引理 `measurable_indicator_const_iff`

English:
lemma measurable_indicator_const_iff
  given: [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b]
  proof: by
  constructor <;> intro h
  · convert! h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [NeZero.ne b]
  · exact measurable_const.indicator h

@[to_additive (attr := measurability)]

中文:
引理 measurable_indicator_const_iff
  条件: [零 β] [MeasurableSingleton类 β] (b : β) [NeZero b]
  证明: by
  constructor <;> intro h
  · convert! h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [NeZero.ne b]
  · exact measurable_const.indicator h

@[to_additive (attr := measurability)]

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, NeZero, NeZero.ne, convert, indicator, measurable_const, measurable_const.indicator, singleton
-/
lemma measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b] :
    Measurable (s.indicator (fun (_ : α) => b)) ↔ MeasurableSet s := by
  constructor <;> intro h
  · convert! h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [NeZero.ne b]
  · exact measurable_const.indicator h

@[to_additive (attr := measurability)]
/--
theorem `measurableSet_mulSupport` / 定理 `measurableSet_mulSupport`

English:
theorem measurableSet_mulSupport
  given: [One β] [MeasurableSingletonClass β] (hf : Measurable f)
  proof: hf (measurableSet_singleton 1).compl

中文:
定理 measurableSet_mulSupport
  条件: [幺 β] [MeasurableSingleton类 β] (hf : 可测 f)
  证明: hf (measurableSet_singleton 1).compl

Depends on / 依赖: measurableSet_singleton
-/
theorem measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measurable f) :
    MeasurableSet (Function.mulSupport f) :=
  hf (measurableSet_singleton 1).compl

/--
theorem `Measurable.measurable_of_countable_ne` / 定理 `Measurable.measurable_of_countable_ne`

English:
theorem Measurable.measurable_of_countable_ne
  statement: [MeasurableSingletonClass α] (hf : Measurable f)
  proof: by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t inter { x | f x = g x }ᶜ union g ⁻¹' t inter { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t inter { x : α | f x = g x } = f ⁻¹' t inter { x : α | f x = g

中文:
定理 可测.measurable_of_countable_ne
  结论: [MeasurableSingleton类 α] (hf : 可测 f)
  证明: by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t inter { x | f x = g x }ᶜ union g ⁻¹' t inter { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t inter { x : α | f x = g x } = f ⁻¹' t inter { x : α | f x = g

Depends on / 依赖: contextual, h.measurableSet.of_compl, h.mono, inter_subset_right, inter_union_distrib_left, measurableSet, measurableSet.union, of_compl
-/
theorem Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : Measurable f)
    (h : Set.Countable { x | f x != g x }) : Measurable g := by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t inter { x | f x = g x }ᶜ union g ⁻¹' t inter { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t inter { x : α | f x = g x } = f ⁻¹' t inter { x : α | f x = g x } := by
    ext x
    simp +contextual
  rw [this]
  exact (hf ht).inter h.measurableSet.of_compl

end MeasurableFunctions

/--
Definition of `IsCountablySpanning` / `IsCountablySpanning` 的定义

English:
definition IsCountablySpanning
  signature: (C : Set (Set α))
  body: exists s : Nat -> Set α, (forall n, s n in C) ∧ ⋃ n, s n = univ

中文:
定义 IsCountablySpanning
  签名: (C : 集合 (集合 α))
  定义体: exists s : Nat -> Set α, (forall n, s n in C) ∧ ⋃ n, s n = univ
-/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  exists s : Nat -> Set α, (forall n, s n in C) ∧ ⋃ n, s n = univ

/--
theorem `isCountablySpanning_measurableSet` / 定理 `isCountablySpanning_measurableSet`

English:
theorem isCountablySpanning_measurableSet
  given: [MeasurableSpace α]
  proof: ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩

中文:
定理 isCountablySpanning_measurableSet
  条件: [可测空间 α]
  证明: ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, iUnion_const
-/
theorem isCountablySpanning_measurableSet [MeasurableSpace α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩

/--
lemma `IsCountablySpanning.prod` / 引理 `IsCountablySpanning.prod`

English:
lemma IsCountablySpanning.prod
  statement: {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
  proof: by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), ?_⟩
  rw [iUnion_unpair_prod]; rw [h2s]; rw [h2t]; rw [univ_prod_univ]

中文:
引理 IsCountablySpanning.乘积
  结论: {C : 集合 (集合 α)} {D : 集合 (集合 β)} (hC : IsCountablySpanning C)
  证明: by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), ?_⟩
  rw [iUnion_unpair_prod]; rw [h2s]; rw [h2t]; rw [univ_prod_univ]

Depends on / 依赖: iUnion_unpair_prod, mem_image2_of_mem, n.unpair, univ_prod_univ, unpair
-/
lemma IsCountablySpanning.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) : IsCountablySpanning (image2 (· ×ˢ ·) C D) := by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), ?_⟩
  rw [iUnion_unpair_prod]; rw [h2s]; rw [h2t]; rw [univ_prod_univ]
