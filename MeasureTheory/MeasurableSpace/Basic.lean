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

variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α → β} {g : β → α}

/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : Set β` whose preimage under `f` is measurable. -/
@[instance_reducible]
/-
**MeasurableSpace.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → MeasurableSpace α → Measurable
Space β
参数：α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_empty`：∀ {α : Type u_7} (self : Measurable
Space α), MeasurableSpace.MeasurableSet' self ∅

--- 原说明 ---
The forward image of a measurable space under a function. `map f m` contains the
 sets
  `s : Set β` whose preimage under `f` is measurable.
-/
protected def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β where
  MeasurableSet' s := MeasurableSet[m] <| f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl _ hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using! m.measurableSet_iUnion _ hf
/-
**MeasurableSpace.map_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl

@[simp]
/-
**MeasurableSpace.map_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_id : m.map id = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun _ => Iff.rfl

@[simp]
/-
**MeasurableSpace.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_comp {f : α -> β} {g : β -> γ} : (m.map f).map g = m.map (g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
  MeasurableSpace.ext fun _ => Iff.rfl

/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
@[instance_reducible]
/-
**MeasurableSpace.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → MeasurableSpace β → Measurable
Space α
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse image of a measurable space under a function. `comap f m` contains t
he sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`.
-/
protected def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α where
  MeasurableSet' s := ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun _ ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurableSet_iUnion _ fun i => (hs' i).left, by simp [hs']⟩
/-
**MeasurableSpace.measurableSet_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableSpace
`。
形式化陈述：measurableSet_comap {m : MeasurableSpace β} : MeasurableSet[m.comap f] s ↔
 exists s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma measurableSet_comap {m : MeasurableSpace β} :
    MeasurableSet[m.comap f] s ↔ ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s := .rfl
/-
**MeasurableSpace.comap_eq_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpa
ce`。
形式化陈述：comap_eq_generateFrom (m : MeasurableSpace β) (f : α -> β) : m.comap f = g
enerateFrom { t | exists s, MeasurableSet s ∧ f ⁻¹' s = t }
参数：m : MeasurableSpace β；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
-/
theorem comap_eq_generateFrom (m : MeasurableSpace β) (f : α → β) :
    m.comap f = generateFrom { t | ∃ s, MeasurableSet s ∧ f ⁻¹' s = t } :=
  (@generateFrom_measurableSet _ (.comap f m)).symm

@[simp]
/-
**MeasurableSpace.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_id : m.comap id = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
-/
theorem comap_id : m.comap id = m :=
  MeasurableSpace.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩

@[simp]
/-
**MeasurableSpace.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_comp {f : β -> α} {g : γ -> β} : (m.comap f).comap g = m.comap (f ∘ 
g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
-/
theorem comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  MeasurableSpace.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩
/-
**MeasurableSpace.comap_le_iff_le_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace
`。
形式化陈述：comap_le_iff_le_map {f : α -> β} : m'.comap f <= m ↔ m' <= m.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
  ⟨fun h _s hs => h _ ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ => heq ▸ h _ ht⟩
/-
**MeasurableSpace.gc_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：gc_comap_map (f : α -> β) : GaloisConnection (MeasurableSpace.comap f) (Me
asurableSpace.map f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.comap_le_iff_le_map`：comap_le_iff_le_map {f : α -> β} : 
m'.comap f <= m ↔ m' <= m.map f
-/
theorem gc_comap_map (f : α → β) :
    GaloisConnection (MeasurableSpace.comap f) (MeasurableSpace.map f) := fun _ _ =>
  comap_le_iff_le_map
/-
**MeasurableSpace.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_mono (h : m₁ <= m₂) : m₁.map f <= m₂.map f
参数：h : m₁ <= m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f :=
  (gc_comap_map f).monotone_u h

@[gcongr]
/-
**MeasurableSpace.monotone_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：monotone_map : Monotone (MeasurableSpace.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.map_mono`：map_mono (h : m₁ <= m₂) : m₁.map f <= m₂.map f
-/
theorem monotone_map : Monotone (MeasurableSpace.map f) := fun _ _ => map_mono
/-
**MeasurableSpace.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_mono (h : m₁ <= m₂) : m₁.comap g <= m₂.comap g
参数：h : m₁ <= m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g :=
  (gc_comap_map g).monotone_l h

@[gcongr]
/-
**MeasurableSpace.monotone_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：monotone_comap : Monotone (MeasurableSpace.comap g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.comap_mono`：comap_mono (h : m₁ <= m₂) : m₁.comap g <= m₂
.comap g
-/
theorem monotone_comap : Monotone (MeasurableSpace.comap g) := fun _ _ h => comap_mono h

@[simp]
/-
**MeasurableSpace.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_bot : (⊥ : MeasurableSpace α).comap g = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem comap_bot : (⊥ : MeasurableSpace α).comap g = ⊥ :=
  (gc_comap_map g).l_bot

@[simp]
/-
**MeasurableSpace.comap_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g :=
  (gc_comap_map g).l_sup

@[simp]
/-
**MeasurableSpace.comap_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_iSup {m : ι -> MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).
comap g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem comap_iSup {m : ι → MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_iSup

@[simp]
/-
**MeasurableSpace.map_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_top : (⊤ : MeasurableSpace α).map f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem map_top : (⊤ : MeasurableSpace α).map f = ⊤ :=
  (gc_comap_map f).u_top

@[simp]
/-
**MeasurableSpace.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf

@[simp]
/-
**MeasurableSpace.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：map_iInf {m : ι -> MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map 
f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem map_iInf {m : ι → MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_iInf
/-
**MeasurableSpace.comap_map_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：comap_map_le : (m.map f).comap f <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem comap_map_le : (m.map f).comap f ≤ m :=
  (gc_comap_map f).l_u_le _
/-
**MeasurableSpace.le_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：le_map_comap : m <= (m.comap g).map g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `MeasurableSpace.gc_comap_map`：gc_comap_map (f : α -> β) : GaloisConnecti
on (MeasurableSpace.comap f) (MeasurableSpace.map f)
-/
theorem le_map_comap : m ≤ (m.comap g).map g :=
  (gc_comap_map g).le_u_l _
/-
**MeasurableSpace.map_comap_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Measurab
leSpace`。
形式化陈述：map_comap_eq_of_surjective (hg : Function.Surjective g) : (m.comap g).map 
g = m
参数：hg : Function.Surjective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasurableSpace.measurableSet_comap`：measurableSet_comap {m : Measurable
Space β} : MeasurableSet[m.comap f] s ↔ exists s', MeasurableSet[m] s' ∧ f ⁻¹' s
' = s
· 使用引理 `MeasurableSpace.map_def`：map_def {s : Set β} : MeasurableSet[m.map f] s 
↔ MeasurableSet[m] (f ⁻¹' s)
· 使用定理 `MeasurableSpace.le_map_comap`：le_map_comap : m <= (m.comap g).map g
-/
theorem map_comap_eq_of_surjective (hg : Function.Surjective g) : (m.comap g).map g = m := by
  refine le_antisymm (fun S hS => ?_) le_map_comap
  rw [map_def, measurableSet_comap] at hS
  aesop

end Functors

/-
**MeasurableSpace.map_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} (b : β), Measurabl
eSpace.map (fun _a => b) m = ⊤
参数：b : β；fun _a => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableSpace.map_def`：map_def {s : Set β} : MeasurableSet[m.map f] s 
↔ MeasurableSet[m] (f ⁻¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `Set.preimage_const_of_notMem`：preimage_const_of_notMem {b : β} {s : Set 
β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] theorem map_const {m} (b : β) : MeasurableSpace.map (fun _a : α ↦ b) m = ⊤ :=
  eq_top_iff.2 <| fun s _ ↦ by rw [map_def]; by_cases h : b ∈ s <;> simp [h]
/-
**MeasurableSpace.comap_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace β} (b : β), Measurabl
eSpace.comap (fun _a => b) m = ⊥
参数：b : β；fun _a => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `Set.preimage_const_of_notMem`：preimage_const_of_notMem {b : β} {s : Set 
β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] theorem comap_const {m} (b : β) : MeasurableSpace.comap (fun _a : α => b) m = ⊥ :=
  eq_bot_iff.2 <| by rintro _ ⟨s, -, rfl⟩; by_cases b ∈ s <;> simp [*]
/-
**MeasurableSpace.comap_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`
。
形式化陈述：comap_generateFrom {f : α -> β} {s : Set (Set β)} : (generateFrom s).comap
 f = generateFrom (preimage f '' s)
参数：Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSpace.comap_le_iff_le_map`：comap_le_iff_le_map {f : α -> β} : 
m'.comap f <= m ↔ m' <= m.map f
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem comap_generateFrom {f : α → β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
      generateFrom_le fun _t hts => GenerateMeasurable.basic _ <| mem_image_of_mem _ <| hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/-
**measurable_iff_le_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f
 : α -> β} : Measurable f ↔ m₂ <= m₁.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂ ≤ m₁.map f :=
  Iff.rfl

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map
/-
**measurable_iff_comap_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} 
{f : α -> β} : Measurable f ↔ m₂.comap f <= m₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasurableSpace.comap_le_iff_le_map`：comap_le_iff_le_map {f : α -> β} : 
m'.comap f <= m ↔ m' <= m.map f
-/
theorem measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂.comap f ≤ m₁ :=
  comap_le_iff_le_map.symm

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le

/-- If `g = h ∘ f`, then the sigma-algebra generated by `g` is
smaller than the one generated by `f`. -/
/-
**MeasurableSpace.comap_le_comap_of_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSpace.comap_le_comap_of_eq_comp {mβ : MeasurableSpace β} {mγ : M
easurableSpace γ} {f : α -> β} {g : α -> γ} (h : β -> γ) (mh : Measurable h) (he
q : g = h ∘ f) : mγ.comap g <= mβ.comap f
参数：h : β -> γ；mh : Measurable h；heq : g = h ∘ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
· 使用定理 `MeasurableSpace.comap_mono`：comap_mono (h : m₁ <= m₂) : m₁.comap g <= m₂
.comap g
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…

--- 原说明 ---
If `g = h ∘ f`, then the sigma-algebra generated by `g` is
smaller than the one generated by `f`.
-/
lemma MeasurableSpace.comap_le_comap_of_eq_comp {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {f : α → β} {g : α → γ} (h : β → γ) (mh : Measurable h) (heq : g = h ∘ f) :
    mγ.comap g ≤ mβ.comap f := by
  rw [heq, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono mh.comap_le
/-
**comap_measurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_measurable {m : MeasurableSpace β} (f : α -> β) : Measurable[m.comap
 f] f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_measurable {m : MeasurableSpace β} (f : α → β) : Measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩
/-
**measurable_comap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_comap_iff {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {f 
: α -> β} {g : β -> γ} : Measurable[mα, mγ.comap g] f ↔ Measurable (g ∘ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma measurable_comap_iff {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
    {f : α → β} {g : β → γ} : Measurable[mα, mγ.comap g] f ↔ Measurable (g ∘ f) := by
  simp [measurable_iff_comap_le]
/-
**measurable_comap_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_comap_iff_right {mβ : MeasurableSpace β} {mγ : MeasurableSpace 
γ} {g : α -> β} {f : β -> γ} (hg : Function.Surjective g) : Measurable f ↔ Measu
rable[mβ.comap g] (f ∘ g)
参数：hg : Function.Surjective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_iff_le_map`：measurable_iff_le_map {m₁ : MeasurableSpace α} {m
₂ : MeasurableSpace β} {f : α -> β} : Measurable f ↔ m₂ <= m₁.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.map_comp`：map_comp {f : α -> β} {g : β -> γ} : (m.map f)
.map g = m.map (g ∘ f)
· 使用定理 `MeasurableSpace.map_comap_eq_of_surjective`：map_comap_eq_of_surjective (
hg : Function.Surjective g) : (m.comap g).map g = m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma measurable_comap_iff_right {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {g : α → β}
    {f : β → γ} (hg : Function.Surjective g) : Measurable f ↔ Measurable[mβ.comap g] (f ∘ g) := by
  rw [measurable_iff_le_map, measurable_iff_le_map, ← map_comp, map_comap_eq_of_surjective hg]
/-
**Measurable.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} 
{f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') (hb : mb' <= mb) : 
@Measurable α β ma' mb' f
参数：hf : @Measurable α β ma mb f；ha : ma <= ma'；hb : mb' <= mb。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α → β}
    (hf : @Measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) : @Measurable α β ma' mb' f :=
  fun _t ht => ha _ <| hf <| hb _ ht
/-
**Measurable.iSup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.iSup' {mα : ι -> MeasurableSpace α} {_ : MeasurableSpace β} {f 
: α -> β} (i₀ : ι) (h : Measurable[mα i₀] f) : Measurable[⨆ i, mα i] f
参数：i₀ : ι；h : Measurable[mα i₀] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Measurable.iSup' {mα : ι → MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β} (i₀ : ι)
    (h : Measurable[mα i₀] f) :
    Measurable[⨆ i, mα i] f :=
  h.mono (le_iSup mα i₀) le_rfl
/-
**Measurable.sup_of_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.sup_of_left {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β
} {f : α -> β} (h : Measurable[mα] f) : Measurable[mα ⊔ mα'] f
参数：h : Measurable[mα] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Measurable.sup_of_left {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    (h : Measurable[mα] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_left le_rfl
/-
**Measurable.sup_of_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.sup_of_right {mα mα' : MeasurableSpace α} {_ : MeasurableSpace 
β} {f : α -> β} (h : Measurable[mα'] f) : Measurable[mα ⊔ mα'] f
参数：h : Measurable[mα'] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Measurable.sup_of_right {mα mα' : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    (h : Measurable[mα'] f) :
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_right le_rfl
/-
**measurable_id''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= mα) : @Measurable α 
α mα m id
参数：hm : m <= mα。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem measurable_id'' {m mα : MeasurableSpace α} (hm : m ≤ mα) : @Measurable α α mα m id :=
  measurable_id.mono le_rfl hm
/-
**measurable_from_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_from_top [MeasurableSpace β] {f : α -> β} : Measurable[⊤] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem measurable_from_top [MeasurableSpace β] {f : α → β} : Measurable[⊤] f := fun _ _ => trivial
/-
**measurable_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α -> β}
 (h : forall t in s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom 
s) f
参数：Set β；h : forall t in s, MeasurableSet (f ⁻¹' t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_le_map`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSp
ace α} {m₂ : MeasurableSpace β} {f : α → β},   m₂ ≤ MeasurableSpace.map f m₁ → M
easurable …
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
-/
theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le h
/-
**measurableSet_generateFrom_of_mem_supClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_generateFrom_of_mem_supClosure {s : Set (Set α)} {t : Set α}
 (ht : t in supClosure s) : MeasurableSet[generateFrom s] t
参数：Set α；ht : t in supClosure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.sup_id_set_eq_sUnion`：sup_id_set_eq_sUnion (s : Finset (Set α)) :
 s.sup id = ⋃₀ ↑s
· 使用定理 `MeasurableSet.sUnion`：∀ {α : Type u_1} {m : MeasurableSpace α} {s : Set 
(Set α)},   s.Countable → (∀ t ∈ s, MeasurableSet t) → MeasurableSet (⋃₀ s)
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
-/
theorem measurableSet_generateFrom_of_mem_supClosure {s : Set (Set α)} {t : Set α}
    (ht : t ∈ supClosure s) : MeasurableSet[generateFrom s] t := by
  rcases ht with ⟨P, hP, PC, rfl⟩
  rw [Finset.sup'_eq_sup, Finset.sup_id_set_eq_sUnion]
  exact MeasurableSet.sUnion (Finset.countable_toSet P)
    (fun s hs ↦ measurableSet_generateFrom (PC hs))

variable {f g : α → β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β]

@[nontriviality]
/-
**Subsingleton.measurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.measurable [Subsingleton α] : Measurable f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.measurableSet`：Subsingleton.measurableSet [Subsingleton α] 
{s : Set α} : MeasurableSet s
-/
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun _ _ =>
  @Subsingleton.measurableSet α _ _ _

@[nontriviality, fun_prop]
/-
**measurable_of_subsingleton_codomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_subsingleton_codomain [Subsingleton β] (f : α -> β) : Measur
able f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.set_cases`：set_cases {p : Set α -> Prop} (h0 : p ∅) (h1 : p
 univ) (s) : p s
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α → β) : Measurable f :=
  fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

@[to_additive (attr := fun_prop)]
/-
**measurable_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_one [One α] : Measurable (1 : β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem measurable_one [One α] : Measurable (1 : β → α) :=
  @measurable_const _ _ _ _ 1
/-
**measurable_of_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_empty [IsEmpty α] (f : α -> β) : Measurable f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.measurable`：Subsingleton.measurable [Subsingleton α] : Meas
urable f
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
-/
theorem measurable_of_empty [IsEmpty α] (f : α → β) : Measurable f :=
  Subsingleton.measurable
/-
**measurable_of_empty_codomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_empty_codomain [IsEmpty β] (f : α -> β) : Measurable f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_subsingleton_codomain`：measurable_of_subsingleton_codomain
 [Subsingleton β] (f : α -> β) : Measurable f
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
-/
theorem measurable_of_empty_codomain [IsEmpty β] (f : α → β) : Measurable f :=
  measurable_of_subsingleton_codomain f

/-- A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This version works
for functions between empty types. -/
/-
**measurable_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_const' {f : β -> α} (hf : forall x y, f x = f y) : Measurable f
参数：hf : forall x y, f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a

--- 原说明 ---
A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This ve
rsion works
for functions between empty types.
-/
theorem measurable_const' {f : β → α} (hf : ∀ x y, f x = f y) : Measurable f := by
  nontriviality β
  inhabit β
  convert! @measurable_const α β _ _ (f default) using 2
  apply hf

@[fun_prop]
/-
**measurable_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_natCast [NatCast α] (n : Nat) : Measurable (n : β -> α)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem measurable_natCast [NatCast α] (n : ℕ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n

@[fun_prop]
/-
**measurable_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_intCast [IntCast α] (n : Int) : Measurable (n : β -> α)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem measurable_intCast [IntCast α] (n : ℤ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n
/-
**measurable_of_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α 
-> β) : Measurable f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
    Measurable f := fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet
/-
**measurable_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α -> β) 
: Measurable f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_countable`：measurable_of_countable [Countable α] [Measurab
leSingletonClass α] (f : α -> β) : Measurable f
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
-/
theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  measurable_of_countable f

end TypeclassMeasurableSpace

variable {m : MeasurableSpace α}

@[fun_prop]
/-
**Measurable.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → α}, Measurable f → ∀ (n 
: ℕ), Measurable f^[n]
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Measurable.iterate {f : α → α} (hf : Measurable f) : ∀ n, Measurable f^[n]
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate hf n).comp hf

variable {mβ : MeasurableSpace β}

@[measurability]
/-
**measurableSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet
 t) : MeasurableSet (f ⁻¹' t)
参数：hf : Measurable f；ht : MeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht
/-
**MeasurableSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : MeasurableSpace α} {mβ : 
MeasurableSpace β} {t : Set β},   MeasurableSet t → Measurable f → MeasurableSet
 (f ⁻¹' t)
参数：f ⁻¹' t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem MeasurableSet.preimage {t : Set β} (ht : MeasurableSet t) (hf : Measurable f) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

@[fun_prop]
/-
**Measurable.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g : α → β} {m : MeasurableS
pace α} {mβ : MeasurableSpace β}   {x : DecidablePred fun x => x ∈ s}, Measurabl
eSet s → Measurable f → Measurable g → Measurable (s.piecewise f g)
参数：s.piecewise f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_preimage`：piecewise_preimage (f g : α -> β) (t) : s.piecew
ise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
· 使用定理 `MeasurableSet.ite`：∀ {α : Type u_1} {m : MeasurableSpace α} {t s₁ s₂ : S
et α},   MeasurableSet t → MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (
t.ite s…
-/
protected theorem Measurable.piecewise {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s)
    (hf : Measurable f) (hg : Measurable g) : Measurable (piecewise s f g) :=
  fun t ht => by simpa [piecewise_preimage] using hs.ite (hf ht) (hg ht)

/-- This is slightly different from `Measurable.piecewise`. It can be used to show
`Measurable (ite (x=0) 0 1)` by
`exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const`,
but replacing `Measurable.ite` by `Measurable.piecewise` in that example proof does not work. -/
/-
**Measurable.ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp : MeasurableSet {
 a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Measurable fun x => it
e (p x) (f x) (g x)
参数：hp : MeasurableSet { a : α | p a }；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.piecewise`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g :
 α → β} {m : MeasurableSpace α} {mβ : MeasurableSpace β}   {x : DecidablePred fu
n x => x ∈…

--- 原说明 ---
This is slightly different from `Measurable.piecewise`. It can be used to show
`Measurable (ite (x=0) 0 1)` by
`exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_co
nst`,
but replacing `Measurable.ite` by `Measurable.piecewise` in that example proof d
oes not work.
-/
theorem Measurable.ite {p : α → Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg

@[fun_prop]
/-
**Measurable.indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
 Measurable (s.indicator f)
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.piecewise`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g :
 α → β} {m : MeasurableSpace α} {mβ : MeasurableSpace β}   {x : DecidablePred fu
n x => x ∈…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const

/-- The measurability of a set `A` is equivalent to the measurability of the indicator function
which takes a constant value `b ≠ 0` on a set `A` and `0` elsewhere. -/
/-
**measurable_indicator_const_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : 
β) [NeZero b] : Measurable (s.indicator (fun (_ : α) => b)) ↔ MeasurableSet s
参数：b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a

--- 原说明 ---
The measurability of a set `A` is equivalent to the measurability of the indicat
or function
which takes a constant value `b ≠ 0` on a set `A` and `0` elsewhere.
-/
lemma measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b] :
    Measurable (s.indicator (fun (_ : α) ↦ b)) ↔ MeasurableSet s := by
  constructor <;> intro h
  · convert! h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [NeZero.ne b]
  · exact measurable_const.indicator h

@[to_additive (attr := measurability)]
/-
**measurableSet_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measur
able f) : MeasurableSet (Function.mulSupport f)
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
theorem measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measurable f) :
    MeasurableSet (Function.mulSupport f) :=
  hf (measurableSet_singleton 1).compl

/-- If a function coincides with a measurable function outside of a countable set, it is
measurable. -/
/-
**Measurable.measurable_of_countable_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : M
easurable f) (h : Set.Countable { x | f x != g x }) : Measurable g
参数：hf : Measurable f；h : Set.Countable { x | f x != g x }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s

--- 原说明 ---
If a function coincides with a measurable function outside of a countable set, i
t is
measurable.
-/
theorem Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : Measurable f)
    (h : Set.Countable { x | f x ≠ g x }) : Measurable g := by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t ∩ { x | f x = g x }ᶜ ∪ g ⁻¹' t ∩ { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } := by
    ext x
    simp +contextual
  rw [this]
  exact (hf ht).inter h.measurableSet.of_compl

end MeasurableFunctions

/-- We say that a collection of sets is countably spanning if a countable subset spans the
whole type. This is a useful condition in various parts of measure theory. For example, it is
a needed condition to show that the product of two collections generate the product sigma algebra,
see `generateFrom_prod_eq`. -/
/-
**IsCountablySpanning** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCountablySpanning (C : Set (Set α)) : Prop
参数：C : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a collection of sets is countably spanning if a countable subset spa
ns the
whole type. This is a useful condition in various parts of measure theory. For e
xample, it is
a needed condition to show that the product of two collections generate the prod
uct sigma algebra,
see `generateFrom_prod_eq`.
-/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ ⋃ n, s n = univ
/-
**isCountablySpanning_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablySpanning_measurableSet [MeasurableSpace α] : IsCountablySpannin
g { s : Set α | MeasurableSet s }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem isCountablySpanning_measurableSet [MeasurableSpace α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩

/-- Rectangles of countably spanning sets are countably spanning. -/
/-
**IsCountablySpanning.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCountablySpanning.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsCount
ablySpanning C) (hD : IsCountablySpanning D) : IsCountablySpanning (image2 (· ×ˢ
 ·) C D)
参数：Set α；Set β；hC : IsCountablySpanning C；hD : IsCountablySpanning D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_unpair_prod`：iUnion_unpair_prod {α β} {s : Nat -> Set α} {t :
 Nat -> Set β} : ⋃ n : Nat, s n.unpair.fst ×ˢ t n.unpair.snd = (⋃ n, s n) ×ˢ ⋃ n
, t n
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ

--- 原说明 ---
Rectangles of countably spanning sets are countably spanning.
-/
lemma IsCountablySpanning.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) : IsCountablySpanning (image2 (· ×ˢ ·) C D) := by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), ?_⟩
  rw [iUnion_unpair_prod, h2s, h2t, univ_prod_univ]
