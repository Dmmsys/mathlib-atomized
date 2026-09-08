/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser
-/
module

public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.ModularLattice
public import Mathlib.Tactic.FinCases

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `Finset.SupIndep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `sSupIndep s`: a set of elements are supremum independent.
* `iSupIndep f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `Finset.supIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.sSupIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.iSupIndep_iff_pairwiseDisjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `Finset.SupIndep.pairwiseDisjoint`
  * `sSupIndep.pairwiseDisjoint`
  * `iSupIndep.pairwiseDisjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/

@[expose] public section


variable {α β ι ι' : Type*}

/-! ### On lattices with a bottom element, via `Finset.sup` -/


namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
/-
**Finset.SupIndep** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：SupIndep (s : Finset ι) (f : ι -> α) : Prop
参数：s : Finset ι；f : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Supremum independence of finite sets. We avoid the "obvious" definition using `s
.erase i`
because `erase` would require decidable equality on `ι`.
-/
def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)

variable {s t : Finset ι} {f g : ι → α} {i : ι}

/-- The RHS looks like the definition of `iSupIndep`. -/
/-
**Finset.supIndep_iff_disjoint_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_iff_disjoint_erase [DecidableEq ι] : s.SupIndep f ↔ forall i in s
, Disjoint (f i) ((s.erase i).sup f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b

--- 原说明 ---
The RHS looks like the definition of `iSupIndep`.
-/
theorem supIndep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs _ hi => hs (erase_subset _ _) hi (notMem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

/-- If both the index type and the lattice have decidable equality,
then the `SupIndep` predicate is decidable.

TODO: speedup the definition and drop the `[DecidableEq ι]` assumption
by iterating over the pairs `(a, t)` such that `s = Finset.cons a t _`
using something like `List.eraseIdx`
or by generating both `f i` and `(s.erase i).sup f` in one loop over `s`.
Yet another possible optimization is to precompute partial suprema of `f`
over the inits and tails of the list representing `s`,
store them in 2 `Array`s,
then compute each `sup` in 1 operation. -/
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If both the index type and the lattice have decidable equality,
then the `SupIndep` predicate is decidable.

TODO: speedup the definition and drop the `[DecidableEq ι]` assumption
by iterating over the pairs `(a, t)` such that `s = Finset.cons a t _`
using something like `List.eraseIdx`
or by generating both `f i` and `(s.erase i).sup f` in one loop over `s`.
Yet another possible optimization is to precompute partial suprema of `f`
over the inits and tails of the list representing `s`,
store them in 2 `Array`s,
then compute each `sup` in 1 operation.
-/
instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) :=
  have : ∀ i, Decidable (Disjoint (f i) ((s.erase i).sup f)) := fun _ ↦
    decidable_of_iff _ disjoint_iff.symm
  decidable_of_iff _ supIndep_iff_disjoint_erase.symm
/-
**Finset.SupIndep.subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [inst_1 : OrderBot α] {
s t : Finset ι} {f : ι → α},   t.SupIndep f → s ⊆ t → s.SupIndep f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun _ hu _ hi =>
  ht (hu.trans h) (h hi)
/-
**Finset.SupIndep.mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [inst_1 : OrderBot α] {
s : Finset ι} {f g : ι → α},   s.SupIndep f → (∀ i ∈ s, g i ≤ f i) → s.SupIndep 
g
参数：∀ i ∈ s, g i ≤ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
-/
lemma SupIndep.mono (hf : s.SupIndep f) (h : ∀ i ∈ s, g i ≤ f i) : s.SupIndep g :=
  fun _ ht j hj htj ↦ (hf ht hj htj).mono (h j hj) (sup_mono_fun fun b a ↦ h b (ht a))

@[simp, grind ←]
/-
**Finset.supIndep_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_empty (f : ι -> α) : (∅ : Finset ι).SupIndep f
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem supIndep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha =>
  (notMem_empty a ha).elim

@[simp, grind ←]
/-
**Finset.supIndep_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_singleton (i : ι) (f : ι -> α) : ({i} : Finset ι).SupIndep f
参数：i : ι；f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_empty_of_ssubset_singleton`：eq_empty_of_ssubset_singleton {s :
 Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `disjoint_bot_right`：disjoint_bot_right : Disjoint a ⊥
-/
theorem supIndep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f :=
  fun s hs j hji hj => by
    rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
    exact disjoint_bot_right
/-
**Finset.SupIndep.pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [inst_1 : OrderBot α] {
s : Finset ι} {f : ι → α},   s.SupIndep f → (↑s).PairwiseDisjoint f
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
-/
theorem SupIndep.pairwiseDisjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f :=
  fun _ ha _ hb hab =>
    sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| notMem_singleton.2 hab
/-
**Finset.SupIndep.le_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [inst_1 : OrderBot α] {
s t : Finset ι} {f : ι → α} {i : ι},   s.SupIndep f → t ⊆ s → i ∈ s → (∀ (i : ι)
, f i ≠ ⊥) → (f i ≤ t.sup f ↔ i ∈ t)
参数：∀ (i : ι), f i ≠ ⊥；f i ≤ t.sup f ↔ i ∈ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem SupIndep.le_sup_iff (hs : s.SupIndep f) (hts : t ⊆ s) (hi : i ∈ s) (hf : ∀ i, f i ≠ ⊥) :
    f i ≤ t.sup f ↔ i ∈ t := by
  refine ⟨fun h => ?_, le_sup⟩
  by_contra hit
  exact hf i (disjoint_self.1 <| (hs hts hi hit).mono_right h)
/-
**Finset.SupIndep.antitone_fun** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [inst_1 : OrderBot α] {
s : Finset ι} {f g : ι → α},   (∀ x ∈ s, f x ≤ g x) → s.SupIndep g → s.SupIndep 
f
参数：∀ x ∈ s, f x ≤ g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
-/
theorem SupIndep.antitone_fun {g : ι → α} (hle : ∀ x ∈ s, f x ≤ g x) (h : s.SupIndep g) :
    s.SupIndep f := fun _t hts i his hit ↦
  (h hts his hit).mono (hle i his) <| Finset.sup_mono_fun fun x hx ↦ hle x <| hts hx
/-
**Finset.SupIndep.image** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4} [inst : Lattice α] [inst_1
 : OrderBot α] {f : ι → α}   [inst_2 : DecidableEq ι] {s : Finset ι'} {g : ι' → 
ι}, s.SupIndep (f ∘ g) → (Finset.image g s).SupIndep f
参数：f ∘ g；Finset.image g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.subset_image_iff`：subset_image_iff [DecidableEq β] {s : Finset α}
 {t : Finset β} {f : α -> β} : t subseteq s.image f ↔ exists s' : Finset α, s' s
ubseteq s ∧ s…
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
protected theorem SupIndep.image [DecidableEq ι] {s : Finset ι'} {g : ι' → ι}
    (hs : s.SupIndep (f ∘ g)) : (s.image g).SupIndep f := by
  intro t ht i hi hit
  rcases subset_image_iff.mp ht with ⟨t, hts, rfl⟩
  rcases mem_image.mp hi with ⟨i, his, rfl⟩
  rw [sup_image]
  exact hs hts his (hit <| mem_image_of_mem _ ·)
/-
**Finset.supIndep_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_map {s : Finset ι'} {g : ι' ↪ ι} : (s.map g).SupIndep f ↔ s.SupIn
dep (f ∘ g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.map_subset_map`：map_subset_map {s₁ s₂ : Finset α} : s₁.map f subs
eteq s₂.map f ↔ s₁ subseteq s₂
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.SupIndep.image`：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4} [
inst : Lattice α] [inst_1 : OrderBot α] {f : ι → α}   [inst_2 : DecidableEq ι] {
s : Finset …
-/
theorem supIndep_map {s : Finset ι'} {g : ι' ↪ ι} : (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g) := by
  refine ⟨fun hs t ht i hi hit => ?_, fun hs => ?_⟩
  · rw [← sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact hs.image

@[simp]
/-
**Finset.supIndep_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_pair [DecidableEq ι] {i j : ι} (hij : i != j) : ({i, j} : Finset 
ι).SupIndep f ↔ Disjoint (f i) (f j)
参数：hij : i != j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.pair_comm`：pair_comm (a b : α) : ({a, b} : Finset α) = {b, a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem supIndep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) := by
  suffices Disjoint (f i) (f j) → Disjoint (f j) ((Finset.erase {i, j} j).sup f) by
    simpa [supIndep_iff_disjoint_erase, hij]
  rw [pair_comm]
  simp [hij.symm, disjoint_comm]
/-
**Finset.supIndep_univ_bool** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_univ_bool (f : Bool -> α) : (Finset.univ : Finset Bool).SupIndep 
f ↔ Disjoint (f false) (f true)
参数：f : Bool -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.supIndep_pair`：supIndep_pair [DecidableEq ι] {i j : ι} (hij : i !
= j) : ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
-/
theorem supIndep_univ_bool (f : Bool → α) :
    (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  haveI : true ≠ false := by simp only [Ne, not_false_iff, reduceCtorEq]
  (supIndep_pair this).trans disjoint_comm

@[simp]
/-
**Finset.supIndep_univ_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_univ_fin_two (f : Fin 2 -> α) : (Finset.univ : Finset (Fin 2)).Su
pIndep f ↔ Disjoint (f 0) (f 1)
参数：f : Fin 2 -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.supIndep_pair`：supIndep_pair [DecidableEq ι] {i j : ι} (hij : i !
= j) : ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j)
-/
theorem supIndep_univ_fin_two (f : Fin 2 → α) :
    (Finset.univ : Finset (Fin 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  have : (0 : Fin 2) ≠ 1 := by simp
  supIndep_pair this

@[simp]
/-
**Finset.supIndep_attach** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_attach : (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.attach_map_val`：attach_map_val {s : Finset α} : s.attach.map (Emb
edding.subtype _) = s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.supIndep_map`：supIndep_map {s : Finset ι'} {g : ι' ↪ ι} : (s.map 
g).SupIndep f ↔ s.SupIndep (f ∘ g)
-/
theorem supIndep_attach : (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f := by
  simpa [Finset.attach_map_val] using! (supIndep_map (s := s.attach) (g := .subtype _)).symm

alias ⟨_, SupIndep.attach⟩ := supIndep_attach

end Lattice

section IsModularLattice

variable [Lattice α] [IsModularLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

/-- Bind operation for `SupIndep`. -/
/-
**Finset.SupIndep.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4} [inst : Lattice α] [IsModu
larLattice α] [inst_2 : OrderBot α]   [inst_3 : DecidableEq ι] {s : Finset ι'} {
g : ι' → Finset ι} {f : ι → α},   (s.SupIndep fun i => (g i).sup f) → (∀ i' ∈ s,
 (g i').SupIndep f) → (s.biUnion g).SupIndep f
参数：s.SupIndep fun i => (g i).sup f；∀ i' ∈ s, (g i').SupIndep f；s.biUnion g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Disjoint.disjoint_sup_left_of_disjoint_sup_right`：disjoint_sup_left_of_d
isjoint_sup_right [Lattice α] [OrderBot α] [IsModularLattice α] (h : Disjoint b 
c) (hsup : Disjoint a (b ⊔ c)) : Disjo…
· 使用定理 `Finset.supIndep_iff_disjoint_erase`：supIndep_iff_disjoint_erase [Decidab
leEq ι] : s.SupIndep f ↔ forall i in s, Disjoint (f i) ((s.erase i).sup f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f

--- 原说明 ---
Bind operation for `SupIndep`.
-/
protected theorem SupIndep.biUnion [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.biUnion g).SupIndep f := by
  classical
  intro a ha b hb hab
  obtain ⟨i', hi', hb⟩ := mem_biUnion.mp hb
  let t := s.erase i'
  let u := (g i').erase b
  apply Disjoint.mono_right <| calc
    a.sup f ≤ (t.biUnion g ∪ u).sup f := by grind
    _ ≤ (t.sup fun i => (g i).sup f) ⊔ (u.sup f) := by grind
  symm
  apply Disjoint.disjoint_sup_left_of_disjoint_sup_right
  · exact (supIndep_iff_disjoint_erase.mp (hg i' hi') b hb).symm
  · rw [← sup_singleton (f := f) (b := b), ← sup_union, show u ∪ {b} = g i' by grind]
    exact (supIndep_iff_disjoint_erase.mp hs i' hi').symm

/-- Bind operation for `SupIndep`. -/
/-
**Finset.SupIndep.sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4} [inst : Lattice α] [IsModu
larLattice α] [inst_2 : OrderBot α]   [inst_3 : DecidableEq ι] {s : Finset ι'} {
g : ι' → Finset ι} {f : ι → α},   (s.SupIndep fun i => (g i).sup f) → (∀ i' ∈ s,
 (g i').SupIndep f) → (s.sup g).SupIndep f
参数：s.SupIndep fun i => (g i).sup f；∀ i' ∈ s, (g i').SupIndep f；s.sup g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `Finset.SupIndep.biUnion`：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4}
 [inst : Lattice α] [IsModularLattice α] [inst_2 : OrderBot α]   [inst_3 : Decid
ableEq ι] {s …

--- 原说明 ---
Bind operation for `SupIndep`.
-/
protected theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.sup g).SupIndep f := by
  rw [sup_eq_biUnion]
  exact hs.biUnion hg

/-- Bind operation for `SupIndep`. -/
/-
**Finset.SupIndep.sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [IsModularLattice α] [i
nst_2 : OrderBot α] {β : ι → Type u_5}   {s : Finset ι} {g : (i : ι) → Finset (β
 i)} {f : Sigma β → α},   (s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩) →   
  (∀ i ∈ s, (g i).SupIndep fun b => f ⟨i, b⟩) → (s.sigma g).SupIndep f
参数：i : ι；β i；s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩；∀ i ∈ s, (g i).SupI
ndep fun b => f ⟨i, b⟩；s.sigma g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sigma_eq_biUnion`：sigma_eq_biUnion [DecidableEq (Σ i, α i)] (s : 
Finset ι) (t : forall i, Finset (α i)) : s.sigma t = s.biUnion fun i => (t i).ma
p Embedding.s…
· 使用定理 `Finset.SupIndep.biUnion`：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4}
 [inst : Lattice α] [IsModularLattice α] [inst_2 : OrderBot α]   [inst_3 : Decid
ableEq ι] {s …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Bind operation for `SupIndep`.
-/
protected theorem SupIndep.sigma {β : ι → Type*} {s : Finset ι} {g : ∀ i, Finset (β i)}
    {f : Sigma β → α} (hs : s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩)
    (hg : ∀ i ∈ s, (g i).SupIndep fun b => f ⟨i, b⟩) : (s.sigma g).SupIndep f := by
  classical
  rw [Finset.sigma_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · simpa [Finset.supIndep_map] using! hg
/-
**Finset.SupIndep.product** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4} [inst : Lattice α] [IsModu
larLattice α] [inst_2 : OrderBot α]   {s : Finset ι} {t : Finset ι'} {f : ι × ι'
 → α},   (s.SupIndep fun i => t.sup fun i' => f (i, i')) →     (t.SupIndep fun i
' => s.sup fun i => f (i, i')) → (s ×ˢ t).SupIndep f
参数：s.SupIndep fun i => t.sup fun i' => f (i, i')；t.SupIndep fun i' => s.sup fun 
i => f (i, i')；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.product_eq_biUnion`：product_eq_biUnion [DecidableEq (α × β)] (s :
 Finset α) (t : Finset β) : s ×ˢ t = s.biUnion fun a => t.image fun b => (a, b)
· 使用定理 `Finset.SupIndep.biUnion`：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4}
 [inst : Lattice α] [IsModularLattice α] [inst_2 : OrderBot α]   [inst_3 : Decid
ableEq ι] {s …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.SupIndep.image`：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4} [
inst : Lattice α] [inst_1 : OrderBot α] {f : ι → α}   [inst_2 : DecidableEq ι] {
s : Finset …
· 使用定理 `Finset.SupIndep.mono`：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α]
 [inst_1 : OrderBot α] {s : Finset ι} {f g : ι → α},   s.SupIndep f → (∀ i ∈ s, 
g i ≤ f i)…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
protected theorem SupIndep.product {s : Finset ι} {t : Finset ι'} {f : ι × ι' → α}
    (hs : s.SupIndep fun i => t.sup fun i' => f (i, i'))
    (ht : t.SupIndep fun i' => s.sup fun i => f (i, i')) : (s ×ˢ t).SupIndep f := by
  classical
  rw [Finset.product_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · exact fun i' hi' ↦ (ht.mono fun i hi ↦ Finset.le_sup (f := fun i' ↦ f (i', i)) hi').image
/-
**Finset.SupIndep.disjoint_sup_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [IsModularLattice α] [i
nst_2 : OrderBot α] {s : Finset ι} {f : ι → α}   {u v : Finset ι}, s.SupIndep f 
→ u ⊆ s → v ⊆ s → Disjoint u v → Disjoint (u.sup f) (v.sup f)
参数：u.sup f；v.sup f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
-/
protected theorem SupIndep.disjoint_sup_sup {s : Finset ι} {f : ι → α} {u v : Finset ι}
    (hs : s.SupIndep f) (hu : u ⊆ s) (hv : v ⊆ s) (huv : Disjoint u v) :
    Disjoint (u.sup f) (v.sup f) := by
  classical
  induction u using Finset.induction generalizing v with
  | empty => simp
  | insert x u hx ih =>
    grind [= SupIndep, Disjoint.disjoint_sup_left_of_disjoint_sup_right]
/-
**Finset.supIndep_sigma_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_sigma_iff' {β : ι -> Type*} {s : Finset ι} {g : forall i, Finset 
(β i)} {f : Sigma β -> α} : (s.sigma g).SupIndep f ↔ (s.SupIndep fun i => (g i).
sup fun b => f ⟨i, b⟩) ∧ forall i in s, (g i).SupIndep fun b => f ⟨i, b⟩
参数：β i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.SupIndep.disjoint_sup_sup`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [IsModularLattice α] [inst_2 : OrderBot α] {s : Finset ι} {f : ι → 
α}   {u v : Finset ι},…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.SupIndep.sigma`：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α
] [IsModularLattice α] [inst_2 : OrderBot α] {β : ι → Type u_5}   {s : Finset ι}
 {g : (i : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem supIndep_sigma_iff' {β : ι → Type*} {s : Finset ι} {g : ∀ i, Finset (β i)}
    {f : Sigma β → α} : (s.sigma g).SupIndep f ↔ (s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩)
      ∧ ∀ i ∈ s, (g i).SupIndep fun b => f ⟨i, b⟩ := by
  classical
  refine ⟨fun h ↦ ⟨fun t _ i _ _ ↦ ?_, fun i _ t _ j _ _ ↦ ?_⟩, fun h ↦ h.1.sigma h.2⟩
  · let u := (g i).map (Function.Embedding.sigmaMk i)
    let v := t.biUnion (fun j => (g j).map (Function.Embedding.sigmaMk j))
    suffices Disjoint (u.sup f) (v.sup f) by simpa only [sup_map, sup_biUnion, u, v]
    apply SupIndep.disjoint_sup_sup h <;> grind [disjoint_left]
  · suffices Disjoint (f ⟨i, j⟩) ((t.image fun b ↦ ⟨i, b⟩).sup f) by simpa only [sup_image]
    grind [= SupIndep]
/-
**Finset.supIndep_product_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_product_iff {s : Finset ι} {t : Finset ι'} {f : ι × ι' -> α} : (s
.product t).SupIndep f ↔ (s.SupIndep fun i => t.sup fun i' => f (i, i')) ∧ t.Sup
Indep fun i' => s.sup fun i => f (i, i')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.sup_product_left`：sup_product_left (s : Finset β) (t : Finset γ) 
(f : β × γ -> α) : (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩
· 使用定理 `Finset.sup_product_right`：sup_product_right (s : Finset β) (t : Finset γ
) (f : β × γ -> α) : (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩
· 使用定理 `Finset.SupIndep.product`：∀ {α : Type u_1} {ι : Type u_3} {ι' : Type u_4}
 [inst : Lattice α] [IsModularLattice α] [inst_2 : OrderBot α]   {s : Finset ι} 
{t : Finset ι…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem supIndep_product_iff {s : Finset ι} {t : Finset ι'} {f : ι × ι' → α} :
    (s.product t).SupIndep f ↔ (s.SupIndep fun i => t.sup fun i' => f (i, i'))
      ∧ t.SupIndep fun i' => s.sup fun i => f (i, i') := by
  classical
  refine ⟨fun h ↦ ⟨fun u _ i _ _ ↦ ?_, fun u _ i _ _ ↦ ?_⟩, fun h ↦ h.1.product h.2⟩
  · suffices Disjoint ((t.image ((i, ·))).sup f) ((u ×ˢ t).sup f) by
      simpa only [sup_image, sup_product_left]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]
  · suffices Disjoint ((s.image ((·, i))).sup f) ((s ×ˢ u).sup f) by
      simpa only [sup_image, sup_product_right]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]
/-
**Finset.SupIndep.union** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [IsModularLattice α] [i
nst_2 : OrderBot α] [inst_3 : DecidableEq ι]   {s t : Finset ι} {f : ι → α}, s.S
upIndep f → t.SupIndep f → Disjoint (s.sup f) (t.sup f) → (s ∪ t).SupIndep f
参数：s.sup f；t.sup f；s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用引理 `Finset.singleton_biUnion`：singleton_biUnion {a : α} : Finset.biUnion {a}
 t = t a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem SupIndep.union [DecidableEq ι] {s t : Finset ι} {f : ι → α}
    (hs : s.SupIndep f) (ht : t.SupIndep f) (h : Disjoint (s.sup f) (t.sup f)) :
    (s ∪ t).SupIndep f := by
  rw [show s ∪ t = ({s, t} : Finset _).biUnion id by simp]
  grind [SupIndep.biUnion, supIndep_pair]
/-
**Finset.SupIndep.insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset.SupIndep`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice α] [IsModularLattice α] [i
nst_2 : OrderBot α] [inst_3 : DecidableEq ι]   {i : ι} {s : Finset ι} {f : ι → α
}, s.SupIndep f → Disjoint (f i) (s.sup f) → (insert i s).SupIndep f
参数：f i；s.sup f；insert i s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem SupIndep.insert [DecidableEq ι] {i : ι} {s : Finset ι} {f : ι → α}
    (hs : s.SupIndep f) (h : Disjoint (f i) (s.sup f)) : (insert i s).SupIndep f := by
  grind [insert_eq, SupIndep.union, sup_singleton]

end IsModularLattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

/-
**Finset.supIndep_iff_pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：supIndep_iff_pairwiseDisjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoin
t f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_sup_right`：∀ {α : Type u_2} {ι : Type u_5} [inst : Distr
ibLattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   Disjoin
t a (s.sup f) ↔…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem supIndep_iff_pairwiseDisjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwiseDisjoint, fun hs _ ht _ hi hit =>
    Finset.disjoint_sup_right.2 fun _ hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.supIndep⟩ := supIndep_iff_pairwiseDisjoint

end DistribLattice

end Finset

/-! ### On complete lattices via `sSup` -/

section CompleteLattice
variable [CompleteLattice α]

open Set Function

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
/-
**sSupIndep** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sSupIndep (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An independent set of elements in a complete lattice is one in which every eleme
nt is disjoint
  from the `Sup` of the rest.
-/
def sSupIndep (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (sSup (s \ {a}))

variable {s : Set α} (hs : sSupIndep s)

@[simp]
/-
**sSupIndep_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_empty : sSupIndep (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem sSupIndep_empty : sSupIndep (∅ : Set α) := fun x hx =>
  (Set.notMem_empty x hx).elim

include hs in
/-
**sSupIndep.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep.mono {t : Set α} (hst : t subseteq s) : sSupIndep t
参数：hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
-/
theorem sSupIndep.mono {t : Set α} (hst : t ⊆ s) : sSupIndep t := fun _ ha =>
  (hs (hst ha)).mono_right (sSup_le_sSup (sdiff_subset_sdiff_left hst))

include hs in
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
/-
**sSupIndep.pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep.pairwiseDisjoint : s.PairwiseDisjoint id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sSup_right`：disjoint_sSup_right {a : Set α} {b : α} (d : Disjoi
nt b (sSup a)) {i} (hi : i in a) : Disjoint b i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If the elements of a set are independent, then any pair within that set is disjo
int.
-/
theorem sSupIndep.pairwiseDisjoint : s.PairwiseDisjoint id := fun _ hx y hy h =>
  disjoint_sSup_right (hs hx) ((mem_sdiff y).mpr ⟨hy, h.symm⟩)
/-
**sSupIndep_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_singleton (a : α) : sSupIndep ({a} : Set α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
-/
theorem sSupIndep_singleton (a : α) : sSupIndep ({a} : Set α) := fun i hi ↦ by
  simp_all
/-
**sSupIndep_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_pair {a b : α} (hab : a != b) : sSupIndep ({a, b} : Set α) ↔ Dis
joint a b
参数：hab : a != b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep.pairwiseDisjoint`：sSupIndep.pairwiseDisjoint : s.PairwiseDisjo
int id
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
· 使用定理 `Set.insert_sdiff_eq_singleton`：insert_sdiff_eq_singleton {a : α} {s : Se
t α} (h : a ∉ s) : insert a s \ s = {a}
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem sSupIndep_pair {a b : α} (hab : a ≠ b) :
    sSupIndep ({a, b} : Set α) ↔ Disjoint a b := by
  constructor
  · intro h
    exact h.pairwiseDisjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert! h using 1
      simp [hab, sSup_singleton]
    · convert! h.symm using 1
      simp [hab, sSup_singleton]

include hs in
/-- If the elements of a set are independent, then any element is disjoint from the `sSup` of some
subset of the rest. -/
/-
**sSupIndep.disjoint_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep.disjoint_sSup {x : α} {y : Set α} (hx : x in s) (hy : y subseteq
 s) (hxy : x ∉ y) : Disjoint x (sSup y)
参数：hx : x in s；hy : y subseteq s；hxy : x ∉ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep.mono`：sSupIndep.mono {t : Set α} (hst : t subseteq s) : sSupIn
dep t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
If the elements of a set are independent, then any element is disjoint from the 
`sSup` of some
subset of the rest.
-/
theorem sSupIndep.disjoint_sSup {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) :
    Disjoint x (sSup y) := by
  have := (hs.mono <| insert_subset_iff.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_sdiff_of_mem _ (mem_singleton _), sdiff_singleton_eq_self hxy] at this
  exact this

/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `iSup` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
/-
**iSupIndep** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSupIndep {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι -> α) : Prop
参数：t : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An independent indexed family of elements in a complete lattice is one in which 
every element
  is disjoint from the `iSup` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they 
generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this se
nse if
  and only the natural map from the direct sum of the submodules to the module i
s injective.
-/
def iSupIndep {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)
/-
**sSupIndep_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_iff {α : Type*} [CompleteLattice α] (s : Set α) : sSupIndep s ↔ 
iSupIndep ((↑) : s -> α)
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sSupIndep_iff {α : Type*} [CompleteLattice α] (s : Set α) :
    sSupIndep s ↔ iSupIndep ((↑) : s → α) := by
  simp_rw [iSupIndep, sSupIndep, SetCoe.forall, sSup_eq_iSup]
  refine forall₂_congr fun a ha => ?_
  simp [iSup_subtype, iSup_and]

variable {t : ι → α} (ht : iSupIndep t)
/-
**iSupIndep_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_def : iSupIndep t ↔ forall i, Disjoint (t i) (⨆ (j) (_ : j != i)
, t j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iSupIndep_def : iSupIndep t ↔ ∀ i, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl
/-
**iSupIndep_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_def' : iSupIndep t ↔ forall i, Disjoint (t i) (sSup (t '' { j | 
j != i }))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iSupIndep_def' : iSupIndep t ↔ ∀ i, Disjoint (t i) (sSup (t '' { j | j ≠ i })) := by
  simp_rw [sSup_image]
  rfl
/-
**iSupIndep_def''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_def'' : iSupIndep t ↔ forall i, Disjoint (t i) (sSup { a | exist
s j != i, t j = a })
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSupIndep_def'`：iSupIndep_def' : iSupIndep t ↔ forall i, Disjoint (t i) 
(sSup (t '' { j | j != i }))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iSupIndep_def'' :
    iSupIndep t ↔ ∀ i, Disjoint (t i) (sSup { a | ∃ j ≠ i, t j = a }) := by
  rw [iSupIndep_def']
  aesop

@[simp]
/-
**iSupIndep_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_subsingleton [Subsingleton ι] (t : ι -> α) : iSupIndep t
参数：t : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
-/
theorem iSupIndep_subsingleton [Subsingleton ι] (t : ι → α) : iSupIndep t :=
  fun i ↦ by simp [← Subsingleton.elim i]

include ht in
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
/-
**iSupIndep.pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.pairwiseDisjoint : Pairwise (Disjoint on t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sSup_right`：disjoint_sSup_right {a : Set α} {b : α} (d : Disjoi
nt b (sSup a)) {i} (hi : i in a) : Disjoint b i
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If the elements of a set are independent, then any pair within that set is disjo
int.
-/
theorem iSupIndep.pairwiseDisjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_sSup_right (ht x) ⟨y, iSup_pos h.symm⟩
/-
**iSupIndep.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.mono {s t : ι -> α} (hs : iSupIndep s) (hst : t <= s) : iSupInde
p t
参数：hs : iSupIndep s；hst : t <= s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
-/
theorem iSupIndep.mono {s t : ι → α} (hs : iSupIndep s) (hst : t ≤ s) : iSupIndep t :=
  fun i => (hs i).mono (hst i) <| iSup₂_mono fun j _ => hst j

/-- Composing an independent indexed family with an injective function on the index results in
another independent indexed family. -/
/-
**iSupIndep.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep t
) (hf : Injective f) : iSupIndep (t ∘ f)
参数：ht : iSupIndep t；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_const_mono`：iSup_const_mono (h : ι -> ι') : ⨆ _ : ι, a <= ⨆ _ : ι',
 a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `iSup_comp_le`：iSup_comp_le {ι' : Sort*} (f : ι' -> α) (g : ι -> ι') : ⨆ 
x, f (g x) <= ⨆ y, f y

--- 原说明 ---
Composing an independent indexed family with an injective function on the index 
results in
another independent indexed family.
-/
theorem iSupIndep.comp {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : iSupIndep t)
    (hf : Injective f) : iSupIndep (t ∘ f) := fun i =>
  (ht (f i)).mono_right <| by
    refine (iSup_mono fun i => ?_).trans (iSup_comp_le _ f)
    exact iSup_const_mono hf.ne
/-
**iSupIndep.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.comp' {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep 
<| t ∘ f) (hf : Surjective f) : iSupIndep t
参数：ht : iSupIndep <| t ∘ f；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem iSupIndep.comp' {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : iSupIndep <| t ∘ f)
    (hf : Surjective f) : iSupIndep t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.iSup_comp]
  exact (ht i').mono_right (biSup_mono fun j' hij => mt (congr_arg f) hij)
/-
**iSupIndep.sSupIndep_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.sSupIndep_range (ht : iSupIndep t) : sSupIndep range t
参数：ht : iSupIndep t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSupIndep_iff`：sSupIndep_iff {α : Type*} [CompleteLattice α] (s : Set α)
 : sSupIndep s ↔ iSupIndep ((↑) : s -> α)
· 使用定理 `iSupIndep.comp'`：iSupIndep.comp' {ι ι' : Sort*} {t : ι -> α} {f : ι' -> 
ι} (ht : iSupIndep <| t ∘ f) (hf : Surjective f) : iSupIndep t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.coe_comp_rangeFactorization`：coe_comp_rangeFactorization (f : ι -> β
) : (↑) ∘ rangeFactorization f = f
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem iSupIndep.sSupIndep_range (ht : iSupIndep t) : sSupIndep <| range t := by
  rw [sSupIndep_iff]
  rw [← coe_comp_rangeFactorization t] at ht
  exact ht.comp' rangeFactorization_surjective

@[simp]
/-
**iSupIndep_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_ne_bot : iSupIndep (fun i : {i // t i != ⊥} => t i) ↔ iSupIndep 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_split`：iSup_split (f : β -> α) (p : β -> Prop) : ⨆ i, f i = (⨆ (i) 
(_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iSupIndep.comp`：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι}
 (ht : iSupIndep t) (hf : Injective f) : iSupIndep (t ∘ f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem iSupIndep_ne_bot :
    iSupIndep (fun i : {i // t i ≠ ⊥} ↦ t i) ↔ iSupIndep t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp Subtype.val_injective⟩
  simp only [iSupIndep_def] at h ⊢
  intro i
  cases eq_or_ne (t i) ⊥ with
  | inl hi => simp [hi]
  | inr hi => ?_
  convert! h ⟨i, hi⟩
  have : ∀ j, ⨆ (_ : t j = ⊥), t j = ⊥ := fun j ↦ by simp only [iSup_eq_bot, imp_self]
  rw [iSup_split _ (fun j ↦ t j = ⊥), iSup_subtype]
  simp only [iSup_comm (ι' := _ ≠ i), this, ne_eq, sup_of_le_right, Subtype.mk.injEq, iSup_bot,
    bot_le]
/-
**iSupIndep.injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i != ⊥}
参数：ht : iSupIndep t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
-/
theorem iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i ≠ ⊥} := by
  rintro i _ j (hj : t j ≠ ⊥) h
  by_contra! contra
  apply hj
  suffices t j ≤ ⨆ (k) (_ : k ≠ i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j ≠ i := Ne.symm contra
  -- Porting note: needs explicit `f`
  exact le_iSup₂ (f := fun x _ ↦ t x) j contra
/-
**iSupIndep.injOn_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep.injOn_iInf {β : ι -> Type*} (t : (i : ι) -> β i -> α) (ht : fora
ll i, iSupIndep (t i)) : InjOn (fun b : (i : ι) -> β i => ⨅ i, t i (b i)) {b | ⨅
 i, t i (b i) != ⊥}
参数：t : (i : ι) -> β i -> α；ht : forall i, iSupIndep (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma iSupIndep.injOn_iInf {β : ι → Type*} (t : (i : ι) → β i → α) (ht : ∀ i, iSupIndep (t i)) :
    InjOn (fun b : (i : ι) → β i ↦ ⨅ i, t i (b i)) {b | ⨅ i, t i (b i) ≠ ⊥} := by
  intro b₁ hb₁ b₂ hb₂ h_eq
  beta_reduce at h_eq
  by_contra h_ne
  obtain ⟨i, hi⟩ : ∃ i, b₁ i ≠ b₂ i := Function.ne_iff.mp h_ne
  have := calc
    ⨅ i, t i (b₁ i) ≤ t i (b₁ i) ⊓ t i (b₂ i) := le_inf (iInf_le ..) (h_eq ▸ iInf_le ..)
    _ = ⊥ := (ht i (b₁ i) |>.mono_right <| le_iSup₂_of_le (b₂ i) hi.symm le_rfl).eq_bot
  simp_all
/-
**iSupIndep.injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.injective (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥) : I
njective t
参数：ht : iSupIndep t；h_ne_bot : forall i, t i != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSupIndep.injOn`：iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i !
= ⊥}
-/
theorem iSupIndep.injective (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Injective t := by
  suffices univ = {i | t i ≠ ⊥} by simpa [← this] using ht.injOn
  simp_all
/-
**iSupIndep_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_pair {i j : ι} (hij : i != j) (huniv : forall k, k = i ∨ k = j) 
: iSupIndep t ↔ Disjoint (t i) (t j)
参数：hij : i != j；huniv : forall k, k = i ∨ k = j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.pairwiseDisjoint`：iSupIndep.pairwiseDisjoint : Pairwise (Disjo
int on t)
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem iSupIndep_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j) :
    iSupIndep t ↔ Disjoint (t i) (t j) := by
  constructor
  · exact fun h => h.pairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine h.mono_right (iSup_le fun i => iSup_le fun hi => Eq.le ?_)
      rw [(huniv i).resolve_left hi]
    · refine h.symm.mono_right (iSup_le fun j => iSup_le fun hj => Eq.le ?_)
      rw [(huniv j).resolve_right hj]

@[simp]
/-
**iSup_fin_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_fin_three {α : Type*} [CompleteLattice α] {f : Fin 3 -> α} : ⨆ i, f i
 = f 0 ⊔ f 1 ⊔ f 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
-/
lemma iSup_fin_three {α : Type*} [CompleteLattice α] {f : Fin 3 → α} :
    ⨆ i, f i = f 0 ⊔ f 1 ⊔ f 2 := by
  suffices ⨆ i ∈ Finset.univ, f i = f 0 ⊔ f 1 ⊔ f 2 by simp [← this]
  rw [← Finset.sup_eq_iSup, show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from rfl]
  simp [sup_assoc]
/-
**iSupIndep_fin_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep_fin_three {α : Type*} [CompleteLattice α] {f : Fin 3 -> α} : iSu
pIndep f ↔ Disjoint (f 0) (f 1 ⊔ f 2) ∧ Disjoint (f 1) (f 2 ⊔ f 0) ∧ Disjoint (f
 2) (f 0 ⊔ f 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSupIndep_def`：iSupIndep_def : iSupIndep t ↔ forall i, Disjoint (t i) (⨆
 (j) (_ : j != i), t j)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `iSup_fin_three`：iSup_fin_three {α : Type*} [CompleteLattice α] {f : Fin 
3 -> α} : ⨆ i, f i = f 0 ⊔ f 1 ⊔ f 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma iSupIndep_fin_three {α : Type*} [CompleteLattice α] {f : Fin 3 → α} :
    iSupIndep f ↔
      Disjoint (f 0) (f 1 ⊔ f 2) ∧
      Disjoint (f 1) (f 2 ⊔ f 0) ∧
      Disjoint (f 2) (f 0 ⊔ f 1) := by
  rw [iSupIndep_def, sup_comm (f 2) (f 0)]
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun ⟨h₀, h₁, h₂⟩ i ↦ ?_⟩
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · fin_cases i <;> simpa

/-- Composing an independent indexed family with an order isomorphism on the elements results in
another independent indexed family. -/
/-
**iSupIndep.map_orderIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.map_orderIso {ι : Sort*} {α β : Type*} [CompleteLattice α] [Comp
leteLattice β] (f : α ≃o β) {a : ι -> α} (ha : iSupIndep a) : iSupIndep (f ∘ a)
参数：f : α ≃o β；ha : iSupIndep a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Monotone.le_map_iSup₂`：Monotone.le_map_iSup₂ [CompleteLattice β] {f : α 
-> β} (hf : Monotone f) (s : forall i, κ i -> α) : ⨆ (i) (j), f (s i j) <= f (⨆ 
(i) (j), s …
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
· 使用定理 `Disjoint.map_orderIso`：Disjoint.map_orderIso [SemilatticeInf α] [OrderBo
t α] [SemilatticeInf β] [OrderBot β] {a b : α} (f : α ≃o β) (ha : Disjoint a b) 
: Disjoint …

--- 原说明 ---
Composing an independent indexed family with an order isomorphism on the element
s results in
another independent indexed family.
-/
theorem iSupIndep.map_orderIso {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} (ha : iSupIndep a) : iSupIndep (f ∘ a) :=
  fun i => ((ha i).map_orderIso f).mono_right (f.monotone.le_map_iSup₂ _)

@[simp]
/-
**iSupIndep_map_orderIso_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_map_orderIso_iff {ι : Sort*} {α β : Type*} [CompleteLattice α] [
CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSupIndep (f ∘ a) ↔ iSupIndep a
参数：f : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `iSupIndep.map_orderIso`：iSupIndep.map_orderIso {ι : Sort*} {α β : Type*}
 [CompleteLattice α] [CompleteLattice β] (f : α ≃o β) {a : ι -> α} (ha : iSupInd
ep a) : iSup…
-/
theorem iSupIndep_map_orderIso_iff {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} : iSupIndep (f ∘ a) ↔ iSupIndep a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩

/-- If the elements of a set are independent, then any element is disjoint from the `iSup` of some
subset of the rest. -/
/-
**iSupIndep.disjoint_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.disjoint_biSup {ι : Type*} {α : Type*} [CompleteLattice α] {t : 
ι -> α} (ht : iSupIndep t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ 
i in y, t i)
参数：ht : iSupIndep t；hx : x ∉ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b

--- 原说明 ---
If the elements of a set are independent, then any element is disjoint from the 
`iSup` of some
subset of the rest.
-/
theorem iSupIndep.disjoint_biSup {ι : Type*} {α : Type*} [CompleteLattice α] {t : ι → α}
    (ht : iSupIndep t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (biSup_mono fun _ hi => (ne_of_mem_of_not_mem hi hx :)) (ht x)
/-
**iSupIndep.of_coe_Iic_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep.of_coe_Iic_comp {ι : Sort*} {a : α} {t : ι -> Set.Iic a} (ht : i
SupIndep ((↑) ∘ t : ι -> α)) : iSupIndep t
参数：ht : iSupIndep ((↑) ∘ t : ι -> α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma iSupIndep.of_coe_Iic_comp {ι : Sort*} {a : α} {t : ι → Set.Iic a}
    (ht : iSupIndep ((↑) ∘ t : ι → α)) : iSupIndep t := by
  intro i x
  specialize ht i
  simp_rw [Function.comp_apply, ← Set.Iic.coe_iSup] at ht
  exact @ht x
/-
**iSupIndep_comp_coe_iff_supIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_comp_coe_iff_supIndep {s : Finset ι} {f : ι -> α} : iSupIndep (f
 ∘ ((↑) : s -> ι)) ↔ s.SupIndep f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.supIndep_iff_disjoint_erase`：supIndep_iff_disjoint_erase [Decidab
leEq ι] : s.SupIndep f ↔ forall i in s, Disjoint (f i) ((s.erase i).sup f)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSupIndep_comp_coe_iff_supIndep {s : Finset ι} {f : ι → α} :
    iSupIndep (f ∘ ((↑) : s → ι)) ↔ s.SupIndep f := by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine Subtype.forall.trans (forall₂_congr fun a b => ?_)
    rw [Finset.sup_eq_iSup]
    congr! 1
    refine iSup_subtype.trans ?_
    congr! 1
    simp [iSup_and, @iSup_comm _ (_ ∈ s)]

alias ⟨iSupIndep.supIndep, Finset.SupIndep.independent⟩ := iSupIndep_comp_coe_iff_supIndep
/-
**iSupIndep.supIndep'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.supIndep' {f : ι -> α} (s : Finset ι) (h : iSupIndep f) : s.SupI
ndep f
参数：s : Finset ι；h : iSupIndep f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.supIndep`：∀ {α : Type u_1} {ι : Type u_3} [inst : CompleteLatt
ice α] {s : Finset ι} {f : ι → α},   iSupIndep (f ∘ Subtype.val) → s.SupIndep f
· 使用定理 `iSupIndep.comp`：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι}
 (ht : iSupIndep t) (hf : Injective f) : iSupIndep (t ∘ f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem iSupIndep.supIndep' {f : ι → α} (s : Finset ι) (h : iSupIndep f) : s.SupIndep f :=
  iSupIndep.supIndep (h.comp Subtype.coe_injective)

/-- A variant of `iSupIndep_comp_coe_iff_supIndep` for `Fintype`s. -/
/-
**iSupIndep_iff_supIndep_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_supIndep_univ [Fintype ι] {f : ι -> α} : iSupIndep f ↔ Finse
t.univ.SupIndep f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A variant of `iSupIndep_comp_coe_iff_supIndep` for `Fintype`s.
-/
theorem iSupIndep_iff_supIndep_univ [Fintype ι] {f : ι → α} :
    iSupIndep f ↔ Finset.univ.SupIndep f := by
  classical
    simp [Finset.supIndep_iff_disjoint_erase, iSupIndep, Finset.sup_eq_iSup]

alias ⟨iSupIndep.sup_indep_univ, Finset.SupIndep.iSupIndep_of_univ⟩ := iSupIndep_iff_supIndep_univ
/-
**iSupIndep.le_iff_eq_of_iSup_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep.le_iff_eq_of_iSup_eq_top [IsModularLattice α] {f g : ι -> α} (h₁
 : iSupIndep g) (h₂ : iSup f = ⊤) : f <= g ↔ f = g
参数：h₁ : iSupIndep g；h₂ : iSup f = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_split_single`：iSup_split_single (f : β -> α) (i₀ : β) : ⨆ i, f i = 
f i₀ ⊔ ⨆ (i) (_ : i != i₀), f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_eq_of_codisjoint_of_disjoint`：le_iff_eq_of_codisjoint_of_disjoint
 [Lattice α] [BoundedOrder α] [IsModularLattice α] {a b c : α} (h₀ : Codisjoint 
a b) (h₁ : Disjoint b c) …
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma iSupIndep.le_iff_eq_of_iSup_eq_top [IsModularLattice α] {f g : ι → α}
    (h₁ : iSupIndep g) (h₂ : iSup f = ⊤) :
    f ≤ g ↔ f = g := by
  refine ⟨fun h₃ ↦ funext fun i ↦ ?_, le_of_eq⟩
  replace h₁ : Disjoint (⨆ (j) (_ : j ≠ i), f j) (g i) :=
    Disjoint.mono_left (iSup₂_mono fun j _ ↦ h₃ j) (h₁ i).symm
  replace h₂ : Codisjoint (f i) (⨆ (j) (_ : j ≠ i), f j) := by
    rw [codisjoint_iff, ← iSup_split_single f i, h₂]
  exact (le_iff_eq_of_codisjoint_of_disjoint h₂ h₁).mp (h₃ i)

/-- See also `iSupIndep.disjoint_biSup_biSup` where it is shown that the hypothesis `s.Finite` may
be omitted if the lattice is compactly-generated. -/
/-
**iSupIndep.disjoint_biSup_biSup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep.disjoint_biSup_biSup' [IsModularLattice α] {f : ι -> α} {s t : S
et ι} (hf : iSupIndep f) (hst : Disjoint s t) (hs : s.Finite) : Disjoint (⨆ i in
 s, f i) (⨆ i in t, f i)
参数：hf : iSupIndep f；hst : Disjoint s t；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
· 使用定理 `iSupIndep.disjoint_biSup`：iSupIndep.disjoint_biSup {ι : Type*} {α : Type
*} [CompleteLattice α] {t : ι -> α} (ht : iSupIndep t) {x : ι} {y : Set ι} (hx :
 x ∉ y) : Disj…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Finset.iSup_insert`：iSup_insert (a : α) (s : Finset α) (t : α -> β) : ⨆ 
x in insert a s, t x = t a ⊔ ⨆ x in s, t x
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `disjoint_sup_right_of_disjoint_sup_right`：∀ {α : Type u_1} {a b c : α} [
inst : Lattice α] [inst_1 : OrderBot α] [IsModularLattice α],   Disjoint a (b ⊔ 
c) → Disjoint b (c ⊔ a) → Disj…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
See also `iSupIndep.disjoint_biSup_biSup` where it is shown that the hypothesis 
`s.Finite` may
be omitted if the lattice is compactly-generated.
-/
lemma iSupIndep.disjoint_biSup_biSup' [IsModularLattice α]
    {f : ι → α} {s t : Set ι} (hf : iSupIndep f) (hst : Disjoint s t) (hs : s.Finite) :
    Disjoint (⨆ i ∈ s, f i) (⨆ i ∈ t, f i) := by
  suffices ∀ (s : Finset ι) (hst : Disjoint ↑s t), Disjoint (⨆ i ∈ s, f i) (⨆ i ∈ t, f i) by
    specialize this hs.toFinset
    aesop
  clear! s
  intro s hst
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simp
  | insert j s₀ hj ih =>
    have hjt : j ∉ t := by aesop
    replace hst : Disjoint ↑s₀ (insert j t) := by aesop
    replace ih : Disjoint (⨆ i ∈ s₀, f i) (f j ⊔ ⨆ i ∈ t, f i) := by
      specialize ih hst
      rwa [iSup_insert] at ih
    have : Disjoint (f j) ((⨆ i ∈ t, f i) ⊔ (⨆ i ∈ (s₀ : Set ι), f i)) := by
      rw [← iSup_union]
      exact disjoint_biSup hf <| by aesop
    rw [s₀.iSup_insert j f, disjoint_comm, sup_comm]
    exact disjoint_sup_right_of_disjoint_sup_right ih this
/-
**iSupIndep.mem_of_biSup_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep.mem_of_biSup_eq_top {f : ι -> α} {s : Set ι} (h₁ : iSupIndep f) 
(h₂ : ⨆ i in s, f i = ⊤) {i : ι} (hi : f i != ⊥) : i in s
参数：h₁ : iSupIndep f；h₂ : ⨆ i in s, f i = ⊤；hi : f i != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma iSupIndep.mem_of_biSup_eq_top {f : ι → α} {s : Set ι}
    (h₁ : iSupIndep f) (h₂ : ⨆ i ∈ s, f i = ⊤) {i : ι} (hi : f i ≠ ⊥) :
    i ∈ s := by
  by_contra contra
  replace h₁ : Disjoint (f i) (⨆ i ∈ s, f i) := (h₁ i).mono_right <| biSup_mono <| by aesop
  aesop

end CompleteLattice

section Frame
variable [Order.Frame α]

/-
**sSupIndep_iff_pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_iff_pairwiseDisjoint {s : Set α} : sSupIndep s ↔ s.PairwiseDisjo
int id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep.pairwiseDisjoint`：sSupIndep.pairwiseDisjoint : s.PairwiseDisjo
int id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_sSup_iff`：∀ {α : Type u} [inst : Order.Frame α] {a : α} {s : Se
t α}, Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sSupIndep_iff_pairwiseDisjoint {s : Set α} : sSupIndep s ↔ s.PairwiseDisjoint id :=
  ⟨sSupIndep.pairwiseDisjoint, fun hs _ hi =>
    disjoint_sSup_iff.2 fun _ hj => hs hi hj.1 <| Ne.symm hj.2⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.sSupIndep⟩ := sSupIndep_iff_pairwiseDisjoint

open scoped Function in -- required for scoped `on` notation
/-
**iSupIndep_iff_pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_pairwiseDisjoint {f : ι -> α} : iSupIndep f ↔ Pairwise (Disj
oint on f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.pairwiseDisjoint`：iSupIndep.pairwiseDisjoint : Pairwise (Disjo
int on t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iSup_iff`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a
 : α} {f : ι → α},   Disjoint a (⨆ i, f i) ↔ ∀ (i : ι), Disjoint a (f i)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem iSupIndep_iff_pairwiseDisjoint {f : ι → α} : iSupIndep f ↔ Pairwise (Disjoint on f) :=
  ⟨iSupIndep.pairwiseDisjoint, fun hs _ =>
    disjoint_iSup_iff.2 fun _ => disjoint_iSup_iff.2 fun hij => hs hij.symm⟩

end Frame

