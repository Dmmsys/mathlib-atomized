/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.ToFun

/-!
# Theory of filters on sets

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

In this file, we endow `Filter α` it with a complete lattice structure.
This structure is lifted from the lattice structure on `Set (Set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `Filter` is a monadic functor, with a push-forward operation
`Filter.map` and a pull-back operation `Filter.comap` that form a Galois connections for the
order on filters.

The examples of filters appearing in the description of the two motivating ideas are:
* `(Filter.atTop : Filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in `Mathlib/Topology/UniformSpace/Basic.lean`)
* `MeasureTheory.ae` : made of sets whose complement has zero measure with respect to `μ`
  (defined in `Mathlib/MeasureTheory/OuterMeasure/AE`)

The predicate "happening eventually" is `Filter.Eventually`, and "happening often" is
`Filter.Frequently`, whose definitions are immediate after `Filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

## Notation

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `Filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[NeBot f]` in a number of lemmas and definitions.
-/

@[expose] public section

assert_not_exists IsOrderedRing Fintype

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

/-
**Filter.inhabitedMem** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：inhabitedMem : Inhabited { s : Set α // s in f }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_sets`：∀ {α : Type u_1} (self : Filter α), Set.univ ∈ self.se
ts
-/
instance inhabitedMem : Inhabited { s : Set α // s ∈ f } :=
  ⟨⟨univ, f.univ_sets⟩⟩
/-
**Filter.filter_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：filter_eq_iff : f = g ↔ f.sets = g.sets
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Filter.filter_eq`：∀ {α : Type u_1} {f g : Filter α}, f.sets = g.sets → f
 = g
-/
theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congr_arg _, filter_eq⟩
/-
**Filter.sets_subset_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, f.sets ⊆ g.sets ↔ g ≤ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sets_subset_sets : f.sets ⊆ g.sets ↔ g ≤ f := .rfl
/-
**Filter.sets_ssubset_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, f.sets ⊂ g.sets ↔ g < f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sets_ssubset_sets : f.sets ⊂ g.sets ↔ g < f := .rfl

/-- An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ f` (e.g.,
`Filter.comap`, `Filter.coprod`, `Filter.Coprod`, `Filter.cofinite`). -/
/-
**Filter.coext** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, (∀ (s : Set α), sᶜ ∈ f ↔ sᶜ ∈ g) → f = g
参数：∀ (s : Set α), sᶜ ∈ f ↔ sᶜ ∈ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)

--- 原说明 ---
An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ 
f` (e.g.,
`Filter.comap`, `Filter.coprod`, `Filter.Coprod`, `Filter.cofinite`).
-/
protected theorem coext (h : ∀ s, sᶜ ∈ f ↔ sᶜ ∈ g) : f = g :=
  Filter.ext <| compl_surjective.forall.2 h
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (· ⊇ ·) ((· ∈ ·) : Set α → Filter α → Prop) (· ∈ ·) where
  trans h₁ h₂ := mem_of_superset h₂ h₁
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans Membership.mem (· ⊆ ·) (Membership.mem : Filter α → Set α → Prop) where
  trans h₁ h₂ := mem_of_superset h₁ h₂

@[simp]
/-
**Filter.inter_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inter_mem_iff {s t : Set α} : s inter t in f ↔ s in f ∧ t in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
  ⟨fun h => ⟨mem_of_superset h inter_subset_left, mem_of_superset h inter_subset_right⟩,
    and_imp.2 inter_mem⟩
/-
**Filter.sdiff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sdiff_mem {s t : Set α} (hs : s in f) (ht : tᶜ in f) : s \ t in f
参数：hs : s in f；ht : tᶜ in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem sdiff_mem {s t : Set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
  inter_mem hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem := sdiff_mem
/-
**Filter.congr_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：congr_sets (h : { x | x in s ↔ x in t } in f) : s in f ↔ t in f
参数：h : { x | x in s ↔ x in t } in f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem congr_sets (h : { x | x ∈ s ↔ x ∈ t } ∈ f) : s ∈ f ↔ t ∈ f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩
/-
**Filter.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：copy_eq {S} (hmem : forall s, s in S ↔ s in f) : f.copy S hmem = f
参数：hmem : forall s, s in S ↔ s in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
-/
lemma copy_eq {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := Filter.ext hmem

/-- Weaker version of `Filter.biInter_mem` that assumes `Subsingleton β` rather than `Finite β`. -/
/-
**Filter.biInter_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：biInter_mem' {β : Type v} {s : β -> Set α} {is : Set β} (hf : is.Subsingle
ton) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
参数：hf : is.Subsingleton。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl

--- 原说明 ---
Weaker version of `Filter.biInter_mem` that assumes `Subsingleton β` rather than
 `Finite β`.
-/
theorem biInter_mem' {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Subsingleton) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f := by
  apply Subsingleton.induction_on hf <;> simp

/-- Weaker version of `Filter.iInter_mem` that assumes `Subsingleton β` rather than `Finite β`. -/
/-
**Filter.iInter_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInter_mem' {β : Sort v} {s : β -> Set α} [Subsingleton β] : (⋂ i, s i) in
 f ↔ forall i, s i in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Filter.biInter_mem'`：biInter_mem' {β : Type v} {s : β -> Set α} {is : Se
t β} (hf : is.Subsingleton) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.subsingleton_range`：subsingleton_range {α : Sort*} [Subsingleton α] 
(f : α -> β) : (range f).Subsingleton
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Weaker version of `Filter.iInter_mem` that assumes `Subsingleton β` rather than 
`Finite β`.
-/
theorem iInter_mem' {β : Sort v} {s : β → Set α} [Subsingleton β] :
    (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f := by
  rw [← sInter_range, sInter_eq_biInter, biInter_mem' (subsingleton_range s), forall_mem_range]
/-
**Filter.exists_mem_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_mem_subset_iff : (exists t in f, t subseteq s) ↔ s in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩
/-
**Filter.monotone_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：monotone_mem {f : Filter α} : Monotone fun s => s in f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem monotone_mem {f : Filter α} : Monotone fun s => s ∈ f := fun _ _ hst h =>
  mem_of_superset h hst
/-
**Filter.exists_mem_and_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_mem_and_iff {P : Set α -> Prop} {Q : Set α -> Prop} (hP : Antitone 
P) (hQ : Antitone Q) : ((exists u in f, P u) ∧ exists u in f, Q u) ↔ exists u in
 f, P u ∧ Q u
参数：hP : Antitone P；hQ : Antitone Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem exists_mem_and_iff {P : Set α → Prop} {Q : Set α → Prop} (hP : Antitone P)
    (hQ : Antitone Q) : ((∃ u ∈ f, P u) ∧ ∃ u ∈ f, Q u) ↔ ∃ u ∈ f, P u ∧ Q u := by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u ∩ v, inter_mem huf hvf, hP inter_subset_left hPu, hQ inter_subset_right hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩

end Filter


namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

/-
**Filter.mem_principal_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_principal_self (s : Set α) : s in 𝓟 s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mem_principal_self (s : Set α) : s ∈ 𝓟 s := Subset.rfl
/-
**Filter.eventually_mem_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_mem_principal (s : Set α) : forallᶠ x in 𝓟 s, x in s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem eventually_mem_principal (s : Set α) : ∀ᶠ x in 𝓟 s, x ∈ s := mem_principal_self s

section Lattice

variable {f g : Filter α} {s t : Set α}

/-
**Filter.not_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, ¬f ≤ g ↔ ∃ s ∈ g, s ∉ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem not_le : ¬f ≤ g ↔ ∃ s ∈ g, s ∉ f := by simp_rw [le_def, not_forall, exists_prop]

/-- `GenerateSets g s`: `s` is in the filter closure of `g`. -/
/-
**Filter.GenerateSets** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u} → Set (Set α) → Set α → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GenerateSets g s`: `s` is in the filter closure of `g`.
-/
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
/-
**Filter.generate** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：generate (g : Set (Set α)) : Filter α where sets
参数：g : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`generate g` is the largest filter containing the sets `g`.
-/
def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter
/-
**Filter.mem_generate_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：mem_generate_of_mem {s : Set <| Set α} {U : Set α} (h : U in s) : U in gen
erate s
参数：h : U in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_generate_of_mem {s : Set <| Set α} {U : Set α} (h : U ∈ s) :
    U ∈ generate s := GenerateSets.basic h
/-
**Filter.le_generate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_generate_iff {s : Set (Set α)} {f : Filter α} : f <= generate s ↔ s sub
seteq f.sets
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem le_generate_iff {s : Set (Set α)} {f : Filter α} : f ≤ generate s ↔ s ⊆ f.sets :=
  Iff.intro (fun h _ hu => h <| GenerateSets.basic <| hu) fun h _ hu =>
    hu.recOn (fun h' => h h') univ_mem (fun _ hxy ↦ by gcongr) fun _ _ hx hy =>
      inter_mem hx hy
/-
**Filter.generate_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} (s : Set α), Filter.generate {s} = Filter.principal s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `Filter.mem_generate_of_mem`：mem_generate_of_mem {s : Set <| Set α} {U : 
Set α} (h : U in s) : U in generate s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_generate_iff`：le_generate_iff {s : Set (Set α)} {f : Filter α}
 : f <= generate s ↔ s subseteq f.sets
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
@[simp] lemma generate_singleton (s : Set α) : generate {s} = 𝓟 s :=
  le_antisymm (fun _t ht ↦ mem_of_superset (mem_generate_of_mem <| mem_singleton _) ht) <|
    le_generate_iff.2 <| singleton_subset_iff.2 Subset.rfl

/-- `mkOfClosure s hs` constructs a filter on `α` whose elements set is exactly
`s : Set (Set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
/-
**Filter.mkOfClosure** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u} → (s : Set (Set α)) → (Filter.generate s).sets = s → Filter α
参数：s : Set (Set α)；Filter.generate s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mkOfClosure s hs` constructs a filter on `α` whose elements set is exactly
`s : Set (Set α)`, provided one gives the assumption `hs : (generate s).sets = s
`.
-/
protected def mkOfClosure (s : Set (Set α)) (hs : (generate s).sets = s) : Filter α where
  sets := s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem
/-
**Filter.mkOfClosure_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mkOfClosure_sets {s : Set (Set α)} {hs : (generate s).sets = s} : Filter.m
kOfClosure s hs = generate s
参数：Set α；generate s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mkOfClosure_sets {s : Set (Set α)} {hs : (generate s).sets = s} :
    Filter.mkOfClosure s hs = generate s :=
  Filter.ext fun u =>
    show u ∈ (Filter.mkOfClosure s hs).sets ↔ u ∈ (generate s).sets from hs.symm ▸ Iff.rfl

/-- Galois insertion from sets of sets into filters. -/
/-
**Filter.giGenerate** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：giGenerate (α : Type*) : @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ F
ilter.generate Filter.sets where gc _ _
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_generate_iff`：le_generate_iff {s : Set (Set α)} {f : Filter α}
 : f <= generate s ↔ s subseteq f.sets

--- 原说明 ---
Galois insertion from sets of sets into filters.
-/
def giGenerate (α : Type*) :
    @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.sets where
  gc _ _ := le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets
/-
**Filter.mem_inf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_inf_iff {f g : Filter α} {s : Set α} : s in f ⊓ g ↔ exists t₁ in f, ex
ists t₂ in g, s = t₁ inter t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf_iff {f g : Filter α} {s : Set α} : s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ :=
  Iff.rfl
/-
**Filter.mem_inf_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_inf_of_left {f g : Filter α} {s : Set α} (h : s in f) : s in f ⊓ g
参数：h : s in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem mem_inf_of_left {f g : Filter α} {s : Set α} (h : s ∈ f) : s ∈ f ⊓ g :=
  ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩
/-
**Filter.mem_inf_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_inf_of_right {f g : Filter α} {s : Set α} (h : s in g) : s in f ⊓ g
参数：h : s in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem mem_inf_of_right {f g : Filter α} {s : Set α} (h : s ∈ g) : s ∈ f ⊓ g :=
  ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩
/-
**Filter.inter_mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s in f) (h
t : t in g) : s inter t in f ⊓ g
参数：hs : s in f；ht : t in g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) :
    s ∩ t ∈ f ⊓ g :=
  ⟨s, hs, t, ht, rfl⟩
/-
**Filter.mem_inf_of_inter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s in f) (ht : t in
 g) (h : s inter t subseteq u) : u in f ⊓ g
参数：hs : s in f；ht : t in g；h : s inter t subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
-/
theorem mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s ∈ f) (ht : t ∈ g)
    (h : s ∩ t ⊆ u) : u ∈ f ⊓ g :=
  mem_of_superset (inter_mem_inf hs ht) h
/-
**Filter.mem_inf_iff_superset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_inf_iff_superset {f g : Filter α} {s : Set α} : s in f ⊓ g ↔ exists t₁
 in f, exists t₂ in g, t₁ inter t₂ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Filter.mem_inf_of_inter`：mem_inf_of_inter {f g : Filter α} {s t u : Set 
α} (hs : s in f) (ht : t in g) (h : s inter t subseteq u) : u in f ⊓ g
-/
theorem mem_inf_iff_superset {f g : Filter α} {s : Set α} :
    s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ∩ t₂ ⊆ s :=
  ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨_, h₁, _, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩
/-
**Filter.mem_sdiff_iff_union** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_sdiff_iff_union {f g : Filter α} {s : Set α} : s in f \ g ↔ forall t i
n g, s union t in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
-/
theorem mem_sdiff_iff_union {f g : Filter α} {s : Set α} :
    s ∈ f \ g ↔ ∀ t ∈ g, s ∪ t ∈ f :=
  ⟨fun hs _ ht => hs (mem_of_superset ht subset_union_right) subset_union_left,
    fun h t htg hst => union_eq_right.2 hst ▸ h t htg⟩

section CompleteLattice

/-
**Filter.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} (s : Set (Filter α)), IsLUB s (sSup s)
参数：s : Set (Filter α)；sSup s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma isLUB_sSup (s : Set (Filter α)) : IsLUB s (sSup s) :=
  ⟨fun _ h₁ _ h₂ ↦ h₂ h₁, fun _ h₁ _ h₂ _ h₃ ↦ h₁ h₃ h₂⟩
/-
**Filter.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} (s : Set (Filter α)), IsGLB s (sInf s)
参数：s : Set (Filter α)；sInf s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLUB_lowerBounds`：isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s
 a
· 使用定理 `Filter.isLUB_sSup`：∀ {α : Type u} (s : Set (Filter α)), IsLUB s (sSup s)
· 使用定理 `Filter.sSup_lowerBounds`：∀ {α : Type u_1} (s : Set (Filter α)), sSup (lo
werBounds s) = sInf s
-/
protected lemma isGLB_sInf (s : Set (Filter α)) : IsGLB s (sInf s) :=
  isLUB_lowerBounds.mp (Filter.sSup_lowerBounds _ ▸ Filter.isLUB_sSup _)

/-- Complete lattice structure on `Filter α`. -/
/-
**Filter.instCompleteLatticeFilter** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instCompleteLatticeFilter : CompleteLattice (Filter α) where inf a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_inf_of_left`：mem_inf_of_left {f g : Filter α} {s : Set α} (h 
: s in f) : s in f ⊓ g
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.isLUB_sSup`：∀ {α : Type u} (s : Set (Filter α)), IsLUB s (sSup s)
· 使用定理 `Filter.isGLB_sInf`：∀ {α : Type u} (s : Set (Filter α)), IsGLB s (sInf s)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `trivial`：True

--- 原说明 ---
Complete lattice structure on `Filter α`.
-/
instance instCompleteLatticeFilter : CompleteLattice (Filter α) where
  inf a b := min a b
  sup a b := max a b
  le_sup_left _ _ _ h := h.1
  le_sup_right _ _ _ h := h.2
  sup_le _ _ _ h₁ h₂ _ h := ⟨h₁ h, h₂ h⟩
  inf_le_left _ _ _ := mem_inf_of_left
  inf_le_right _ _ _ := mem_inf_of_right
  le_inf := fun _ _ _ h₁ h₂ _s ⟨_a, ha, _b, hb, hs⟩ => hs.symm ▸ inter_mem (h₁ ha) (h₂ hb)
  isLUB_sSup := Filter.isLUB_sSup
  isGLB_sInf := Filter.isGLB_sInf
  le_top _ _ := univ_mem'
  bot_le _ _ _ := trivial
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Filter α) := ⟨⊥⟩

end CompleteLattice

/-
**Filter.NeBot.ne** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne'`：∀ {α : Type u_1} {f : Filter α} [self : f.NeBot], f ≠ 
⊥
-/
theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f ≠ ⊥ := hf.ne'

@[simp, push]
/-
**Filter.not_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
-/
theorem not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥ := neBot_iff.not_left

@[gcongr]
/-
**Filter.NeBot.mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.NeBot
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Filter.NeBot.ne'`：∀ {α : Type u_1} {f : Filter α} [self : f.NeBot], f ≠ 
⊥
-/
theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f ≤ g) : NeBot g :=
  ⟨ne_bot_of_le_ne_bot hf.1 hg⟩
/-
**Filter.neBot_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f <= g) : NeBot g
参数：hg : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
-/
theorem neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f ≤ g) : NeBot g :=
  hf.mono hg
/-
**Filter.sup_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, (f ⊔ g).NeBot ↔ f.NeBot ∨ g.NeBot
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem sup_neBot {f g : Filter α} : NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g := by
  simp only [neBot_iff, not_and_or, Ne, sup_eq_bot_iff]
/-
**Filter.neBot_sup_of_left** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：neBot_sup_of_left {f g : Filter α} [f.NeBot] : NeBot (f ⊔ g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
instance neBot_sup_of_left {f g : Filter α} [f.NeBot] : NeBot (f ⊔ g) := by simp [*]
/-
**Filter.neBot_sup_of_right** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：neBot_sup_of_right {f g : Filter α} [g.NeBot] : NeBot (f ⊔ g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
instance neBot_sup_of_right {f g : Filter α} [g.NeBot] : NeBot (f ⊔ g) := by simp [*]
/-
**Filter.not_disjoint_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_disjoint_self_iff : ¬Disjoint f f ↔ f.NeBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_disjoint_self_iff : ¬Disjoint f f ↔ f.NeBot := by rw [disjoint_self, neBot_iff]
/-
**Filter.bot_sets_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bot_sets_eq : (⊥ : Filter α).sets = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_sets_eq : (⊥ : Filter α).sets = univ := rfl

/-- Either `f = ⊥` or `Filter.NeBot f`. This is a version of `eq_or_ne` that uses `Filter.NeBot`
as the second alternative, to be used as an instance. -/
/-
**Filter.eq_or_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y

--- 原说明 ---
Either `f = ⊥` or `Filter.NeBot f`. This is a version of `eq_or_ne` that uses `F
ilter.NeBot`
as the second alternative, to be used as an instance.
-/
theorem eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f := (eq_or_ne f ⊥).imp_right NeBot.mk
/-
**Filter.sup_sets_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_sets_eq {f g : Filter α} : (f ⊔ g).sets = f.sets inter g.sets
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem sup_sets_eq {f g : Filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
  (giGenerate α).gc.u_inf
/-
**Filter.sSup_sets_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sSup_sets_eq {s : Set (Filter α)} : (sSup s).sets = ⋂ f in s, (f : Filter 
α).sets
参数：Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem sSup_sets_eq {s : Set (Filter α)} : (sSup s).sets = ⋂ f ∈ s, (f : Filter α).sets :=
  (giGenerate α).gc.u_sInf
/-
**Filter.iSup_sets_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_sets_eq {f : ι -> Filter α} : (iSup f).sets = ⋂ i, (f i).sets
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem iSup_sets_eq {f : ι → Filter α} : (iSup f).sets = ⋂ i, (f i).sets :=
  (giGenerate α).gc.u_iInf
/-
**Filter.generate_empty** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_empty : Filter.generate ∅ = (⊤ : Filter α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem generate_empty : Filter.generate ∅ = (⊤ : Filter α) :=
  (giGenerate α).gc.l_bot
/-
**Filter.generate_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_univ : Filter.generate univ = (⊥ : Filter α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem generate_univ : Filter.generate univ = (⊥ : Filter α) :=
  bot_unique fun _ _ => GenerateSets.basic (mem_univ _)
/-
**Filter.generate_union** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_union {s t : Set (Set α)} : Filter.generate (s union t) = Filter.
generate s ⊓ Filter.generate t
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem generate_union {s t : Set (Set α)} :
    Filter.generate (s ∪ t) = Filter.generate s ⊓ Filter.generate t :=
  (giGenerate α).gc.l_sup
/-
**Filter.generate_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_iUnion {s : ι -> Set (Set α)} : Filter.generate (⋃ i, s i) = ⨅ i,
 Filter.generate (s i)
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem generate_iUnion {s : ι → Set (Set α)} :
    Filter.generate (⋃ i, s i) = ⨅ i, Filter.generate (s i) :=
  (giGenerate α).gc.l_iSup

@[simp]
/-
**Filter.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in f ∧ s in g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sup {f g : Filter α} {s : Set α} : s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
  Iff.rfl
/-
**Filter.union_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：union_mem_sup {f g : Filter α} {s t : Set α} (hs : s in f) (ht : t in g) :
 s union t in f ⊔ g
参数：hs : s in f；ht : t in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem union_mem_sup {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∪ t ∈ f ⊔ g :=
  ⟨mem_of_superset hs subset_union_left, mem_of_superset ht subset_union_right⟩

@[simp]
/-
**Filter.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iSup {x : Set α} {f : ι -> Filter α} : x in iSup f ↔ forall i, x in f 
i
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
· 使用定理 `Filter.iSup_sets_eq`：iSup_sets_eq {f : ι -> Filter α} : (iSup f).sets = 
⋂ i, (f i).sets
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iSup {x : Set α} {f : ι → Filter α} : x ∈ iSup f ↔ ∀ i, x ∈ f i := by
  simp only [← Filter.mem_sets, iSup_sets_eq, mem_iInter]

@[simp]
/-
**Filter.iSup_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_neBot {f : ι -> Filter α} : (⨆ i, f i).NeBot ↔ exists i, (f i).NeBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_neBot {f : ι → Filter α} : (⨆ i, f i).NeBot ↔ ∃ i, (f i).NeBot := by
  simp [neBot_iff]
/-
**Filter.iInf_eq_generate** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_eq_generate (s : ι -> Filter α) : iInf s = generate (⋃ i, (s i).sets)
参数：s : ι -> Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInf_eq_generate (s : ι → Filter α) : iInf s = generate (⋃ i, (s i).sets) :=
  eq_of_forall_le_iff fun _ ↦ by simp [le_generate_iff]
/-
**Filter.mem_iInf_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} (hs : s in f i) : s in ⨅ i
, f i
参数：i : ι；hs : s in f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem mem_iInf_of_mem {f : ι → Filter α} (i : ι) {s} (hs : s ∈ f i) : s ∈ ⨅ i, f i :=
  iInf_le f i hs

@[elab_as_elim]
/-
**Filter.iInf_sets_induct** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_sets_induct {f : ι -> Filter α} {s : Set α} (hs : s in iInf f) {p : S
et α -> Prop} (uni : p univ) (ins : forall {i s₁ s₂}, s₁ in f i -> p s₂ -> p (s₁
 inter s₂)) : p s
参数：hs : s in iInf f；uni : p univ；ins : forall {i s₁ s₂}, s₁ in f i -> p s₂ -> p 
(s₁ inter s₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.union_inter_distrib_left`：union_inter_distrib_left (s t u : Set α) :
 s union t inter u = (s union t) inter (s union u)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_eq_left`：union_eq_left {s t : Set α} : s union t = s ↔ t subse
teq s
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem iInf_sets_induct {f : ι → Filter α} {s : Set α} (hs : s ∈ iInf f) {p : Set α → Prop}
    (uni : p univ) (ins : ∀ {i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) : p s := by
  have p_of_f : ∀ i, ∀ s ∈ f i, p s := fun i s hs ↦ by simpa using ins hs uni
  let q : Set α → Prop := fun t ↦ t ∈ iInf f ∧ ∀ t', t ⊆ t' → p t'
  have q_mono : Monotone q := fun a b hab ha ↦
    ⟨mem_of_superset ha.1 hab, fun t hbt ↦ ha.2 _ (hab.trans hbt)⟩
  have A : ∀ i, ∀ s ∈ f i, ∀ t, q t → q (s ∩ t) := fun i s hs t ht ↦ by
    use inter_mem (mem_iInf_of_mem _ hs) ht.1
    intro u hu
    have : u = (u ∪ s) ∩ (u ∪ t) := by
      rwa [← union_eq_left, union_inter_distrib_left, eq_comm] at hu
    rw [this]
    exact ins (mem_of_superset hs subset_union_right) (ht.2 _ subset_union_right)
  have B : ∀ s t, q s → q t → q (s ∩ t) := fun s t hqs hqt ↦ by
    let 𝓕 : Filter α :=
    { sets := {s | ∀ t, q t → q (s ∩ t)}
      univ_sets := by simp
      sets_of_superset ha hab t ht := q_mono (inter_subset_inter_left _ hab) (ha t ht)
      inter_sets ha hb t ht := by simpa [inter_assoc] using ha _ (hb _ ht) }
    exact (le_iInf_iff.mpr A : 𝓕 ≤ iInf f) hqs.1 _ hqt
  have C : ∀ i, ∀ s ∈ f i, q s := fun i s hs ↦
    ⟨mem_iInf_of_mem _ hs, fun t hst ↦ p_of_f _ _ (mem_of_superset hs hst)⟩
  let 𝓖 : Filter α :=
  { sets := {t | q t}
    univ_sets := by simpa [q] using uni
    sets_of_superset ha hab :=
      ⟨mem_of_superset ha.1 hab, fun t hbt ↦ ha.2 _ (hab.trans hbt)⟩
    inter_sets := B _ _ }
  have : 𝓖 ≤ iInf f := le_iInf_iff.mpr C
  exact (this hs).2 s subset_rfl

@[simp]
/-
**Filter.le_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_principal_iff {s : Set α} {f : Filter α} : f <= 𝓟 s ↔ s in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩
/-
**Filter.Iic_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：Iic_principal (s : Set α) : Iic (𝓟 s) = { l | s in l }
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem Iic_principal (s : Set α) : Iic (𝓟 s) = { l | s ∈ l } :=
  Set.ext fun _ => le_principal_iff

@[gcongr]
/-
**Filter.principal_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem principal_mono {s t : Set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  simp only [le_principal_iff, mem_principal]

@[mono]
/-
**Filter.monotone_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：monotone_principal : Monotone (𝓟 : Set α -> Filter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem monotone_principal : Monotone (𝓟 : Set α → Filter α) := fun _ _ => principal_mono.2
/-
**Filter.principal_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {s t : Set α}, Filter.principal s = Filter.principal t ↔ s 
= t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem principal_eq_iff_eq {s t : Set α} : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal]
/-
**Filter.join_principal_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {s : Set (Filter α)}, (Filter.principal s).join = sSup s
参数：Filter α；Filter.principal s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem join_principal_eq_sSup {s : Set (Filter α)} : join (𝓟 s) = sSup s := rfl
/-
**Filter.principal_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u}, Filter.principal Set.univ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem principal_univ : 𝓟 (univ : Set α) = ⊤ :=
  top_unique <| by simp only [le_principal_iff, mem_top]

@[simp]
/-
**Filter.principal_empty** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_empty : 𝓟 (∅ : Set α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem principal_empty : 𝓟 (∅ : Set α) = ⊥ :=
  bot_unique fun _ _ => empty_subset _
/-
**Filter.generate_eq_biInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_eq_biInf (S : Set (Set α)) : generate S = ⨅ s in S, 𝓟 s
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem generate_eq_biInf (S : Set (Set α)) : generate S = ⨅ s ∈ S, 𝓟 s :=
  eq_of_forall_le_iff fun f => by simp [le_generate_iff, le_principal_iff, subset_def]

/-! ### Lattice equations -/

/-
**Filter.empty_mem_iff_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Filter.mem_bot`：mem_bot {s : Set α} : s in (⊥ : Filter α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### Lattice equations
-/
theorem empty_mem_iff_bot {f : Filter α} : ∅ ∈ f ↔ f = ⊥ :=
  ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩
/-
**Filter.nonempty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s in f) : 
s.Nonempty
参数：hs : s in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.NeBot.ne'`：∀ {α : Type u_1} {f : Filter α} [self : f.NeBot], f ≠ 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id
/-
**Filter.NeBot.nonempty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀ {s : Set α}, s ∈ f → s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
-/
theorem NeBot.nonempty_of_mem {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  @Filter.nonempty_of_mem α f hf s hs

@[simp]
/-
**Filter.empty_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：empty_notMem (f : Filter α) [NeBot f] : ∅ ∉ f
参数：f : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
-/
theorem empty_notMem (f : Filter α) [NeBot f] : ∅ ∉ f := fun h => (nonempty_of_mem h).ne_empty rfl
/-
**Filter.nonempty_of_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：nonempty_of_neBot (f : Filter α) [NeBot f] : Nonempty α
参数：f : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem nonempty_of_neBot (f : Filter α) [NeBot f] : Nonempty α :=
  Exists.nonempty <| nonempty_of_mem (univ_mem : univ ∈ f)
/-
**Filter.compl_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_notMem {f : Filter α} {s : Set α} [NeBot f] (h : s in f) : sᶜ ∉ f
参数：h : s in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
-/
theorem compl_notMem {f : Filter α} {s : Set α} [NeBot f] (h : s ∈ f) : sᶜ ∉ f := fun hsc =>
  (nonempty_of_mem (inter_mem h hsc)).ne_empty <| inter_compl_self s
/-
**Filter.filter_eq_bot_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：filter_eq_bot_of_isEmpty [IsEmpty α] (f : Filter α) : f = ⊥
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem filter_eq_bot_of_isEmpty [IsEmpty α] (f : Filter α) : f = ⊥ :=
  empty_mem_iff_bot.mp <| univ_mem' isEmptyElim
/-
**Filter.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f g : Filter α}, Disjoint f g ↔ ∃ s ∈ f, ∃ t ∈ g, Disjoint
 s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma disjoint_iff {f g : Filter α} : Disjoint f g ↔ ∃ s ∈ f, ∃ t ∈ g, Disjoint s t := by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]
/-
**Filter.disjoint_of_disjoint_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s
 t) (hs : s in f) (ht : t in g) : Disjoint f g
参数：h : Disjoint s t；hs : s in f；ht : t in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.disjoint_iff`：∀ {α : Type u} {f g : Filter α}, Disjoint f g ↔ ∃ s
 ∈ f, ∃ t ∈ g, Disjoint s t
-/
theorem disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s ∈ f)
    (ht : t ∈ g) : Disjoint f g :=
  Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩
/-
**Filter.NeBot.not_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} {f : Filter α} {s t : Set α}, f.NeBot → s ∈ f → t ∈ f → ¬Di
sjoint s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.not_disjoint_self_iff`：not_disjoint_self_iff : ¬Disjoint f f ↔ f.
NeBot
· 使用定理 `Filter.disjoint_iff`：∀ {α : Type u} {f g : Filter α}, Disjoint f g ↔ ∃ s
 ∈ f, ∃ t ∈ g, Disjoint s t
-/
theorem NeBot.not_disjoint (hf : f.NeBot) (hs : s ∈ f) (ht : t ∈ f) : ¬Disjoint s t := fun h =>
  not_disjoint_self_iff.2 hf <| Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩
/-
**Filter.inf_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_eq_bot_iff {f g : Filter α} : f ⊓ g = ⊥ ↔ exists U in f, exists V in g
, U inter V = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inf_eq_bot_iff {f g : Filter α} : f ⊓ g = ⊥ ↔ ∃ U ∈ f, ∃ V ∈ g, U ∩ V = ∅ := by
  simp only [← disjoint_iff, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty]

/-- There is exactly one filter on an empty type. -/
/-
**Filter.unique** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：unique [IsEmpty α] : Unique (Filter α) where default
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥

--- 原说明 ---
There is exactly one filter on an empty type.
-/
instance unique [IsEmpty α] : Unique (Filter α) where
  default := ⊥
  uniq := filter_eq_bot_of_isEmpty
/-
**Filter.NeBot.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} (f : Filter α) [hf : f.NeBot], Nonempty α
参数：f : Filter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem NeBot.nonempty (f : Filter α) [hf : f.NeBot] : Nonempty α :=
  not_isEmpty_iff.mp fun _ ↦ hf.ne (Subsingleton.elim _ _)

/-- There are only two filters on a `Subsingleton`: `⊥` and `⊤`. If the type is empty, then they are
equal. -/
/-
**Filter.eq_top_of_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_top_of_neBot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤
参数：l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.eq_univ_of_nonempty`：eq_univ_of_nonempty {s : Set α} : s.No
nempty -> s = univ
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty

--- 原说明 ---
There are only two filters on a `Subsingleton`: `⊥` and `⊤`. If the type is empt
y, then they are
equal.
-/
theorem eq_top_of_neBot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤ := by
  refine top_unique fun s hs => ?_
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem
/-
**Filter.forall_mem_nonempty_iff_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：forall_mem_nonempty_iff_neBot {f : Filter α} : (forall s : Set α, s in f -
> s.Nonempty) ↔ NeBot f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.not_nonempty_empty`：not_nonempty_empty : ¬(∅ : Set α).Nonempty
· 使用定理 `Filter.mem_bot`：mem_bot {s : Set α} : s in (⊥ : Filter α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
-/
theorem forall_mem_nonempty_iff_neBot {f : Filter α} :
    (∀ s : Set α, s ∈ f → s.Nonempty) ↔ NeBot f :=
  ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩
/-
**Filter.instNeBotTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instNeBotTop [Nonempty α] : NeBot (⊤ : Filter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.forall_mem_nonempty_iff_neBot`：forall_mem_nonempty_iff_neBot {f :
 Filter α} : (forall s : Set α, s in f -> s.Nonempty) ↔ NeBot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_top`：mem_top {s : Set α} : s in (⊤ : Filter α) ↔ s = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
-/
instance instNeBotTop [Nonempty α] : NeBot (⊤ : Filter α) :=
  forall_mem_nonempty_iff_neBot.1 fun s hs => by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]
/-
**Filter.instNontrivialFilter** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instNontrivialFilter [Nonempty α] : Nontrivial (Filter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
-/
instance instNontrivialFilter [Nonempty α] : Nontrivial (Filter α) :=
  ⟨⟨⊤, ⊥, instNeBotTop.ne⟩⟩
/-
**Filter.nontrivial_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
theorem nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α :=
  ⟨fun _ =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.instNontrivialFilter α⟩
/-
**Filter.eq_sInf_of_mem_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_sInf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α} (h : for
all {s}, s in l ↔ exists f in S, s in f) : l = sInf S
参数：Filter α；h : forall {s}, s in l ↔ exists f in S, s in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem eq_sInf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = sInf S :=
  le_antisymm (le_sInf fun f hf _ hs => h.2 ⟨f, hf, hs⟩)
    fun _ hs => let ⟨_, hf, hs⟩ := h.1 hs; (sInf_le hf) hs
/-
**Filter.eq_iInf_of_mem_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_iInf_of_mem_iff_exists_mem {f : ι -> Filter α} {l : Filter α} (h : fora
ll {s}, s in l ↔ exists i, s in f i) : l = iInf f
参数：h : forall {s}, s in l ↔ exists i, s in f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_sInf_of_mem_iff_exists_mem`：eq_sInf_of_mem_iff_exists_mem {S :
 Set (Filter α)} {l : Filter α} (h : forall {s}, s in l ↔ exists f in S, s in f)
 : l = sInf S
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
-/
theorem eq_iInf_of_mem_iff_exists_mem {f : ι → Filter α} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) : l = iInf f :=
  eq_sInf_of_mem_iff_exists_mem <| h.trans (exists_range_iff (p := (_ ∈ ·))).symm
/-
**Filter.eq_biInf_of_mem_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_biInf_of_mem_iff_exists_mem {f : ι -> Filter α} {p : ι -> Prop} {l : Fi
lter α} (h : forall {s}, s in l ↔ exists i, p i ∧ s in f i) : l = ⨅ (i) (_ : p i
), f i
参数：h : forall {s}, s in l ↔ exists i, p i ∧ s in f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `Filter.eq_iInf_of_mem_iff_exists_mem`：eq_iInf_of_mem_iff_exists_mem {f :
 ι -> Filter α} {l : Filter α} (h : forall {s}, s in l ↔ exists i, s in f i) : l
 = iInf f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_biInf_of_mem_iff_exists_mem {f : ι → Filter α} {p : ι → Prop} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, p i ∧ s ∈ f i) : l = ⨅ (i) (_ : p i), f i := by
  rw [iInf_subtype']
  exact eq_iInf_of_mem_iff_exists_mem fun {_} => by simp only [Subtype.exists, h, exists_prop]
/-
**Filter.iInf_sets_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_sets_eq {f : ι -> Filter α} (h : Directed (· >= ·) f) [ne : Nonempty 
ι] : (iInf f).sets = ⋃ i, (f i).sets
参数：h : Directed (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.eq_iInf_of_mem_iff_exists_mem`：eq_iInf_of_mem_iff_exists_mem {f :
 ι -> Filter α} {l : Filter α} (h : forall {s}, s in l ↔ exists i, s in f i) : l
 = iInf f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iInf_sets_eq {f : ι → Filter α} (h : Directed (· ≥ ·) f) [ne : Nonempty ι] :
    (iInf f).sets = ⋃ i, (f i).sets :=
  let ⟨i⟩ := ne
  let u :=
    { sets := ⋃ i, (f i).sets
      univ_sets := mem_iUnion.2 ⟨i, univ_mem⟩
      sets_of_superset := by
        simp only [mem_iUnion, exists_imp]
        exact fun i hx hxy => ⟨i, mem_of_superset hx hxy⟩
      inter_sets := by
        simp only [mem_iUnion, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = iInf f := eq_iInf_of_mem_iff_exists_mem mem_iUnion
  congr_arg Filter.sets this.symm
/-
**Filter.mem_iInf_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_of_directed {f : ι -> Filter α} (h : Directed (· >= ·) f) [Nonemp
ty ι] (s) : s in iInf f ↔ exists i, s in f i
参数：h : Directed (· >= ·) f；s。
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
· 使用定理 `Filter.iInf_sets_eq`：iInf_sets_eq {f : ι -> Filter α} (h : Directed (· >
= ·) f) [ne : Nonempty ι] : (iInf f).sets = ⋃ i, (f i).sets
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf_of_directed {f : ι → Filter α} (h : Directed (· ≥ ·) f) [Nonempty ι] (s) :
    s ∈ iInf f ↔ ∃ i, s ∈ f i := by
  simp only [← Filter.mem_sets, iInf_sets_eq h, mem_iUnion]
/-
**Filter.mem_biInf_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_biInf_of_directed {f : β -> Filter α} {s : Set β} (h : DirectedOn (f ⁻
¹'o (· >= ·)) s) (ne : s.Nonempty) {t : Set α} : (t in ⨅ i in s, f i) ↔ exists i
 in s, t in f i
参数：h : DirectedOn (f ⁻¹'o (· >= ·)) s；ne : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_biInf_of_directed {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) {t : Set α} : (t ∈ ⨅ i ∈ s, f i) ↔ ∃ i ∈ s, t ∈ f i := by
  have := ne.to_subtype
  simp_rw [iInf_subtype', mem_iInf_of_directed h.directed_val, Subtype.exists, exists_prop]
/-
**Filter.biInf_sets_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：biInf_sets_eq {f : β -> Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· >
= ·)) s) (ne : s.Nonempty) : (⨅ i in s, f i).sets = ⋃ i in s, (f i).sets
参数：h : DirectedOn (f ⁻¹'o (· >= ·)) s；ne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_biInf_of_directed`：mem_biInf_of_directed {f : β -> Filter α} 
{s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s) (ne : s.Nonempty) {t : Set α} :
 (t in ⨅ i in s, f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biInf_sets_eq {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) : (⨅ i ∈ s, f i).sets = ⋃ i ∈ s, (f i).sets :=
  ext fun t => by simp [mem_biInf_of_directed h ne]

@[simp]
/-
**Filter.sup_join** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_join {f₁ f₂ : Filter (Filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂)
参数：Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_join {f₁ f₂ : Filter (Filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂) :=
  Filter.ext fun x => by simp only [mem_sup, mem_join]

@[simp]
/-
**Filter.iSup_join** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_join {ι : Sort w} {f : ι -> Filter (Filter α)} : ⨆ x, join (f x) = jo
in (⨆ x, f x)
参数：Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_join {ι : Sort w} {f : ι → Filter (Filter α)} : ⨆ x, join (f x) = join (⨆ x, f x) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_join]


/-- The dual version does not hold! `Filter α` is not a `CompleteDistribLattice`. -/
/-
**Filter.instCoframe** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instCoframe : Coframe (Filter α) where sdiff_le_iff a b c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual version does not hold! `Filter α` is not a `CompleteDistribLattice`.
-/
instance instCoframe : Coframe (Filter α) where
  sdiff_le_iff a b c :=
    ⟨fun h s hs ↦ h hs.right hs.left (subset_refl s),
      fun h s hsc t htb hst ↦ h ⟨htb, mem_of_superset hsc hst⟩⟩
  top_sdiff f := by
    ext s
    simp only [mem_sdiff_iff_union, Filter.hnot_def, mem_principal, compl_subset_iff_union,
      mem_top_iff_forall, eq_univ_iff_forall, ker, mem_union, mem_sInter, Filter.mem_sets]
    grind

/-- If `f : ι → Filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `iInf f ≠ ⊥`.
See also `iInf_neBot_of_directed` for a version assuming `Nonempty α` instead of `Nonempty ι`. -/
/-
**Filter.iInf_neBot_of_directed'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_neBot_of_directed' {f : ι -> Filter α} [Nonempty ι] (hd : Directed (·
 >= ·) f) : (forall i, NeBot (f i)) -> NeBot (iInf f)
参数：hd : Directed (· >= ·) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If `f : ι → Filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `i
Inf f ≠ ⊥`.
See also `iInf_neBot_of_directed` for a version assuming `Nonempty α` instead of
 `Nonempty ι`.
-/
theorem iInf_neBot_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    (∀ i, NeBot (f i)) → NeBot (iInf f) :=
  not_imp_not.1 <| by simpa only [not_forall, not_neBot, ← empty_mem_iff_bot,
    mem_iInf_of_directed hd] using id

/-- If `f : ι → Filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `iInf f ≠ ⊥`.
See also `iInf_neBot_of_directed'` for a version assuming `Nonempty ι` instead of `Nonempty α`. -/
/-
**Filter.iInf_neBot_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_neBot_of_directed {f : ι -> Filter α} [hn : Nonempty α] (hd : Directe
d (· >= ·) f) (hb : forall i, NeBot (f i)) : NeBot (iInf f)
参数：hd : Directed (· >= ·) f；hb : forall i, NeBot (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.iInf_neBot_of_directed'`：iInf_neBot_of_directed' {f : ι -> Filter
 α} [Nonempty ι] (hd : Directed (· >= ·) f) : (forall i, NeBot (f i)) -> NeBot (
iInf f)

--- 原说明 ---
If `f : ι → Filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `i
Inf f ≠ ⊥`.
See also `iInf_neBot_of_directed'` for a version assuming `Nonempty ι` instead o
f `Nonempty α`.
-/
theorem iInf_neBot_of_directed {f : ι → Filter α} [hn : Nonempty α] (hd : Directed (· ≥ ·) f)
    (hb : ∀ i, NeBot (f i)) : NeBot (iInf f) := by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [iInf_of_empty f, top_ne_bot]
  · exact iInf_neBot_of_directed' hd hb
/-
**Filter.sInf_neBot_of_directed'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sInf_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : Dire
ctedOn (· >= ·) s) (hbot : ⊥ ∉ s) : NeBot (sInf s)
参数：Filter α；hne : s.Nonempty；hd : DirectedOn (· >= ·) s；hbot : ⊥ ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.iInf_neBot_of_directed'`：iInf_neBot_of_directed' {f : ι -> Filter
 α} [Nonempty ι] (hd : Directed (· >= ·) f) : (forall i, NeBot (f i)) -> NeBot (
iInf f)
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
-/
theorem sInf_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    @iInf_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨_, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩
/-
**Filter.sInf_neBot_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sInf_neBot_of_directed [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn 
(· >= ·) s) (hbot : ⊥ ∉ s) : NeBot (sInf s)
参数：Filter α；hd : DirectedOn (· >= ·) s；hbot : ⊥ ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.iInf_neBot_of_directed`：iInf_neBot_of_directed {f : ι -> Filter α
} [hn : Nonempty α] (hd : Directed (· >= ·) f) (hb : forall i, NeBot (f i)) : Ne
Bot (iInf f)
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
-/
theorem sInf_neBot_of_directed [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    iInf_neBot_of_directed hd.directed_val fun ⟨_, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩
/-
**Filter.iInf_neBot_iff_of_directed'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_neBot_iff_of_directed' {f : ι -> Filter α} [Nonempty ι] (hd : Directe
d (· >= ·) f) : NeBot (iInf f) ↔ forall i, NeBot (f i)
参数：hd : Directed (· >= ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Filter.iInf_neBot_of_directed'`：iInf_neBot_of_directed' {f : ι -> Filter
 α} [Nonempty ι] (hd : Directed (· >= ·) f) : (forall i, NeBot (f i)) -> NeBot (
iInf f)
-/
theorem iInf_neBot_iff_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    NeBot (iInf f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed' hd⟩
/-
**Filter.iInf_neBot_iff_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_neBot_iff_of_directed {f : ι -> Filter α} [Nonempty α] (hd : Directed
 (· >= ·) f) : NeBot (iInf f) ↔ forall i, NeBot (f i)
参数：hd : Directed (· >= ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Filter.iInf_neBot_of_directed`：iInf_neBot_of_directed {f : ι -> Filter α
} [hn : Nonempty α] (hd : Directed (· >= ·) f) (hb : forall i, NeBot (f i)) : Ne
Bot (iInf f)
-/
theorem iInf_neBot_iff_of_directed {f : ι → Filter α} [Nonempty α] (hd : Directed (· ≥ ·) f) :
    NeBot (iInf f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed hd⟩

/-! #### `principal` equations -/

@[simp]
/-
**Filter.inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s inter t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
#### `principal` equations
-/
theorem inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) :=
  le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, Subset.rfl, t, Subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp]
/-
**Filter.sup_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) :=
  Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]

@[simp]
/-
**Filter.iSup_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_principal {ι : Sort w} {s : ι -> Set α} : ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_principal {ι : Sort w} {s : ι → Set α} : ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_principal, iUnion_subset_iff]

@[simp]
/-
**Filter.principal_sdiff_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_sdiff_principal {s t : Set α} : 𝓟 s \ 𝓟 t = 𝓟 (s \ t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem principal_sdiff_principal {s t : Set α} : 𝓟 s \ 𝓟 t = 𝓟 (s \ t) :=
  Filter.ext fun _ => by simp [← le_principal_iff, principal_mono]

@[simp]
/-
**Filter.hnot_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hnot_principal {s : Set α} : ￢𝓟 s = 𝓟 sᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a
· 使用定理 `Filter.principal_sdiff_principal`：principal_sdiff_principal {s t : Set α
} : 𝓟 s \ 𝓟 t = 𝓟 (s \ t)
-/
theorem hnot_principal {s : Set α} : ￢𝓟 s = 𝓟 sᶜ := by
  simpa [← compl_eq_univ_sdiff] using @principal_sdiff_principal _ univ s

@[simp]
/-
**Filter.principal_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
-/
theorem principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
  empty_mem_iff_bot.symm.trans <| mem_principal.trans subset_empty_iff

@[simp]
/-
**Filter.principal_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_neBot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Filter.principal_eq_bot_iff`：principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ 
↔ s = ∅
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem principal_neBot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty :=
  neBot_iff.trans <| (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm

alias ⟨_, _root_.Set.Nonempty.principal_neBot⟩ := principal_neBot_iff
/-
**Filter.isCompl_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isCompl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 sᶜ)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem isCompl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 sᶜ) :=
  IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) <| by
    rw [sup_principal, union_compl_self, principal_univ]
/-
**Filter.mem_inf_principal'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_inf_principal' {f : Filter α} {s t : Set α} : s in f ⊓ 𝓟 t ↔ tᶜ union 
s in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.le_left_iff`：le_left_iff (h : IsCompl x y) : z <= x ↔ Disjoint z
 y
· 使用定理 `Filter.isCompl_principal`：isCompl_principal (s : Set α) : IsCompl (𝓟 s) 
(𝓟 sᶜ)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.le_right_iff`：le_right_iff (h : IsCompl x y) : z <= y ↔ Disjoint
 z x
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_inf_principal' {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ tᶜ ∪ s ∈ f := by
  simp only [← le_principal_iff, (isCompl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (isCompl_principal (t ∩ sᶜ)).le_right_iff, compl_inter, compl_compl]
/-
**Filter.mem_inf_principal** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：mem_inf_principal {f : Filter α} {s t : Set α} : s in f ⊓ 𝓟 t ↔ { x | x in
 t -> x in s } in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_inf_principal {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ { x | x ∈ t → x ∈ s } ∈ f := by
  simp only [mem_inf_principal', imp_iff_not_or, ofPred_or, compl_def, ofPred_mem_eq]
/-
**Filter.iSup_inf_principal** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：iSup_inf_principal (f : ι -> Filter α) (s : Set α) : ⨆ i, f i ⊓ 𝓟 s = (⨆ i
, f i) ⊓ 𝓟 s
参数：f : ι -> Filter α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_inf_principal (f : ι → Filter α) (s : Set α) : ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s := by
  ext
  simp only [mem_iSup, mem_inf_principal]
/-
**Filter.inf_principal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_principal_eq_bot {f : Filter α} {s : Set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inf_principal_eq_bot {f : Filter α} {s : Set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ ∈ f := by
  rw [← empty_mem_iff_bot, mem_inf_principal]
  simp only [mem_empty_iff_false, imp_false, compl_def]
/-
**Filter.mem_of_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 sᶜ = ⊥) : s in f
参数：h : f ⊓ 𝓟 sᶜ = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.inf_principal_eq_bot`：inf_principal_eq_bot {f : Filter α} {s : Se
t α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f
-/
theorem mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 sᶜ = ⊥) : s ∈ f := by
  rwa [inf_principal_eq_bot, compl_compl] at h
/-
**Filter.sdiff_mem_inf_principal_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sdiff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s in f) (t 
: Set α) : s \ t in f ⊓ 𝓟 tᶜ
参数：hs : s in f；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem sdiff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s ∈ f) (t : Set α) :
    s \ t ∈ f ⊓ 𝓟 tᶜ :=
  inter_mem_inf hs <| mem_principal_self tᶜ

@[deprecated (since := "2026-06-03")]
alias diff_mem_inf_principal_compl := sdiff_mem_inf_principal_compl
/-
**Filter.principal_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s <= f ↔ forall V in f, s 
subseteq V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s ≤ f ↔ ∀ V ∈ f, s ⊆ V := by
  simp_rw [le_def, mem_principal]

end Lattice

@[mono, gcongr]
/-
**Filter.join_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ <= f₂) : join f₁ <= join f₂
参数：Filter α；h : f₁ <= f₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ ≤ f₂) : join f₁ ≤ join f₂ := fun _ hs => h hs

/-! ### Eventually -/

/-
**Filter.eventually_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_iff {f : Filter α} {P : α -> Prop} : (forallᶠ x in f, P x) ↔ { 
x | P x } in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Eventually
-/
theorem eventually_iff {f : Filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ { x | P x } ∈ f :=
  Iff.rfl

@[simp]
/-
**Filter.eventually_mem_set** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_mem_set {s : Set α} {l : Filter α} : (forallᶠ x in l, x in s) ↔
 s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_mem_set {s : Set α} {l : Filter α} : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l :=
  Iff.rfl
/-
**Filter.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {f₁ f₂ : Filter α}, (∀ (p : α → Prop), (∀ᶠ (x : α) in f₁, p
 x) ↔ ∀ᶠ (x : α) in f₂, p x) → f₁ = f₂
参数：∀ (p : α → Prop), (∀ᶠ (x : α) in f₁, p x) ↔ ∀ᶠ (x : α) in f₂, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Set.ofPred_bijective`：ofPred_bijective : Bijective (ofPred : (α -> Prop)
 -> Set α)
-/
protected theorem ext' {f₁ f₂ : Filter α}
    (h : ∀ p : α → Prop, (∀ᶠ x in f₁, p x) ↔ ∀ᶠ x in f₂, p x) : f₁ = f₂ :=
  Filter.ext <| Set.ofPred_bijective.surjective.forall.mpr h
/-
**Filter.Eventually.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α)
 in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
参数：∀ᶠ (x : α) in f₂, p x；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Eventually.filter_mono {f₁ f₂ : Filter α} (h : f₁ ≤ f₂) {p : α → Prop}
    (hp : ∀ᶠ x in f₂, p x) : ∀ᶠ x in f₁, p x :=
  h hp
/-
**Filter.eventually_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_of_mem {f : Filter α} {P : α -> Prop} {U : Set α} (hU : U in f)
 (h : forall x in U, P x) : forallᶠ x in f, P x
参数：hU : U in f；h : forall x in U, P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem eventually_of_mem {f : Filter α} {P : α → Prop} {U : Set α} (hU : U ∈ f)
    (h : ∀ x ∈ U, P x) : ∀ᶠ x in f, P x :=
  mem_of_superset hU h
/-
**Filter.Eventually.and** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   Filter.Eventually p f → 
Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
protected theorem Eventually.and {p q : α → Prop} {f : Filter α} :
    f.Eventually p → f.Eventually q → ∀ᶠ x in f, p x ∧ q x :=
  inter_mem
/-
**Filter.eventually_true** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} (f : Filter α), ∀ᶠ (x : α) in f, True
参数：f : Filter α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
@[simp] theorem eventually_true (f : Filter α) : ∀ᶠ _ in f, True := univ_mem
/-
**Filter.Eventually.of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {f : Filter α}, (∀ (x : α), p x) → ∀ᶠ (x : α
) in f, p x
参数：∀ (x : α), p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem Eventually.of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp

@[simp]
/-
**Filter.eventually_false_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_false_iff_eq_bot {f : Filter α} : (forallᶠ _ in f, False) ↔ f =
 ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
-/
theorem eventually_false_iff_eq_bot {f : Filter α} : (∀ᶠ _ in f, False) ↔ f = ⊥ :=
  empty_mem_iff_bot

@[simp]
/-
**Filter.eventually_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (forallᶠ _ in f
, p) ↔ p
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
-/
theorem eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (∀ᶠ _ in f, p) ↔ p := by
  by_cases h : p <;> simp [h, t.ne]
/-
**Filter.eventually_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_iff_exists_mem {p : α -> Prop} {f : Filter α} : (forallᶠ x in f
, p x) ↔ exists v in f, forall y in v, p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
-/
theorem eventually_iff_exists_mem {p : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x) ↔ ∃ v ∈ f, ∀ y ∈ v, p y :=
  exists_mem_subset_iff.symm
/-
**Filter.Eventually.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {f : Filter α}, (∀ᶠ (x : α) in f, p x) → ∃ v
 ∈ f, ∀ y ∈ v, p y
参数：∀ᶠ (x : α) in f, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
-/
theorem Eventually.exists_mem {p : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) :
    ∃ v ∈ f, ∀ y ∈ v, p y :=
  eventually_iff_exists_mem.1 hp
/-
**Filter.Eventually.mp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   (∀ᶠ (x : α) in f, p x) →
 (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
参数：∀ᶠ (x : α) in f, p x；∀ᶠ (x : α) in f, p x → q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
-/
theorem Eventually.mp {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, p x → q x) : ∀ᶠ x in f, q x :=
  mp_mem hp hq

@[gcongr]
/-
**Filter.Eventually.mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, (∀ᶠ (x : α) in f, p x) → (
∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
参数：∀ᶠ (x : α) in f, p x；∀ (x : α), p x → q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Eventually.mono {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ x, p x → q x) : ∀ᶠ x in f, q x :=
  hp.mp (Eventually.of_forall hq)
/-
**Filter.forall_eventually_of_eventually_forall** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
形式化陈述：forall_eventually_of_eventually_forall {f : Filter α} {p : α -> β -> Prop}
 (h : forallᶠ x in f, forall y, p x y) : forall y, forallᶠ x in f, p x y
参数：h : forallᶠ x in f, forall y, p x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem forall_eventually_of_eventually_forall {f : Filter α} {p : α → β → Prop}
    (h : ∀ᶠ x in f, ∀ y, p x y) : ∀ y, ∀ᶠ x in f, p x y :=
  fun y => h.mono fun _ h => h y

@[simp]
/-
**Filter.eventually_and** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_and {p q : α -> Prop} {f : Filter α} : (forallᶠ x in f, p x ∧ q
 x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in f, q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem_iff`：inter_mem_iff {s t : Set α} : s inter t in f ↔ s i
n f ∧ t in f
-/
theorem eventually_and {p q : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in f, q x :=
  inter_mem_iff
/-
**Filter.Eventually.congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {f : Filter α} {p q : α → Prop},   (∀ᶠ (x : α) in f, p x) →
 (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
参数：∀ᶠ (x : α) in f, p x；∀ᶠ (x : α) in f, p x ↔ q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Eventually.congr {f : Filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x)
    (h : ∀ᶠ x in f, p x ↔ q x) : ∀ᶠ x in f, q x :=
  h'.mp (h.mono fun _ hx => hx.mp)
/-
**Filter.eventually_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_congr {f : Filter α} {p q : α -> Prop} (h : forallᶠ x in f, p x
 ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
参数：h : forallᶠ x in f, p x ↔ q x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.congr`：∀ {α : Type u} {f : Filter α} {p q : α → Prop},
   (∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem eventually_congr {f : Filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∀ᶠ x in f, p x) ↔ ∀ᶠ x in f, q x :=
  ⟨fun hp => hp.congr h, fun hq => hq.congr <| by simpa only [Iff.comm] using h⟩

@[simp]
/-
**Filter.eventually_or_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α -> Prop} : (fo
rallᶠ x in f, p ∨ q x) ↔ p ∨ forallᶠ x in f, q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p ∨ q x) ↔ p ∨ ∀ᶠ x in f, q x :=
  by_cases (fun h : p => by simp [h]) fun h => by simp [h]

@[simp]
/-
**Filter.eventually_or_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_or_distrib_right {f : Filter α} {p : α -> Prop} {q : Prop} : (f
orallᶠ x in f, p x ∨ q) ↔ (forallᶠ x in f, p x) ∨ q
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_or_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x ∨ q) ↔ (∀ᶠ x in f, p x) ∨ q := by
  simp only [@or_comm _ q, eventually_or_distrib_left]
/-
**Filter.eventually_imp_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α -> Prop} : (f
orallᶠ x in f, p -> q x) ↔ p -> forallᶠ x in f, q x
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p → q x) ↔ p → ∀ᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]
/-
**Filter.eventually_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, p x
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x :=
  ⟨⟩

@[simp]
/-
**Filter.eventually_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_top {p : α -> Prop} : (forallᶠ x in ⊤, p x) ↔ forall x, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ ∀ x, p x :=
  Iff.rfl

@[simp]
/-
**Filter.eventually_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_sup {p : α -> Prop} {f g : Filter α} : (forallᶠ x in f ⊔ g, p x
) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_sup {p : α → Prop} {f g : Filter α} :
    (∀ᶠ x in f ⊔ g, p x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in g, p x :=
  Iff.rfl

@[simp]
/-
**Filter.eventually_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_sSup {p : α -> Prop} {fs : Set (Filter α)} : (forallᶠ x in sSup
 fs, p x) ↔ forall f in fs, forallᶠ x in f, p x
参数：Filter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_sSup {p : α → Prop} {fs : Set (Filter α)} :
    (∀ᶠ x in sSup fs, p x) ↔ ∀ f ∈ fs, ∀ᶠ x in f, p x :=
  Iff.rfl

@[simp]
/-
**Filter.eventually_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_iSup {p : α -> Prop} {fs : ι -> Filter α} : (forallᶠ x in ⨆ b, 
fs b, p x) ↔ forall b, forallᶠ x in fs b, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_iSup`：mem_iSup {x : Set α} {f : ι -> Filter α} : x in iSup f 
↔ forall i, x in f i
-/
theorem eventually_iSup {p : α → Prop} {fs : ι → Filter α} :
    (∀ᶠ x in ⨆ b, fs b, p x) ↔ ∀ b, ∀ᶠ x in fs b, p x :=
  mem_iSup

@[simp]
/-
**Filter.eventually_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_principal {a : Set α} {p : α -> Prop} : (forallᶠ x in 𝓟 a, p x)
 ↔ forall x in a, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_principal {a : Set α} {p : α → Prop} : (∀ᶠ x in 𝓟 a, p x) ↔ ∀ x ∈ a, p x :=
  Iff.rfl
/-
**Filter.Eventually.forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_2} {f : Filter α} {s : Set α} {P : α → Prop},   (∀ᶠ (x : α) 
in f, P x) → Filter.principal s ≤ f → ∀ x ∈ s, P x
参数：∀ᶠ (x : α) in f, P x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_principal`：eventually_principal {a : Set α} {p : α -> 
Prop} : (forallᶠ x in 𝓟 a, p x) ↔ forall x in a, p x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
-/
theorem Eventually.forall_mem {α : Type*} {f : Filter α} {s : Set α} {P : α → Prop}
    (hP : ∀ᶠ x in f, P x) (hf : 𝓟 s ≤ f) : ∀ x ∈ s, P x :=
  Filter.eventually_principal.mp (hP.filter_mono hf)
/-
**Filter.eventually_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_inf {f g : Filter α} {p : α -> Prop} : (forallᶠ x in f ⊓ g, p x
) ↔ exists s in f, exists t in g, forall x in s inter t, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_inf_iff_superset`：mem_inf_iff_superset {f g : Filter α} {s : 
Set α} : s in f ⊓ g ↔ exists t₁ in f, exists t₂ in g, t₁ inter t₂ subseteq s
-/
theorem eventually_inf {f g : Filter α} {p : α → Prop} :
    (∀ᶠ x in f ⊓ g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x ∈ s ∩ t, p x :=
  mem_inf_iff_superset
/-
**Filter.eventually_inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_inf_principal {f : Filter α} {p : α -> Prop} {s : Set α} : (for
allᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x in s -> p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
-/
theorem eventually_inf_principal {f : Filter α} {p : α → Prop} {s : Set α} :
    (∀ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∀ᶠ x in f, x ∈ s → p x :=
  mem_inf_principal
/-
**Filter.eventually_iff_all_subsets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_iff_all_subsets {f : Filter α} {p : α -> Prop} : (forallᶠ x in 
f, p x) ↔ forall (s : Set α), forallᶠ x in f, x in s -> p x where mp h _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem eventually_iff_all_subsets {f : Filter α} {p : α → Prop} :
    (∀ᶠ x in f, p x) ↔ ∀ (s : Set α), ∀ᶠ x in f, x ∈ s → p x where
  mp h _ := by filter_upwards [h] with _ pa _ using pa
  mpr h := by filter_upwards [h univ] with _ pa using pa (by simp)

/-! ### Frequently -/

/-
**Filter.Eventually.frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {f : Filter α} [f.NeBot] {p : α → Prop}, (∀ᶠ (x : α) in f, 
p x) → ∃ᶠ (x : α) in f, p x
参数：∀ᶠ (x : α) in f, p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.compl_notMem`：compl_notMem {f : Filter α} {s : Set α} [NeBot f] (
h : s in f) : sᶜ ∉ f

--- 原说明 ---
### Frequently
-/
theorem Eventually.frequently {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ᶠ x in f, p x) :
    ∃ᶠ x in f, p x :=
  compl_notMem h
/-
**Filter.Frequently.of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u} {f : Filter α} [f.NeBot] {p : α → Prop}, (∀ (x : α), p x) →
 ∃ᶠ (x : α) in f, p x
参数：∀ (x : α), p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Frequently.of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) :
    ∃ᶠ x in f, p x :=
  Eventually.frequently (Eventually.of_forall h)
/-
**Filter.Frequently.mp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   (∃ᶠ (x : α) in f, p x) →
 (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
参数：∃ᶠ (x : α) in f, p x；∀ᶠ (x : α) in f, p x → q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem Frequently.mp {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ᶠ x in f, p x → q x) : ∃ᶠ x in f, q x :=
  mt (fun hq => hq.mp <| hpq.mono fun _ => mt) h
/-
**Filter.frequently_congr** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：frequently_congr {p q : α -> Prop} {f : Filter α} (h : forallᶠ x in f, p x
 ↔ q x) : (existsᶠ x in f, p x) ↔ existsᶠ x in f, q x
参数：h : forallᶠ x in f, p x ↔ q x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma frequently_congr {p q : α → Prop} {f : Filter α} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∃ᶠ x in f, p x) ↔ ∃ᶠ x in f, q x :=
  ⟨fun h' ↦ h'.mp (h.mono fun _ ↦ Iff.mp), fun h' ↦ h'.mp (h.mono fun _ ↦ Iff.mpr)⟩
/-
**Filter.Frequently.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {f g : Filter α}, (∃ᶠ (x : α) in f, p x) → f
 ≤ g → ∃ᶠ (x : α) in g, p x
参数：∃ᶠ (x : α) in f, p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
-/
theorem Frequently.filter_mono {p : α → Prop} {f g : Filter α} (h : ∃ᶠ x in f, p x) (hle : f ≤ g) :
    ∃ᶠ x in g, p x :=
  mt (fun h' => h'.filter_mono hle) h

@[gcongr]
/-
**Filter.Frequently.mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, (∃ᶠ (x : α) in f, p x) → (
∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
参数：∃ᶠ (x : α) in f, p x；∀ (x : α), p x → q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Frequently.mono {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ x, p x → q x) : ∃ᶠ x in f, q x :=
  h.mp (Eventually.of_forall hpq)
/-
**Filter.Frequently.and_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`
。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   (∃ᶠ (x : α) in f, p x) →
 (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p x ∧ q x
参数：∃ᶠ (x : α) in f, p x；∀ᶠ (x : α) in f, q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem Frequently.and_eventually {p q : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  refine mt (fun h => hq.mp <| h.mono ?_) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩
/-
**Filter.Eventually.and_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`
。
形式化陈述：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   (∀ᶠ (x : α) in f, p x) →
 (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p x ∧ q x
参数：∀ᶠ (x : α) in f, p x；∃ᶠ (x : α) in f, q x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
-/
theorem Eventually.and_frequently {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∃ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  simpa only [and_comm] using hq.and_eventually hp
/-
**Filter.Frequently.exists** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {f : Filter α}, (∃ᶠ (x : α) in f, p x) → ∃ x
, p x
参数：∃ᶠ (x : α) in f, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
-/
theorem Frequently.exists {p : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x := by
  by_contra H
  replace H : ∀ᶠ x in f, ¬p x := Eventually.of_forall (not_exists.1 H)
  exact hp H
/-
**Filter.Eventually.exists** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {f : Filter α} [f.NeBot], (∀ᶠ (x : α) in f, 
p x) → ∃ x, p x
参数：∀ᶠ (x : α) in f, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
-/
theorem Eventually.exists {p : α → Prop} {f : Filter α} [NeBot f] (hp : ∀ᶠ x in f, p x) :
    ∃ x, p x :=
  hp.frequently.exists
/-
**Filter.frequently_iff_neBot** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：frequently_iff_neBot {l : Filter α} {p : α -> Prop} : (existsᶠ x in l, p x
) ↔ NeBot (l ⊓ 𝓟 {x | p x})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Filter.inf_principal_eq_bot`：inf_principal_eq_bot {f : Filter α} {s : Se
t α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma frequently_iff_neBot {l : Filter α} {p : α → Prop} :
    (∃ᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x}) := by
  rw [neBot_iff, Ne, inf_principal_eq_bot]; rfl
/-
**Filter.frequently_mem_iff_neBot** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：frequently_mem_iff_neBot {l : Filter α} {s : Set α} : (existsᶠ x in l, x i
n s) ↔ NeBot (l ⊓ 𝓟 s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})
-/
lemma frequently_mem_iff_neBot {l : Filter α} {s : Set α} : (∃ᶠ x in l, x ∈ s) ↔ NeBot (l ⊓ 𝓟 s) :=
  frequently_iff_neBot
/-
**Filter.frequently_iff_forall_eventually_exists_and** 是 Mathlib 中的一个定理，位于命名空间 `
Filter`。
形式化陈述：frequently_iff_forall_eventually_exists_and {p : α -> Prop} {f : Filter α}
 : (existsᶠ x in f, p x) ↔ forall {q : α -> Prop}, (forallᶠ x in f, q x) -> exis
ts x, p x ∧ q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : Filter α} :
    (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
  ⟨fun hp _ hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩
/-
**Filter.frequently_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_iff {f : Filter α} {P : α -> Prop} : (existsᶠ x in f, P x) ↔ fo
rall {U}, U in f -> exists x in U, P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Set.ofPred_bijective`：ofPred_bijective : Bijective (ofPred : (α -> Prop)
 -> Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_iff {f : Filter α} {P : α → Prop} :
    (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x := by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _),
    Set.ofPred_bijective.surjective.forall, Filter.Eventually, mem_ofPred]

@[simp, push]
/-
**Filter.not_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_eventually {p : α -> Prop} {f : Filter α} : (¬forallᶠ x in f, p x) ↔ e
xistsᶠ x in f, ¬p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_eventually {p : α → Prop} {f : Filter α} : (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x := by
  simp [Filter.Frequently]

@[simp, push]
/-
**Filter.not_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_frequently {p : α -> Prop} {f : Filter α} : (¬existsᶠ x in f, p x) ↔ f
orallᶠ x in f, ¬p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_frequently {p : α → Prop} {f : Filter α} : (¬∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, ¬p x := by
  simp only [Filter.Frequently, not_not]

@[simp]
/-
**Filter.frequently_true_iff_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_true_iff_neBot (f : Filter α) : (existsᶠ _ in f, True) ↔ NeBot 
f
参数：f : Filter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_true_iff_neBot (f : Filter α) : (∃ᶠ _ in f, True) ↔ NeBot f := by
  simp [frequently_iff_neBot]

@[simp]
/-
**Filter.frequently_false** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_false (f : Filter α) : ¬existsᶠ _ in f, False
参数：f : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem frequently_false (f : Filter α) : ¬∃ᶠ _ in f, False := by simp

@[simp]
/-
**Filter.frequently_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_const {f : Filter α} [NeBot f] {p : Prop} : (existsᶠ _ in f, p)
 ↔ p
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem frequently_const {f : Filter α} [NeBot f] {p : Prop} : (∃ᶠ _ in f, p) ↔ p := by
  by_cases p <;> simp [*]

@[simp]
/-
**Filter.frequently_or_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_or_distrib {f : Filter α} {p q : α -> Prop} : (existsᶠ x in f, 
p x ∨ q x) ↔ (existsᶠ x in f, p x) ∨ existsᶠ x in f, q x
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_or_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]
/-
**Filter.frequently_or_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α -> P
rop} : (existsᶠ x in f, p ∨ q x) ↔ p ∨ existsᶠ x in f, q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∨ q x) ↔ p ∨ ∃ᶠ x in f, q x := by simp
/-
**Filter.frequently_or_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α -> Prop} {q : 
Prop} : (existsᶠ x in f, p x ∨ q) ↔ (existsᶠ x in f, p x) ∨ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q := by simp
/-
**Filter.frequently_imp_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_imp_distrib {f : Filter α} {p q : α -> Prop} : (existsᶠ x in f,
 p x -> q x) ↔ (forallᶠ x in f, p x) -> existsᶠ x in f, q x
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_imp_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∃ᶠ x in f, q x := by
  simp [imp_iff_not_or]
/-
**Filter.frequently_imp_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α -> 
Prop} : (existsᶠ x in f, p -> q x) ↔ p -> existsᶠ x in f, q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p → q x) ↔ p → ∃ᶠ x in f, q x := by simp [frequently_imp_distrib]
/-
**Filter.frequently_imp_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α -> Prop} {q :
 Prop} : (existsᶠ x in f, p x -> q) ↔ (forallᶠ x in f, p x) -> q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x → q) ↔ (∀ᶠ x in f, p x) → q := by
  simp only [frequently_imp_distrib, frequently_const]
/-
**Filter.eventually_imp_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_imp_distrib_right {f : Filter α} {p : α -> Prop} {q : Prop} : (
forallᶠ x in f, p x -> q) ↔ (existsᶠ x in f, p x) -> q
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_imp_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x → q) ↔ (∃ᶠ x in f, p x) → q := by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp]
/-
**Filter.frequently_and_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α -> Prop} : (e
xistsᶠ x in f, p ∧ q x) ↔ p ∧ existsᶠ x in f, q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∧ q x) ↔ p ∧ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, Classical.not_imp]

@[simp]
/-
**Filter.frequently_and_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_and_distrib_right {f : Filter α} {p : α -> Prop} {q : Prop} : (
existsᶠ x in f, p x ∧ q) ↔ (existsᶠ x in f, p x) ∧ q
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_and_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∧ q) ↔ (∃ᶠ x in f, p x) ∧ q := by
  simp only [@and_comm _ q, frequently_and_distrib_left]

@[simp]
/-
**Filter.frequently_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_bot {p : α -> Prop} : ¬existsᶠ x in ⊥, p x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem frequently_bot {p : α → Prop} : ¬∃ᶠ x in ⊥, p x := by simp

@[simp]
/-
**Filter.frequently_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_top {p : α -> Prop} : (existsᶠ x in ⊤, p x) ↔ exists x, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ ∃ x, p x := by simp [Filter.Frequently]

@[simp]
/-
**Filter.frequently_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_principal {a : Set α} {p : α -> Prop} : (existsᶠ x in 𝓟 a, p x)
 ↔ exists x in a, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_principal {a : Set α} {p : α → Prop} : (∃ᶠ x in 𝓟 a, p x) ↔ ∃ x ∈ a, p x := by
  simp [Filter.Frequently, not_forall]
/-
**Filter.frequently_inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_inf_principal {f : Filter α} {s : Set α} {p : α -> Prop} : (exi
stsᶠ x in f ⊓ 𝓟 s, p x) ↔ existsᶠ x in f, x in s ∧ p x
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_inf_principal {f : Filter α} {s : Set α} {p : α → Prop} :
    (∃ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∃ᶠ x in f, x ∈ s ∧ p x := by
  simp only [Filter.Frequently, eventually_inf_principal, not_and]

alias ⟨Frequently.of_inf_principal, Frequently.inf_principal⟩ := frequently_inf_principal
/-
**Filter.frequently_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_sup {p : α -> Prop} {f g : Filter α} : (existsᶠ x in f ⊔ g, p x
) ↔ (existsᶠ x in f, p x) ∨ existsᶠ x in g, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_sup {p : α → Prop} {f g : Filter α} :
    (∃ᶠ x in f ⊔ g, p x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in g, p x := by
  simp only [Filter.Frequently, eventually_sup, not_and_or]

@[simp]
/-
**Filter.frequently_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_sSup {p : α -> Prop} {fs : Set (Filter α)} : (existsᶠ x in sSup
 fs, p x) ↔ exists f in fs, existsᶠ x in f, p x
参数：Filter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_sSup {p : α → Prop} {fs : Set (Filter α)} :
    (∃ᶠ x in sSup fs, p x) ↔ ∃ f ∈ fs, ∃ᶠ x in f, p x := by
  simp only [Filter.Frequently, not_forall, eventually_sSup, exists_prop]

@[simp]
/-
**Filter.frequently_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_iSup {p : α -> Prop} {fs : β -> Filter α} : (existsᶠ x in ⨆ b, 
fs b, p x) ↔ exists b, existsᶠ x in fs b, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_iSup {p : α → Prop} {fs : β → Filter α} :
    (∃ᶠ x in ⨆ b, fs b, p x) ↔ ∃ b, ∃ᶠ x in fs b, p x := by
  simp only [Filter.Frequently, eventually_iSup, not_forall]
/-
**Filter.Eventually.choice** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {β : Type v} {r : α → β → Prop} {l : Filter α} [l.NeBot],  
 (∀ᶠ (x : α) in l, ∃ y, r x y) → ∃ f, ∀ᶠ (x : α) in l, r x (f x)
参数：∀ᶠ (x : α) in l, ∃ y, r x y；x : α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Eventually.choice {r : α → β → Prop} {l : Filter α} [l.NeBot] (h : ∀ᶠ x in l, ∃ y, r x y) :
    ∃ f : α → β, ∀ᶠ x in l, r x (f x) := by
  have : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : ∃ y, r x y) => hx
  exact ⟨f, h.mono hf⟩
/-
**Filter.skolem** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：skolem {ι : Type*} {α : ι -> Type*} [forall i, Nonempty (α i)] {P : forall
 i : ι, α i -> Prop} {F : Filter ι} : (forallᶠ i in F, exists b, P i b) ↔ exists
 b : (Π i, α i), forallᶠ i in F, P i (b i)
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma skolem {ι : Type*} {α : ι → Type*} [∀ i, Nonempty (α i)]
    {P : ∀ i : ι, α i → Prop} {F : Filter ι} :
    (∀ᶠ i in F, ∃ b, P i b) ↔ ∃ b : (Π i, α i), ∀ᶠ i in F, P i (b i) := by
  classical
  refine ⟨fun H ↦ ?_, fun ⟨b, hb⟩ ↦ hb.mp (.of_forall fun x a ↦ ⟨_, a⟩)⟩
  refine ⟨fun i ↦ if h : ∃ b, P i b then h.choose else Nonempty.some inferInstance, ?_⟩
  filter_upwards [H] with i hi
  exact dif_pos hi ▸ hi.choose_spec

/-!
### Relation “eventually equal”
-/

section EventuallyEq
variable {l : Filter α} {f g : α → β}

/-
**Filter.EventuallyEq.eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`
。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g : α → β}, f =ᶠ[l] g → ∀ᶠ (
x : α) in l, f x = g x
参数：x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EventuallyEq.eventually (h : f =ᶠ[l] g) : ∀ᶠ x in l, f x = g x := h
/-
**Filter.eventuallyEq_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} {f g : α → β}, f =ᶠ[⊤] g ↔ f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma eventuallyEq_top : f =ᶠ[⊤] g ↔ f = g := by simp [EventuallyEq, funext_iff]
/-
**Filter.EventuallyEq.rw** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g : α → β},   f =ᶠ[l] g → ∀ 
(p : α → β → Prop), (∀ᶠ (x : α) in l, p x (f x)) → ∀ᶠ (x : α) in l, p x (g x)
参数：p : α → β → Prop；∀ᶠ (x : α) in l, p x (f x)；x : α；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.congr`：∀ {α : Type u} {f : Filter α} {p q : α → Prop},
   (∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem EventuallyEq.rw {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (p : α → β → Prop)
    (hf : ∀ᶠ x in l, p x (f x)) : ∀ᶠ x in l, p x (g x) :=
  hf.congr <| h.mono fun _ hx => hx ▸ Iff.rfl
/-
**Filter.eventuallyEq_set** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ forallᶠ x in l
, x in s ↔ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
-/
theorem eventuallyEq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
  eventually_congr <| Eventually.of_forall fun _ ↦ eq_iff_iff

alias ⟨EventuallyEq.mem_iff, Eventually.set_eq⟩ := eventuallyEq_set

@[simp]
/-
**Filter.eventuallyEq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventuallyEq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s ∈ l := by
  simp [eventuallyEq_set]
/-
**Filter.EventuallyEq.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`
。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g : α → β}, f =ᶠ[l] g → ∃ s 
∈ l, Set.EqOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
-/
theorem EventuallyEq.exists_mem {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    ∃ s ∈ l, EqOn f g s :=
  Eventually.exists_mem h
/-
**Filter.eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_of_mem {l : Filter α} {f g : α -> β} {s : Set α} (hs : s in l
) (h : EqOn f g s) : f =ᶠ[l] g
参数：hs : s in l；h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
-/
theorem eventuallyEq_of_mem {l : Filter α} {f g : α → β} {s : Set α} (hs : s ∈ l) (h : EqOn f g s) :
    f =ᶠ[l] g :=
  eventually_of_mem hs h
/-
**Filter.eventuallyEq_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_iff_exists_mem {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ ex
ists s in l, EqOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
-/
theorem eventuallyEq_iff_exists_mem {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ ∃ s ∈ l, EqOn f g s :=
  eventually_iff_exists_mem
/-
**Filter.EventuallyEq.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq
`。
形式化陈述：∀ {α : Type u} {β : Type v} {l l' : Filter α} {f g : α → β}, f =ᶠ[l] g → l
' ≤ l → f =ᶠ[l'] g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EventuallyEq.filter_mono {l l' : Filter α} {f g : α → β} (h₁ : f =ᶠ[l] g) (h₂ : l' ≤ l) :
    f =ᶠ[l'] g :=
  h₂ h₁

@[refl, simp]
/-
**Filter.EventuallyEq.refl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} (l : Filter α) (f : α → β), f =ᶠ[l] f
参数：l : Filter α；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem EventuallyEq.refl (l : Filter α) (f : α → β) : f =ᶠ[l] f :=
  Eventually.of_forall fun _ => rfl
/-
**Filter.EventuallyEq.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f : α → β}, f =ᶠ[l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
protected theorem EventuallyEq.rfl {l : Filter α} {f : α → β} : f =ᶠ[l] f :=
  EventuallyEq.refl l f
/-
**Filter.EventuallyEq.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g : α → β}, f = g → f =ᶠ[l] 
g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem EventuallyEq.of_eq {l : Filter α} {f g : α → β} (h : f = g) : f =ᶠ[l] g := h ▸ .rfl
alias _root_.Eq.eventuallyEq := EventuallyEq.of_eq

@[symm]
/-
**Filter.EventuallyEq.symm** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {f g : α → β} {l : Filter α}, f =ᶠ[l] g → g =ᶠ
[l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem EventuallyEq.symm {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
  H.mono fun _ => Eq.symm
/-
**Filter.eventuallyEq_comm** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_comm {f g : α -> β} {l : Filter α} : f =ᶠ[l] g ↔ g =ᶠ[l] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma eventuallyEq_comm {f g : α → β} {l : Filter α} : f =ᶠ[l] g ↔ g =ᶠ[l] f := ⟨.symm, .symm⟩

@[trans]
/-
**Filter.EventuallyEq.trans** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g h : α → β}, f =ᶠ[l] g → g 
=ᶠ[l] h → f =ᶠ[l] h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.rw`：∀ {α : Type u} {β : Type v} {l : Filter α} {f g 
: α → β},   f =ᶠ[l] g → ∀ (p : α → β → Prop), (∀ᶠ (x : α) in l, p x (f x)) → ∀ᶠ 
(x : α) in l…
-/
theorem EventuallyEq.trans {l : Filter α} {f g h : α → β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
    f =ᶠ[l] h :=
  H₂.rw (fun x y => f x = y) H₁
/-
**Filter.EventuallyEq.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`
。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g h : α → β}, f =ᶠ[l] g → (f
 =ᶠ[l] h ↔ g =ᶠ[l] h)
参数：f =ᶠ[l] h ↔ g =ᶠ[l] h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.congr_left {l : Filter α} {f g h : α → β} (H : f =ᶠ[l] g) :
    f =ᶠ[l] h ↔ g =ᶠ[l] h :=
  ⟨H.symm.trans, H.trans⟩
/-
**Filter.EventuallyEq.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq
`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g h : α → β}, g =ᶠ[l] h → (f
 =ᶠ[l] g ↔ f =ᶠ[l] h)
参数：f =ᶠ[l] g ↔ f =ᶠ[l] h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.congr_right {l : Filter α} {f g h : α → β} (H : g =ᶠ[l] h) :
    f =ᶠ[l] g ↔ f =ᶠ[l] h :=
  ⟨(·.trans H), (·.trans H.symm)⟩
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {l : Filter α} :
    Trans ((· =ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· =ᶠ[l] ·) (· =ᶠ[l] ·) where
  trans := EventuallyEq.trans
/-
**Filter.EventuallyEq.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} {l : Filter α} {f f' : α → β},   
f =ᶠ[l] f' → ∀ {g g' : α → γ}, g =ᶠ[l] g' → (fun x => (f x, g x)) =ᶠ[l] fun x =>
 (f' x, g' x)
参数：fun x => (f x, g x)；f' x, g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EventuallyEq.prodMk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
    (fun x => (f x, g x)) =ᶠ[l] fun x => (f' x, g' x) :=
  hf.mp <|
    hg.mono <| by
      intros
      simp only [*]

/-- See `EventuallyEq.comp_tendsto` in Mathlib.Order.Filter.Tendsto for a similar statement w.r.t.
composition on the right. -/
@[gcongr]
/-
**Filter.EventuallyEq.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} {f g : α → β} {l : Filter α}, f =
ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
参数：h : β → γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
See `EventuallyEq.comp_tendsto` in Mathlib.Order.Filter.Tendsto for a similar st
atement w.r.t.
composition on the right.
-/
theorem EventuallyEq.fun_comp {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) (h : β → γ) :
    h ∘ f =ᶠ[l] h ∘ g :=
  H.mono fun _ hx => congr_arg h hx
/-
**Filter.EventuallyEq.comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EventuallyEq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ)
    (Hg : g =ᶠ[l] g') : (fun x => h (f x) (g x)) =ᶠ[l] fun x => h (f' x) (g' x) :=
  (Hf.prodMk Hg).fun_comp (uncurry h)

@[to_additive (attr := gcongr, to_fun)]
/-
**Filter.EventuallyEq.mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f' g g' : α → β} {l : Filter
 α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.mul [Mul β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : f * f' =ᶠ[l] g * g' :=
  h.comp₂ (· * ·) h'

@[to_additive]
/-
**Filter.EventuallyEq.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} [inst : Mul β] {f₁ f₂ f₃ : α → 
β}, f₁ =ᶠ[l] f₂ → f₃ * f₁ =ᶠ[l] f₃ * f₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma EventuallyEq.mul_left [Mul β] {f₁ f₂ f₃ : α → β} (h : f₁ =ᶠ[l] f₂) :
    f₃ * f₁ =ᶠ[l] f₃ * f₂ := EventuallyEq.mul (by rfl) h

@[to_additive]
/-
**Filter.EventuallyEq.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} [inst : Mul β] {f₁ f₂ f₃ : α → 
β}, f₁ =ᶠ[l] f₂ → f₁ * f₃ =ᶠ[l] f₂ * f₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma EventuallyEq.mul_right [Mul β] {f₁ f₂ f₃ : α → β} (h : f₁ =ᶠ[l] f₂) :
    f₁ * f₃ =ᶠ[l] f₂ * f₃ := EventuallyEq.mul h (by rfl)

@[to_additive (attr := gcongr, to_fun, to_additive) const_smul]
/-
**Filter.EventuallyEq.pow_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type u_2} [inst : Pow β γ] {f g : α → β} 
{l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), f ^ c =ᶠ[l] g ^ c
参数：c : γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem EventuallyEq.pow_const {γ} [Pow β γ] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) (c : γ) :
    f ^ c =ᶠ[l] g ^ c :=
  h.fun_comp (· ^ c)

@[to_additive (attr := gcongr, to_fun)]
/-
**Filter.EventuallyEq.inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Inv β] {f g : α → β} {l : Filter α}, f
 =ᶠ[l] g → f⁻¹ =ᶠ[l] g⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem EventuallyEq.inv [Inv β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) : f⁻¹ =ᶠ[l] g⁻¹ :=
  h.fun_comp Inv.inv

@[to_additive (attr := gcongr, to_fun)]
/-
**Filter.EventuallyEq.div** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Div β] {f f' g g' : α → β} {l : Filter
 α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f / f' =ᶠ[l] g / g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.div [Div β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : f / f' =ᶠ[l] g / g' :=
  h.comp₂ (· / ·) h'

@[to_additive]
/-
**Filter.EventuallyEq.smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {𝕜 : Type u_2} [inst : SMul 𝕜 β] {l : Filter α
} {f f' : α → 𝕜} {g g' : α → β},   f =ᶠ[l] f' → g =ᶠ[l] g' → (fun x => f x • g x
) =ᶠ[l] fun x => f' x • g' x
参数：fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β}
    (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : (fun x => f x • g x) =ᶠ[l] fun x => f' x • g' x :=
  hf.comp₂ (· • ·) hg

@[gcongr, to_fun]
/-
**Filter.EventuallyEq.star** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {R : Type u_2} [inst : Star R] {f g : α → R} {l : Filter α}
, f =ᶠ[l] g → star f =ᶠ[l] star g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
protected theorem EventuallyEq.star {R : Type*} [Star R]
    {f g : α → R} {l : Filter α} (h : f =ᶠ[l] g) : star f =ᶠ[l] star g := h.fun_comp Star.star

@[gcongr]
/-
**Filter.EventuallyEq.sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Max β] {l : Filter α} {f f' g g' : α →
 β},   f =ᶠ[l] f' → g =ᶠ[l] g' → f ⊔ g =ᶠ[l] f' ⊔ g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.sup [Max β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : f ⊔ g =ᶠ[l] f' ⊔ g' :=
  hf.comp₂ (· ⊔ ·) hg

@[gcongr]
/-
**Filter.EventuallyEq.inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Min β] {l : Filter α} {f f' g g' : α →
 β},   f =ᶠ[l] f' → g =ᶠ[l] g' → f ⊓ g =ᶠ[l] f' ⊓ g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.inf [Min β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : f ⊓ g =ᶠ[l] f' ⊓ g' :=
  hf.comp₂ (· ⊓ ·) hg

@[gcongr]
/-
**Filter.EventuallyEq.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : Filter α} {f g : α → β}, f =ᶠ[l] g → ∀ (s
 : Set β), f ⁻¹' s =ᶠ[l] g ⁻¹' s
参数：s : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem EventuallyEq.preimage {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (s : Set β) :
    f ⁻¹' s =ᶠ[l] g ⁻¹' s :=
  h.fun_comp s

@[gcongr]
/-
**Filter.EventuallyEq.inter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s =ᶠ[l] t → s' =ᶠ[l] t'
 → s ∩ s' =ᶠ[l] t ∩ t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.inter {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∩ s' : Set α) =ᶠ[l] (t ∩ t' : Set α) :=
  h.comp₂ (· ∧ ·) h'

@[gcongr]
/-
**Filter.EventuallyEq.union** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s =ᶠ[l] t → s' =ᶠ[l] t'
 → s ∪ s' =ᶠ[l] t ∪ t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem EventuallyEq.union {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∪ s' : Set α) =ᶠ[l] (t ∪ t' : Set α) :=
  h.comp₂ (· ∨ ·) h'

@[gcongr]
/-
**Filter.EventuallyEq.compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {s t : Set α} {l : Filter α}, s =ᶠ[l] t → sᶜ =ᶠ[l] tᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem EventuallyEq.compl {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t) :
    (sᶜ : Set α) =ᶠ[l] (tᶜ : Set α) :=
  h.fun_comp Not

@[gcongr]
/-
**Filter.EventuallyEq.diff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s =ᶠ[l] t → s' =ᶠ[l] t'
 → s \ s' =ᶠ[l] t \ t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `Filter.EventuallyEq.compl`：∀ {α : Type u} {s t : Set α} {l : Filter α}, 
s =ᶠ[l] t → sᶜ =ᶠ[l] tᶜ
-/
theorem EventuallyEq.diff {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s \ s' : Set α) =ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

@[gcongr]
/-
**Filter.EventuallyEq.symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s =ᶠ[l] t → s' =ᶠ[l] t'
 → symmDiff s s' =ᶠ[l] symmDiff t t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.union`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∪ s' =ᶠ[l] t ∪ t'
· 使用定理 `Filter.EventuallyEq.diff`：∀ {α : Type u} {s t s' t' : Set α} {l : Filter
 α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s \ s' =ᶠ[l] t \ t'
-/
protected theorem EventuallyEq.symmDiff {s t s' t' : Set α} {l : Filter α}
    (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') : (s ∆ s' : Set α) =ᶠ[l] (t ∆ t' : Set α) :=
  (h.diff h').union (h'.diff h)
/-
**Filter.eventuallyEq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ fora
llᶠ x in l, x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventuallyEq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ ∀ᶠ x in l, x ∉ s :=
  eventuallyEq_set.trans <| by simp
/-
**Filter.inter_eventuallyEq_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inter_eventuallyEq_left {s t : Set α} {l : Filter α} : (s inter t : Set α)
 =ᶠ[l] s ↔ forallᶠ x in l, x in s -> x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inter_eventuallyEq_left {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] s ↔ ∀ᶠ x in l, x ∈ s → x ∈ t := by
  simp only [eventuallyEq_set, mem_inter_iff, and_iff_left_iff_imp]
/-
**Filter.inter_eventuallyEq_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inter_eventuallyEq_right {s t : Set α} {l : Filter α} : (s inter t : Set α
) =ᶠ[l] t ↔ forallᶠ x in l, x in t -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Filter.inter_eventuallyEq_left`：inter_eventuallyEq_left {s t : Set α} {l
 : Filter α} : (s inter t : Set α) =ᶠ[l] s ↔ forallᶠ x in l, x in s -> x in t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inter_eventuallyEq_right {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ t → x ∈ s := by
  rw [inter_comm, inter_eventuallyEq_left]

@[simp]
/-
**Filter.eventuallyEq_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_principal {s : Set α} {f g : α -> β} : f =ᶠ[𝓟 s] g ↔ EqOn f g
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyEq_principal {s : Set α} {f g : α → β} : f =ᶠ[𝓟 s] g ↔ EqOn f g s :=
  Iff.rfl
/-
**Filter.eventuallyEq_inf_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α -> β} :
 f =ᶠ[F ⊓ 𝓟 s] g ↔ forallᶠ x in F, x in s -> f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
-/
theorem eventuallyEq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α → β} :
    f =ᶠ[F ⊓ 𝓟 s] g ↔ ∀ᶠ x in F, x ∈ s → f x = g x :=
  eventually_inf_principal
/-
**Filter.EventuallyEq.sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : AddGroup β] {f g : α → β} {l : Filter 
α}, f =ᶠ[l] g → f - g =ᶠ[l] 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem EventuallyEq.sub_eq [AddGroup β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    f - g =ᶠ[l] 0 := by simpa using ((EventuallyEq.refl l f).sub h).symm
/-
**Filter.eventuallyEq_iff_sub** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_iff_sub [AddGroup β] {f g : α -> β} {l : Filter α} : f =ᶠ[l] 
g ↔ f - g =ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.sub_eq`：∀ {α : Type u} {β : Type v} [inst : AddGroup
 β] {f g : α → β} {l : Filter α}, f =ᶠ[l] g → f - g =ᶠ[l] 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem eventuallyEq_iff_sub [AddGroup β] {f g : α → β} {l : Filter α} :
    f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
  ⟨fun h => h.sub_eq, fun h => by simpa using h.add (EventuallyEq.refl l g)⟩
/-
**Filter.eventuallyEq_iff_all_subsets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_iff_all_subsets {f g : α -> β} {l : Filter α} : f =ᶠ[l] g ↔ f
orall s : Set α, forallᶠ x in l, x in s -> f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_iff_all_subsets`：eventually_iff_all_subsets {f : Filte
r α} {p : α -> Prop} : (forallᶠ x in f, p x) ↔ forall (s : Set α), forallᶠ x in 
f, x in s -> p x where …
-/
theorem eventuallyEq_iff_all_subsets {f g : α → β} {l : Filter α} :
    f =ᶠ[l] g ↔ ∀ s : Set α, ∀ᶠ x in l, x ∈ s → f x = g x :=
  eventually_iff_all_subsets

section LE

variable [LE β] {l : Filter α}

@[to_dual self (reorder := f g, f' g', hf hg)]
/-
**Filter.EventuallyLE.congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LE β] {l : Filter α} {f f' g g' : α → 
β},   f ≤ᶠ[l] g → f =ᶠ[l] f' → g =ᶠ[l] g' → f' ≤ᶠ[l] g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem EventuallyLE.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f' ≤ᶠ[l] g' :=
  H.mp <| hg.mp <| hf.mono fun x hf hg H => by rwa [hf, hg] at H

@[to_dual self (reorder := f g, f' g', hf hg)]
/-
**Filter.eventuallyLE_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyLE_congr {f f' g g' : α -> β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g'
) : f <=ᶠ[l] g ↔ f' <=ᶠ[l] g'
参数：hf : f =ᶠ[l] f'；hg : g =ᶠ[l] g'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.congr`：∀ {α : Type u} {β : Type v} [inst : LE β] {l 
: Filter α} {f f' g g' : α → β},   f ≤ᶠ[l] g → f =ᶠ[l] f' → g =ᶠ[l] g' → f' ≤ᶠ[l
] g'
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem eventuallyLE_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
  ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩

@[to_dual self]
/-
**Filter.eventuallyLE_iff_all_subsets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyLE_iff_all_subsets {f g : α -> β} {l : Filter α} : f <=ᶠ[l] g ↔ 
forall s : Set α, forallᶠ x in l, x in s -> f x <= g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_iff_all_subsets`：eventually_iff_all_subsets {f : Filte
r α} {p : α -> Prop} : (forallᶠ x in f, p x) ↔ forall (s : Set α), forallᶠ x in 
f, x in s -> p x where …
-/
theorem eventuallyLE_iff_all_subsets {f g : α → β} {l : Filter α} :
    f ≤ᶠ[l] g ↔ ∀ s : Set α, ∀ᶠ x in l, x ∈ s → f x ≤ g x :=
  eventually_iff_all_subsets

end LE

section Preorder

variable [Preorder β] {l : Filter α} {f g h : α → β}

@[to_dual ge]
/-
**Filter.EventuallyEq.le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] {l : Filter α} {f g : α → 
β}, f =ᶠ[l] g → f ≤ᶠ[l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem EventuallyEq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g :=
  h.mono fun _ => le_of_eq

@[refl]
/-
**Filter.EventuallyLE.refl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] (l : Filter α) (f : α → β)
, f ≤ᶠ[l] f
参数：l : Filter α；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem EventuallyLE.refl (l : Filter α) (f : α → β) : f ≤ᶠ[l] f :=
  EventuallyEq.rfl.le
/-
**Filter.EventuallyLE.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] {l : Filter α} {f : α → β}
, f ≤ᶠ[l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
-/
theorem EventuallyLE.rfl : f ≤ᶠ[l] f :=
  EventuallyLE.refl l f

@[trans, to_dual self (reorder := f h, H₁ H₂)]
/-
**Filter.EventuallyLE.trans** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] {l : Filter α} {f g h : α 
→ β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem EventuallyLE.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₂.mp <| H₁.mono fun _ => le_trans
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans ((· ≤ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· ≤ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyLE.trans
/-
**Filter.EventuallyEq.trans_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] {l : Filter α} {f g h : α 
→ β}, f =ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
-/
theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.le.trans H₂
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans ((· =ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· ≤ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyEq.trans_le
/-
**Filter.EventuallyLE.trans_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] {l : Filter α} {f g h : α 
→ β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
-/
theorem EventuallyLE.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.trans H₂.le
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans ((· ≤ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· =ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyLE.trans_eq

end Preorder

variable {l : Filter α}

@[to_dual self (reorder := h₁ h₂)]
/-
**Filter.EventuallyLE.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder β] {l : Filter α} {f g : 
α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem EventuallyLE.antisymm [PartialOrder β] {l : Filter α} {f g : α → β} (h₁ : f ≤ᶠ[l] g)
    (h₂ : g ≤ᶠ[l] f) : f =ᶠ[l] g :=
  h₂.mp <| h₁.mono fun _ => le_antisymm

@[to_dual none]
/-
**Filter.eventuallyLE_antisymm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyLE_antisymm_iff [PartialOrder β] {l : Filter α} {f g : α -> β} :
 f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventuallyLE_antisymm_iff [PartialOrder β] {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ f ≤ᶠ[l] g ∧ g ≤ᶠ[l] f := by
  simp only [EventuallyEq, EventuallyLE, le_antisymm_iff, eventually_and]

@[to_dual ge_iff_eq']
/-
**Filter.EventuallyLE.ge_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder β] {l : Filter α} {f g : 
α → β}, f ≤ᶠ[l] g → (g ≤ᶠ[l] f ↔ f =ᶠ[l] g)
参数：g ≤ᶠ[l] f ↔ f =ᶠ[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.ge`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → g ≤ᶠ[l] f
-/
theorem EventuallyLE.ge_iff_eq [PartialOrder β] {l : Filter α} {f g : α → β} (h : f ≤ᶠ[l] g) :
    g ≤ᶠ[l] f ↔ f =ᶠ[l] g :=
  ⟨fun h' => h.antisymm h', EventuallyEq.ge⟩

@[to_dual ne_of_gt]
/-
**Filter.Eventually.ne_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] {l : Filter α} {f g : α → 
β},   (∀ᶠ (x : α) in l, f x < g x) → ∀ᶠ (x : α) in l, f x ≠ g x
参数：∀ᶠ (x : α) in l, f x < g x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem Eventually.ne_of_lt [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ᶠ x in l, f x < g x) :
    ∀ᶠ x in l, f x ≠ g x :=
  h.mono fun _ hx => hx.ne

@[to_dual ne_bot_of_gt]
/-
**Filter.Eventually.ne_top_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder β] [inst_1 : OrderTop β] {l :
 Filter α} {f g : α → β},   (∀ᶠ (x : α) in l, f x < g x) → ∀ᶠ (x : α) in l, f x 
≠ ⊤
参数：∀ᶠ (x : α) in l, f x < g x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
-/
theorem Eventually.ne_top_of_lt [Preorder β] [OrderTop β] {l : Filter α} {f g : α → β}
    (h : ∀ᶠ x in l, f x < g x) : ∀ᶠ x in l, f x ≠ ⊤ :=
  h.mono fun _ hx => hx.ne_top

@[to_dual bot_lt_of_ne]
/-
**Filter.Eventually.lt_top_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder β] [inst_1 : OrderTop β] 
{l : Filter α} {f : α → β},   (∀ᶠ (x : α) in l, f x ≠ ⊤) → ∀ᶠ (x : α) in l, f x 
< ⊤
参数：∀ᶠ (x : α) in l, f x ≠ ⊤；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem Eventually.lt_top_of_ne [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β}
    (h : ∀ᶠ x in l, f x ≠ ⊤) : ∀ᶠ x in l, f x < ⊤ :=
  h.mono fun _ hx => hx.lt_top

@[to_dual bot_lt_iff_ne_bot]
/-
**Filter.Eventually.lt_top_iff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
ly`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder β] [inst_1 : OrderTop β] 
{l : Filter α} {f : α → β},   (∀ᶠ (x : α) in l, f x < ⊤) ↔ ∀ᶠ (x : α) in l, f x 
≠ ⊤
参数：∀ᶠ (x : α) in l, f x < ⊤；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.ne_of_lt`：∀ {α : Type u} {β : Type v} [inst : Preorder
 β] {l : Filter α} {f g : α → β},   (∀ᶠ (x : α) in l, f x < g x) → ∀ᶠ (x : α) in
 l, f x ≠ g x
· 使用定理 `Filter.Eventually.lt_top_of_ne`：∀ {α : Type u} {β : Type v} [inst : Part
ialOrder β] [inst_1 : OrderTop β] {l : Filter α} {f : α → β},   (∀ᶠ (x : α) in l
, f x ≠ ⊤) → ∀ᶠ (x :…
-/
theorem Eventually.lt_top_iff_ne_top [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β} :
    (∀ᶠ x in l, f x < ⊤) ↔ ∀ᶠ x in l, f x ≠ ⊤ :=
  ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩

@[gcongr, mono]
/-
**Filter.EventuallyLE.inter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s ≤ᶠ[l] t → s' ≤ᶠ[l] t'
 → s ∩ s' ≤ᶠ[l] t ∩ t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
-/
theorem EventuallyLE.inter {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∩ s' : Set α) ≤ᶠ[l] (t ∩ t' : Set α) :=
  h'.mp <| h.mono fun _ => And.imp

@[gcongr, mono]
/-
**Filter.EventuallyLE.union** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s ≤ᶠ[l] t → s' ≤ᶠ[l] t'
 → s ∪ s' ≤ᶠ[l] t ∪ t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem EventuallyLE.union {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∪ s' : Set α) ≤ᶠ[l] (t ∪ t' : Set α) :=
  h'.mp <| h.mono fun _ => Or.imp

@[gcongr, mono]
/-
**Filter.EventuallyLE.compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {s t : Set α} {l : Filter α}, s ≤ᶠ[l] t → tᶜ ≤ᶠ[l] sᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem EventuallyLE.compl {s t : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) :
    (tᶜ : Set α) ≤ᶠ[l] (sᶜ : Set α) :=
  h.mono fun _ => mt

@[gcongr, mono]
/-
**Filter.EventuallyLE.diff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {s t s' t' : Set α} {l : Filter α}, s ≤ᶠ[l] t → t' ≤ᶠ[l] s'
 → s \ s' ≤ᶠ[l] t \ t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s ≤ᶠ[l] t → s' ≤ᶠ[l] t' → s ∩ s' ≤ᶠ[l] t ∩ t'
· 使用定理 `Filter.EventuallyLE.compl`：∀ {α : Type u} {s t : Set α} {l : Filter α}, 
s ≤ᶠ[l] t → tᶜ ≤ᶠ[l] sᶜ
-/
theorem EventuallyLE.diff {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : t' ≤ᶠ[l] s') :
    (s \ s' : Set α) ≤ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl
/-
**Filter.set_eventuallyLE_iff_mem_inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
形式化陈述：set_eventuallyLE_iff_mem_inf_principal {s t : Set α} {l : Filter α} : s <=
ᶠ[l] t ↔ t in l ⊓ 𝓟 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
-/
theorem set_eventuallyLE_iff_mem_inf_principal {s t : Set α} {l : Filter α} :
    s ≤ᶠ[l] t ↔ t ∈ l ⊓ 𝓟 s :=
  eventually_inf_principal.symm
/-
**Filter.set_eventuallyLE_iff_inf_principal_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter
`。
形式化陈述：set_eventuallyLE_iff_inf_principal_le {s t : Set α} {l : Filter α} : s <=ᶠ
[l] t ↔ l ⊓ 𝓟 s <= l ⊓ 𝓟 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.set_eventuallyLE_iff_mem_inf_principal`：set_eventuallyLE_iff_mem_
inf_principal {s t : Set α} {l : Filter α} : s <=ᶠ[l] t ↔ t in l ⊓ 𝓟 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem set_eventuallyLE_iff_inf_principal_le {s t : Set α} {l : Filter α} :
    s ≤ᶠ[l] t ↔ l ⊓ 𝓟 s ≤ l ⊓ 𝓟 t :=
  set_eventuallyLE_iff_mem_inf_principal.trans <| by
    simp only [le_inf_iff, inf_le_left, true_and, le_principal_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.set_eventuallyEq_iff_inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：set_eventuallyEq_iff_inf_principal {s t : Set α} {l : Filter α} : s =ᶠ[l] 
t ↔ l ⊓ 𝓟 s = l ⊓ 𝓟 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem set_eventuallyEq_iff_inf_principal {s t : Set α} {l : Filter α} :
    s =ᶠ[l] t ↔ l ⊓ 𝓟 s = l ⊓ 𝓟 t := by
  simp only [eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le]

@[to_dual (attr := gcongr)]
/-
**Filter.EventuallyLE.sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : SemilatticeSup β] {l : Filter α} {f₁ f
₂ g₁ g₂ : α → β},   f₁ ≤ᶠ[l] f₂ → g₁ ≤ᶠ[l] g₂ → f₁ ⊔ g₁ ≤ᶠ[l] f₂ ⊔ g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem EventuallyLE.sup [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂)
    (hg : g₁ ≤ᶠ[l] g₂) : f₁ ⊔ g₁ ≤ᶠ[l] f₂ ⊔ g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx

@[to_dual le_inf]
/-
**Filter.EventuallyLE.sup_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : SemilatticeSup β] {l : Filter α} {f g 
h : α → β},   f ≤ᶠ[l] h → g ≤ᶠ[l] h → f ⊔ g ≤ᶠ[l] h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem EventuallyLE.sup_le [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hf : f ≤ᶠ[l] h)
    (hg : g ≤ᶠ[l] h) : f ⊔ g ≤ᶠ[l] h := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.sup_le hfx hgx

@[to_dual inf_le_of_left_le]
/-
**Filter.EventuallyLE.le_sup_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventu
allyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : SemilatticeSup β] {l : Filter α} {f g 
h : α → β}, h ≤ᶠ[l] f → h ≤ᶠ[l] f ⊔ g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
-/
theorem EventuallyLE.le_sup_of_le_left [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hf : h ≤ᶠ[l] f) : h ≤ᶠ[l] f ⊔ g :=
  hf.mono fun _ => _root_.le_sup_of_le_left

@[to_dual inf_le_of_right_le]
/-
**Filter.EventuallyLE.le_sup_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Event
uallyLE`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : SemilatticeSup β] {l : Filter α} {f g 
h : α → β}, h ≤ᶠ[l] g → h ≤ᶠ[l] f ⊔ g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
-/
theorem EventuallyLE.le_sup_of_le_right [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hg : h ≤ᶠ[l] g) : h ≤ᶠ[l] f ⊔ g :=
  hg.mono fun _ => _root_.le_sup_of_le_right
/-
**Filter.join_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：join_le {f : Filter (Filter α)} {l : Filter α} (h : forallᶠ m in f, m <= l
) : join f <= l
参数：Filter α；h : forallᶠ m in f, m <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem join_le {f : Filter (Filter α)} {l : Filter α} (h : ∀ᶠ m in f, m ≤ l) : join f ≤ l :=
  fun _ hs => h.mono fun _ hm => hm hs

end EventuallyEq

end Filter

open Filter

/-
**Set.EqOn.eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α -> β} (h : EqOn f g s) : 
f =ᶠ[𝓟 s] g
参数：h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α → β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g :=
  h
/-
**Set.EqOn.eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.EqOn.eventuallyEq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α -> 
β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
参数：h : EqOn f g s；hl : s in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem Set.EqOn.eventuallyEq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α → β} (h : EqOn f g s)
    (hl : s ∈ l) : f =ᶠ[l] g :=
  h.eventuallyEq.filter_mono <| Filter.le_principal_iff.2 hl
/-
**LE.le.eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} (h : s subseteq t) : s
 <=ᶠ[l] t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} (h : s ⊆ t) : s ≤ᶠ[l] t :=
  Filter.Eventually.of_forall h

@[deprecated (since := "2026-03-16")] alias HasSubset.Subset.eventuallyLE := LE.le.eventuallyLE

variable {α β : Type*} {F : Filter α} {G : Filter β}

namespace Filter

/-
**Filter.compl_mem_comk** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：compl_mem_comk {p : Set α -> Prop} {he hmono hunion s} : sᶜ in comk p he h
mono hunion ↔ p s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma compl_mem_comk {p : Set α → Prop} {he hmono hunion s} :
    sᶜ ∈ comk p he hmono hunion ↔ p s := by
  simp

end Filter

