/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.OuterMeasure.Induced
public import Mathlib.Tactic.FinCases

/-!
# Additive Contents

An additive content `m` on a set of sets `C` is a set function with value 0 at the empty set which
is finitely additive on `C`. That means that for any finset `I` of pairwise disjoint sets in `C`
such that `⋃₀ I ∈ C`, `m (⋃₀ I) = ∑ s ∈ I, m s`.

Mathlib also has a definition of contents over compact sets: see `MeasureTheory.Content`.
A `Content` is in particular an `AddContent` on the set of compact sets.

## Main definitions

* `MeasureTheory.AddContent G C`: additive contents over the set of sets `C` taking values in the
  additive monoid `G`.
* `MeasureTheory.AddContent.IsSigmaSubadditive`: an `AddContent` with values in `ℝ≥0∞` is
  σ-subadditive if `m (⋃ i, f i) ≤ ∑' i, m (f i)` for any sequence of sets `f` in `C`
  such that `⋃ i, f i ∈ C`.

## Main statements

Let `m` be an `AddContent C` with values in `ℝ≥0∞`. If `C` is a set semi-ring (`IsSetSemiring C`)
we have the properties

* `MeasureTheory.sum_addContent_le_of_subset`: if `I` is a finset of pairwise disjoint sets in `C`
  and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`.
* `MeasureTheory.addContent_mono`: if `s ⊆ t` for two sets in `C`, then `m s ≤ m t`.
* `MeasureTheory.addContent_sUnion_le_sum`: an `AddContent C` on a `SetSemiring C` is
  sub-additive.
* `MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le`: if an
  `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive.
* `MeasureTheory.addContent_union'`: if `s, t ∈ C` are disjoint and `s ∪ t ∈ C`,
  then `m (s ∪ t) = m s + m t`.
  If `C` is a set ring (`IsSetRing`), then `addContent_union` gives the same conclusion without the
  hypothesis `s ∪ t ∈ C` (since it is a consequence of `IsSetRing C`).

If `C` is a set ring (`MeasureTheory.IsSetRing C`), we have

* `MeasureTheory.addContent_union_le`: for `s, t ∈ C`, `m (s ∪ t) ≤ m s + m t`
* `MeasureTheory.addContent_le_sdiff`: for `s, t ∈ C`, `m s - m t ≤ m (s \ t)`
* `IsSetRing.addContent_of_union`: a function on a ring of sets which is additive on pairs of
  disjoint sets defines an additive content
* `addContent_iUnion_eq_sum_of_tendsto_zero`: if an additive content is continuous at `∅`, then
  its value on a countable disjoint union is the sum of the values
* `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum`: if an `AddContent` is
  σ-additive on a set ring, then it is σ-subadditive.

We define a specific example of `AddContent`, called `AddContent.onIoc`, on the semiring of sets
made of open-closed intervals, mapping `(a, b]` to `f b - f a`.
-/

@[expose] public section

open Set Finset Function Filter

open scoped ENNReal Topology Function

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}
  {G : Type*} [AddCommMonoid G]

variable (G) in
/-- An additive content is a set function with value 0 at the empty set which is finitely additive
on a given set of sets. -/
/-
**MeasureTheory.AddContent** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → (G : Type u_2) → [AddCommMonoid G] → Set (Set α) → Type (
max u_1 u_2)
参数：G : Type u_2；Set α；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive content is a set function with value 0 at the empty set which is fin
itely additive
on a given set of sets.
-/
structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α → G
  empty' : toFun ∅ = 0
  sUnion' (I : Finset (Set α)) (_h_ss : ↑I ⊆ C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I ∈ C) :
    toFun (⋃₀ I) = ∑ u ∈ I, toFun u
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (AddContent G C) :=
  ⟨{toFun := fun _ => 0
    empty' := by simp
    sUnion' := by simp }⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (AddContent G C) (Set α) G where
  coe m s := m.toFun s
  coe_injective m m' _ := by
    cases m
    cases m'
    congr

variable {m m' : AddContent G C}
/-
**MeasureTheory.AddContent.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AddConte
nt`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G]
 {m m' : MeasureTheory.AddContent G C},   (∀ (s : Set α), m s = m' s) → m = m'
参数：Set α；∀ (s : Set α), m s = m' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] protected lemma AddContent.ext (h : ∀ s, m s = m' s) : m = m' :=
  DFunLike.ext _ _ h
/-
**MeasureTheory.addContent_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G]
 {m : MeasureTheory.AddContent G C}, m ∅ = 0
参数：Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AddContent.empty'`：∀ {α : Type u_1} {G : Type u_2} [inst :
 AddCommMonoid G] {C : Set (Set α)} (self : MeasureTheory.AddContent G C),   sel
f.toFun ∅ = 0
-/
@[simp] lemma addContent_empty : m ∅ = 0 := m.empty'
/-
**MeasureTheory.addContent_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_sUnion (h_ss : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Se
t (Set α)) id) (h_mem : ⋃₀ ↑I in C) : m (⋃₀ I) = ∑ u in I, m u
参数：h_ss : ↑I subseteq C；h_dis : PairwiseDisjoint (I : Set (Set α)) id；h_mem : ⋃₀
 ↑I in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AddContent.sUnion'`：∀ {α : Type u_1} {G : Type u_2} [inst 
: AddCommMonoid G] {C : Set (Set α)} (self : MeasureTheory.AddContent G C)   (I 
: Finset (Set α)), ↑I …
-/
lemma addContent_sUnion (h_ss : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u ∈ I, m u :=
  m.sUnion' I h_ss h_dis h_mem
/-
**MeasureTheory.addContent_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_biUnion {ι : Type*} {a : Finset ι} {f : ι -> Set α} (hf : foral
l i in a, f i in C) (h_dis : PairwiseDisjoint ↑a f) (h_mem : ⋃ i in a, f i in C)
 : m (⋃ i in a, f i) = ∑ i in a, m (f i)
参数：hf : forall i in a, f i in C；h_dis : PairwiseDisjoint ↑a f；h_mem : ⋃ i in a, 
f i in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.addContent_sUnion`：addContent_sUnion (h_ss : ↑I subseteq C
) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I in C) : m (⋃₀ I
) = ∑ u in I, m u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Pairwise.image`：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → Prop} {
f : ι → α} {s : Set ι},   s.Pairwise (Function.onFun r f) → (f '' s).Pairwise r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_image_of_pairwise_eq_zero`：∀ {ι : Type u_1} {κ : Type u_2} {M
 : Type u_4} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {f : κ → ι} {g : 
ι → M}   {I : Finset κ}, (…
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
-/
lemma addContent_biUnion {ι : Type*} {a : Finset ι} {f : ι → Set α} (hf : ∀ i ∈ a, f i ∈ C)
    (h_dis : PairwiseDisjoint ↑a f) (h_mem : ⋃ i ∈ a, f i ∈ C) :
    m (⋃ i ∈ a, f i) = ∑ i ∈ a, m (f i) := by
  have A : ⋃ i ∈ a, f i = ⋃₀ (a.image f) := by simp
  rw [A, addContent_sUnion]; rotate_left
  · grind
  · simpa using! h_dis.image
  · rwa [← A]
  rw [sum_image_of_pairwise_eq_zero]
  refine h_dis.imp ?_
  grind [Set.bot_eq_empty (α := α), addContent_empty]
/-
**MeasureTheory.addContent_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_iUnion {ι : Type*} [Fintype ι] {f : ι -> Set α} (hf : forall i,
 f i in C) (h_dis : Pairwise (Disjoint on f)) (h_mem : ⋃ i, f i in C) : m (⋃ i, 
f i) = ∑ i, m (f i)
参数：hf : forall i, f i in C；h_dis : Pairwise (Disjoint on f)；h_mem : ⋃ i, f i in 
C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.addContent_biUnion`：addContent_biUnion {ι : Type*} {a : Fi
nset ι} {f : ι -> Set α} (hf : forall i in a, f i in C) (h_dis : PairwiseDisjoin
t ↑a f) (h_mem : ⋃ i i…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
-/
lemma addContent_iUnion {ι : Type*} [Fintype ι] {f : ι → Set α} (hf : ∀ i, f i ∈ C)
    (h_dis : Pairwise (Disjoint on f)) (h_mem : ⋃ i, f i ∈ C) :
    m (⋃ i, f i) = ∑ i, m (f i) := by
  convert! addContent_biUnion (a := Finset.univ) (f := f) (m := m) ?_ ?_ ?_ using 1
  · simp
  · simpa
  · simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using h_dis
  · simpa
/-
**MeasureTheory.addContent_union'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_union' (hs : s in C) (ht : t in C) (hst : s union t in C) (h_di
s : Disjoint s t) : m (s union t) = m s + m t
参数：hs : s in C；ht : t in C；hst : s union t in C；h_dis : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.univ_castSuccEmb`：Fin.univ_castSuccEmb (n : Nat) : (univ : Finset (F
in (n + 1))) = Finset.cons (Fin.last n) (univ.map Fin.castSuccEmb) (by simp [map
_eq_image]…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.addContent_iUnion`：addContent_iUnion {ι : Type*} [Fintype 
ι] {f : ι -> Set α} (hf : forall i, f i in C) (h_dis : Pairwise (Disjoint on f))
 (h_mem : ⋃ i, f i in…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
lemma addContent_union' (hs : s ∈ C) (ht : t ∈ C) (hst : s ∪ t ∈ C) (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t := by
  have A : s ∪ t = ⋃ i, ![s, t] i := by ext; simp
  convert! addContent_iUnion (f := ![s, t]) (m := m) (fun i ↦ ?_) (fun i j hij ↦ ?_) ?_ using 2
  · simp [Fin.univ_castSuccEmb, add_comm]
  · fin_cases i <;> simpa
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed all four
    cases. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
    the new canonicalizer; a minimization would help. The original proof was:
    `fin_cases i <;> fin_cases j <;> grind` -/
    fin_cases i <;> fin_cases j
    · grind
    · assumption
    · exact h_dis.symm
    · grind
  · rwa [← A]

/-- An additive content with values in `ℝ≥0∞` is said to be sigma-sub-additive if for any sequence
of sets `f` in `C` such that `⋃ i, f i ∈ C`, we have `m (⋃ i, f i) ≤ ∑' i, m (f i)`. -/
/-
**MeasureTheory.AddContent.IsSigmaSubadditive** 是 Mathlib 中的一个定义，位于命名空间 `Measure
Theory.AddContent`。
形式化陈述：{α : Type u_1} → {C : Set (Set α)} → MeasureTheory.AddContent ENNReal C → 
Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive content with values in `ℝ≥0∞` is said to be sigma-sub-additive if fo
r any sequence
of sets `f` in `C` such that `⋃ i, f i ∈ C`, we have `m (⋃ i, f i) ≤ ∑' i, m (f 
i)`.
-/
def AddContent.IsSigmaSubadditive (m : AddContent ℝ≥0∞ C) : Prop :=
  ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C), m (⋃ i, f i) ≤ ∑' i, m (f i)

section IsSetSemiring

/-
**MeasureTheory.addContent_eq_add_disjointOfDiffUnion_of_subset** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_eq_add_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs
 : s in C) (hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s) (h_dis : P
airwiseDisjoint (I : Set (Set α)) id) : m s = ∑ i in I, m i + ∑ i in hC.disjoint
OfDiffUnion hs hI, m i
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C；hI_ss : forall t in I, t 
subseteq s；h_dis : PairwiseDisjoint (I : Set (Set α)) id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsSetSemiring.sUnion_union_disjointOfDiffUnion_of_subset`：
sUnion_union_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s) :…
· 使用引理 `MeasureTheory.addContent_sUnion`：addContent_sUnion (h_ss : ↑I subseteq C
) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I in C) : m (⋃₀ I
) = ∑ u in I, m u
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用引理 `MeasureTheory.IsSetSemiring.disjointOfDiffUnion_subset`：disjointOfDiffUn
ion_subset (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) : ↑(hC.disj
ointOfDiffUnion hs hI) subseteq C
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_union_disjointOfDiffUnion`：
pairwiseDisjoint_union_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Set (Set…
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用引理 `MeasureTheory.IsSetSemiring.disjoint_disjointOfDiffUnion`：disjoint_disjo
intOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) : Disjo
int I (hC.disjointOfDiffUnion hs hI)
-/
lemma addContent_eq_add_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    m s = ∑ i ∈ I, m i + ∑ i ∈ hC.disjointOfDiffUnion hs hI, m i := by
  conv_lhs => rw [← hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]
  rw [addContent_sUnion]
  · rw [sum_union]
    exact hC.disjoint_disjointOfDiffUnion hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.disjointOfDiffUnion_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_disjointOfDiffUnion hs hI h_dis
  · rwa [hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]

/-- For an `m : addContent C` on a `SetSemiring C` and `s t : Set α` with `s ⊆ t`, we can write
`m t = m s + ∑ i in hC.disjointOfDiff ht hs, m i`. -/
/-
**MeasureTheory.eq_add_disjointOfDiff_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：eq_add_disjointOfDiff_of_subset (hC : IsSetSemiring C) (hs : s in C) (ht :
 t in C) (hst : s subseteq t) : m t = m s + ∑ i in hC.disjointOfDiff ht hs, m i
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsSetSemiring.sUnion_insert_disjointOfDiff`：sUnion_insert_
disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) (hst : t subse
teq s) : ⋃₀ insert t (hC.disjointOfDiff hs ht)…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用引理 `MeasureTheory.addContent_sUnion`：addContent_sUnion (h_ss : ↑I subseteq C
) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I in C) : m (⋃₀ I
) = ∑ u in I, m u
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用引理 `MeasureTheory.IsSetSemiring.subset_disjointOfDiff`：subset_disjointOfDiff
 (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : ↑(hC.disjointOfDiff hs ht)
 subseteq C
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_insert_disjointOfDiff`：pair
wiseDisjoint_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t 
in C) : PairwiseDisjoint (insert t (hC.disjointOfDiff hs…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `MeasureTheory.IsSetSemiring.notMem_disjointOfDiff`：notMem_disjointOfDiff
 (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : t ∉ hC.disjointOfDiff hs h
t

--- 原说明 ---
For an `m : addContent C` on a `SetSemiring C` and `s t : Set α` with `s ⊆ t`, w
e can write
`m t = m s + ∑ i in hC.disjointOfDiff ht hs, m i`.
-/
theorem eq_add_disjointOfDiff_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) :
    m t = m s + ∑ i ∈ hC.disjointOfDiff ht hs, m i := by
  conv_lhs => rw [← hC.sUnion_insert_disjointOfDiff ht hs hst]
  rw [← coe_insert, addContent_sUnion]
  · rw [sum_insert]
    exact hC.notMem_disjointOfDiff ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.subset_disjointOfDiff ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_disjointOfDiff ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_disjointOfDiff ht hs hst]

/-- If a set can be written in two different ways as a disjoint union of elements of a semi-ring
of sets `C`, then the sums of the values of `m : addContent C` along the two decompositions give
the same result.
In other words, `m` can be canonically extended to finite unions of elements of `C`. -/
/-
**MeasureTheory.sum_addContent_eq_of_sUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：sum_addContent_eq_of_sUnion_eq (hC : IsSetSemiring C) (J J' : Finset (Set 
α)) (hJ : ↑J subseteq C) (hJdisj : PairwiseDisjoint (J : Set (Set α)) id) (hJ' :
 ↑J' subseteq C) (hJ'disj : PairwiseDisjoint (J' : Set (Set α)) id) (h : ⋃₀ (J :
 Set (Set α)) = ⋃₀ J') : ∑ s in J, m s = ∑ t in J', m t
参数：hC : IsSetSemiring C；J J' : Finset (Set α)；hJ : ↑J subseteq C；hJdisj : Pairwi
seDisjoint (J : Set (Set α)) id；hJ' : ↑J' subseteq C；hJ'disj : PairwiseDisjoint 
(J' : Set (Set α)) id；h : ⋃₀ (J : Set (Set α)) = ⋃₀ J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用引理 `MeasureTheory.addContent_biUnion`：addContent_biUnion {ι : Type*} {a : Fi
nset ι} {f : ι -> Set α} (hf : forall i in a, f i in C) (h_dis : PairwiseDisjoin
t ↑a f) (h_mem : ⋃ i i…
· 使用定理 `MeasureTheory.IsSetSemiring.inter_mem`：∀ {α : Type u_1} {C : Set (Set α)
}, MeasureTheory.IsSetSemiring C → ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C
· 使用定理 `Set.PairwiseDisjoint.mono`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f g : ι → α},   s.PairwiseDisjoint
 f → g ≤ f → s.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…

--- 原说明 ---
If a set can be written in two different ways as a disjoint union of elements of
 a semi-ring
of sets `C`, then the sums of the values of `m : addContent C` along the two dec
ompositions give
the same result.
In other words, `m` can be canonically extended to finite unions of elements of 
`C`.
-/
theorem sum_addContent_eq_of_sUnion_eq (hC : IsSetSemiring C) (J J' : Finset (Set α))
    (hJ : ↑J ⊆ C) (hJdisj : PairwiseDisjoint (J : Set (Set α)) id)
    (hJ' : ↑J' ⊆ C) (hJ'disj : PairwiseDisjoint (J' : Set (Set α)) id)
    (h : ⋃₀ (J : Set (Set α)) = ⋃₀ J') :
    ∑ s ∈ J, m s = ∑ t ∈ J', m t := by
  calc ∑ s ∈ J, m s
  _ = ∑ s ∈ J, (∑ t ∈ J', m (s ∩ t)) := by
    apply Finset.sum_congr rfl (fun s hs ↦ ?_)
    have : s = ⋃ t ∈ J', s ∩ t := by
      simp_rw [← Finset.set_biUnion_coe, ← inter_iUnion, left_eq_inter, ← sUnion_eq_biUnion, ← h]
      exact subset_sUnion_of_mem hs
    nth_rewrite 1 [this]
    apply addContent_biUnion
    · exact fun t ht ↦ hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJ'disj.mono fun _ ↦ by simp
    · rw [← this]
      exact hJ hs
  _ = ∑ t ∈ J', (∑ s ∈ J, m (s ∩ t)) := sum_comm
  _ = ∑ t ∈ J', m t := by
    apply Finset.sum_congr rfl (fun t ht ↦ ?_)
    have : t = ⋃ s ∈ J, s ∩ t := by
      simp_rw [← Finset.set_biUnion_coe, ← iUnion_inter, right_eq_inter, ← sUnion_eq_biUnion, h]
      exact subset_sUnion_of_mem ht
    nth_rewrite 2 [this]
    apply (addContent_biUnion _ _ _).symm
    · exact fun s hs ↦ hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJdisj.mono fun _ ↦ by simp
    · rw [← this]
      exact hJ' ht

open scoped Classical in
/-- Extend a content over `C` to the finite unions of elements of `C` by additivity.
Use instead `AddContent.supClosure` which is the same function bundled as an `AddContent`. -/
/-
**MeasureTheory.AddContent.supClosureFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a content over `C` to the finite unions of elements of `C` by additivity.
Use instead `AddContent.supClosure` which is the same function bundled as an `Ad
dContent`.
-/
private noncomputable def AddContent.supClosureFun (m : AddContent G C) (s : Set α) : G :=
  if h : ∃ (J : Finset (Set α)), ↑J ⊆ C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J
    then ∑ s ∈ h.choose, m s
  else 0
/-
**MeasureTheory.AddContent.supClosureFun_apply** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma AddContent.supClosureFun_apply (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finset (Set α)}
    (hJ : ↑J ⊆ C) (h'J : PairwiseDisjoint (J : Set (Set α)) id) (hs : s = ⋃₀ ↑J) :
    m.supClosureFun s = ∑ s ∈ J, m s := by
  have h : ∃ (J : Finset (Set α)), ↑J ⊆ C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J :=
    ⟨J, hJ, h'J, hs⟩
  simp only [supClosureFun, h, ↓reduceDIte]
  apply sum_addContent_eq_of_sUnion_eq hC _ _ h.choose_spec.1 h.choose_spec.2.1 hJ h'J
  rw [← hs]
  exact h.choose_spec.2.2.symm
/-
**MeasureTheory.AddContent.supClosureFun_apply_of_mem** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma AddContent.supClosureFun_apply_of_mem (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} (hs : s ∈ C) :
    m.supClosureFun s = m s := by
  have : m.supClosureFun s = ∑ t ∈ {s}, m t :=
    m.supClosureFun_apply hC (by simp [hs]) (by simp) (by simp)
  simp [this]

/-- Extend a content over `C` to the finite unions of elements of `C` by additivity. -/
/-
**MeasureTheory.AddContent.supClosure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.A
ddContent`。
形式化陈述：{α : Type u_1} →   {C : Set (Set α)} →     {G : Type u_2} →       [inst : 
AddCommMonoid G] →         MeasureTheory.AddContent G C → MeasureTheory.IsSetSem
iring C → MeasureTheory.AddContent G (supClosure C)
参数：Set α；supClosure C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a content over `C` to the finite unions of elements of `C` by additivity.
-/
@[no_expose] noncomputable def AddContent.supClosure (m : AddContent G C) (hC : IsSetSemiring C) :
    AddContent G (supClosure C) where
  toFun := m.supClosureFun
  empty' := by rw [m.supClosureFun_apply_of_mem hC hC.empty_mem, addContent_empty]
  sUnion' I hI h'I hh'I := by
    choose! J hJC using fun s (hs : s ∈ I) => hC.mem_supClosure_iff.mp (hI hs)
    let K : Finpartition (I.sup id) := Finpartition.combine J h'I.supIndep
    rw [← sSup_eq_sUnion, ← sup_id_eq_sSup, ← K.sup_parts, sup_id_eq_sSup, sSup_eq_sUnion,
      m.supClosureFun_apply hC (by simpa [K] using hJC) K.supIndep.pairwiseDisjoint rfl,
      Finpartition.sum_combine]
    refine Finset.sum_congr rfl fun i hi ↦ Eq.symm <|
      m.supClosureFun_apply hC (hJC i hi) (J i).supIndep.pairwiseDisjoint ?_
    rw [← sSup_eq_sUnion, ← sup_id_eq_sSup, (J i).sup_parts]
/-
**MeasureTheory.AddContent.supClosure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AddContent`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G]
 (hC : MeasureTheory.IsSetSemiring C)   (m : MeasureTheory.AddContent G C) {s : 
Set α} {J : Finset (Set α)},   ↑J ⊆ C → (↑J).PairwiseDisjoint id → s = ⋃₀ ↑J → (
m.supClosure hC) s = ∑ s ∈ J, m s
参数：Set α；hC : MeasureTheory.IsSetSemiring C；m : MeasureTheory.AddContent G C；Set
 α；↑J；m.supClosure hC。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.AddContent.0.MeasureTheory.AddCon
tent.supClosureFun_apply`：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_2} [ins
t : AddCommMonoid G],   MeasureTheory.IsSetSemiring C →     ∀ (m : MeasureTheory
.AddCo…
-/
lemma AddContent.supClosure_apply (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finset (Set α)}
    (hJ : ↑J ⊆ C) (h'J : PairwiseDisjoint (J : Set (Set α)) id) (hs : s = ⋃₀ ↑J) :
    m.supClosure hC s = ∑ s ∈ J, m s :=
  m.supClosureFun_apply hC hJ h'J hs
/-
**MeasureTheory.AddContent.supClosure_apply_finpartition** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AddContent`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G]
 (hC : MeasureTheory.IsSetSemiring C)   (m : MeasureTheory.AddContent G C) {s : 
Set α} {J : Finpartition s},   ↑J.parts ⊆ C → (m.supClosure hC) s = ∑ s ∈ J.part
s, m s
参数：Set α；hC : MeasureTheory.IsSetSemiring C；m : MeasureTheory.AddContent G C；m.s
upClosure hC。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AddContent.supClosure_apply`：∀ {α : Type u_1} {C : Set (Se
t α)} {G : Type u_2} [inst : AddCommMonoid G] (hC : MeasureTheory.IsSetSemiring 
C)   (m : MeasureTheory.AddCont…
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma AddContent.supClosure_apply_finpartition (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finpartition s} (hJ : ↑J.parts ⊆ C) :
    m.supClosure hC s = ∑ s ∈ J.parts, m s := by
  rw [m.supClosure_apply _ hJ J.disjoint]
  nth_rewrite 1 [← J.sup_parts, Finset.sup_set_eq_biUnion, sUnion_eq_biUnion]
  simp
/-
**MeasureTheory.AddContent.supClosure_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AddContent`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G]
 (hC : MeasureTheory.IsSetSemiring C)   (m : MeasureTheory.AddContent G C) {s : 
Set α}, s ∈ C → (m.supClosure hC) s = m s
参数：Set α；hC : MeasureTheory.IsSetSemiring C；m : MeasureTheory.AddContent G C；m.s
upClosure hC。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.AddContent.0.MeasureTheory.AddCon
tent.supClosureFun_apply_of_mem`：∀ {α : Type u_1} {C : Set (Set α)} {G : Type u_
2} [inst : AddCommMonoid G],   MeasureTheory.IsSetSemiring C →     ∀ (m : Measur
eTheory.AddCo…
-/
lemma AddContent.supClosure_apply_of_mem (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} (hs : s ∈ C) :
    m.supClosure hC s = m s :=
  m.supClosureFun_apply_of_mem hC hs

variable [PartialOrder G] [CanonicallyOrderedAdd G]

/-- For an `m : addContent C` on a `SetSemiring C`, if `I` is a `Finset` of pairwise disjoint
  sets in `C` and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`. -/
/-
**MeasureTheory.sum_addContent_le_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：sum_addContent_le_of_subset (hC : IsSetSemiring C) (h_ss : ↑I subseteq C) 
(h_dis : PairwiseDisjoint (I : Set (Set α)) id) (ht : t in C) (hJt : forall s in
 I, s subseteq t) : ∑ u in I, m u <= m t
参数：hC : IsSetSemiring C；h_ss : ↑I subseteq C；h_dis : PairwiseDisjoint (I : Set (
Set α)) id；ht : t in C；hJt : forall s in I, s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.addContent_eq_add_disjointOfDiffUnion_of_subset`：addConten
t_eq_add_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s in C) (hI 
: ↑I subseteq C) (hI_ss : forall t in I, t subseteq…
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
For an `m : addContent C` on a `SetSemiring C`, if `I` is a `Finset` of pairwise
 disjoint
  sets in `C` and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`.
-/
lemma sum_addContent_le_of_subset (hC : IsSetSemiring C)
    (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (ht : t ∈ C) (hJt : ∀ s ∈ I, s ⊆ t) :
    ∑ u ∈ I, m u ≤ m t := by
  rw [addContent_eq_add_disjointOfDiffUnion_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

/-- An `addContent C` on a `SetSemiring C` is monotone. -/
/-
**MeasureTheory.addContent_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_mono (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) (hst : 
s subseteq t) : m s <= m t
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.sum_addContent_le_of_subset`：sum_addContent_le_of_subset (
hC : IsSetSemiring C) (h_ss : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Set 
(Set α)) id) (ht : t in C) (hJt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.singleton_subset_set_iff`：singleton_subset_set_iff {s : Set α} {a
 : α} : ↑({a} : Finset α) subseteq s ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a

--- 原说明 ---
An `addContent C` on a `SetSemiring C` is monotone.
-/
lemma addContent_mono (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    (hst : s ⊆ t) :
    m s ≤ m t := by
  have h := sum_addContent_le_of_subset (m := m) hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp [hst]
/-
**MeasureTheory.addContent_le_sum_of_subset_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：addContent_le_sum_of_subset_sUnion {m : AddContent G C} (hC : IsSetSemirin
g C) {J : Finset (Set α)} (h_ss : ↑J subseteq C) (ht : t in C) (htJ : t subseteq
 ⋃₀ ↑J) : m t <= ∑ u in J, m u
参数：hC : IsSetSemiring C；Set α；h_ss : ↑J subseteq C；ht : t in C；htJ : t subseteq 
⋃₀ ↑J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MeasureTheory.IsSetRing.disjointed_mem`：disjointed_mem {ι : Type*} [Preo
rder ι] [LocallyFiniteOrderBot ι] (hC : IsSetRing C) {s : ι -> Set α} (hs : fora
ll j, s j in C) (i : ι) : di…
· 使用定理 `MeasureTheory.IsSetSemiring.isSetRing_supClosure`：isSetRing_supClosure (
hC : IsSetSemiring C) : IsSetRing (supClosure C) where empty_mem
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用引理 `SupClosed.iSup_mem`：SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hb
ot : ⊥ in s) (hf : forall i, f i in s) : ⨆ i, f i in s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用定理 `MeasureTheory.IsSetSemiring.empty_mem`：∀ {α : Type u_1} {C : Set (Set α)
}, MeasureTheory.IsSetSemiring C → ∅ ∈ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AddContent.supClosure_apply_of_mem`：∀ {α : Type u_1} {C : 
Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G] (hC : MeasureTheory.IsSetSe
miring C)   (m : MeasureTheory.AddCont…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `MeasureTheory.addContent_mono`：addContent_mono (hC : IsSetSemiring C) (h
s : s in C) (ht : t in C) (hst : s subseteq t) : m s <= m t
· 使用引理 `MeasureTheory.IsSetRing.isSetSemiring`：isSetSemiring (hC : IsSetRing C) 
: IsSetSemiring C where empty_mem
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.addContent_iUnion`：addContent_iUnion {ι : Type*} [Fintype 
ι] {f : ι -> Set α} (hf : forall i, f i in C) (h_dis : Pairwise (Disjoint on f))
 (h_mem : ⋃ i, f i in…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.attach_eq_univ`：Finset.attach_eq_univ {s : Finset α} : s.attach =
 Finset.univ
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
-/
lemma addContent_le_sum_of_subset_sUnion {m : AddContent G C} (hC : IsSetSemiring C)
    {J : Finset (Set α)} (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u ∈ J, m u := by
  simp_rw +singlePass [← sSup_eq_sUnion, sSup_eq_iSup', SetLike.coe_sort_coe,
    ← J.equivFin.symm.iSup_comp, iSup_eq_iUnion, ← iUnion_disjointed] at htJ
  set f := disjointed fun j => (J.equivFin.symm j).1
  have h1 : ∀ j, f j ∈ supClosure C :=
    hC.isSetRing_supClosure.disjointed_mem fun j =>
      subset_supClosure <| h_ss <| (J.equivFin.symm j).2
  have h2 : Pairwise (Disjoint on f) := disjoint_disjointed _
  have h3 : ⋃ i, f i ∈ supClosure C :=
    supClosed_supClosure.iSup_mem (subset_supClosure hC.empty_mem) h1
  grw [← m.supClosure_apply_of_mem hC ht,
    addContent_mono hC.isSetRing_supClosure.isSetSemiring (subset_supClosure ht) h3 htJ,
    addContent_iUnion h1 h2 h3, ← J.sum_attach, Finset.attach_eq_univ, ← J.equivFin.symm.sum_comp]
  gcongr with j -
  rw [← m.supClosure_apply_of_mem hC (h_ss (J.equivFin.symm _).2)]
  exact addContent_mono hC.isSetRing_supClosure.isSetSemiring (h1 j)
    (subset_supClosure (h_ss (J.equivFin.symm j).2)) (disjointed_subset _ j)

/-- An `addContent C` on a `SetSemiring C` is sub-additive. -/
/-
**MeasureTheory.addContent_sUnion_le_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：addContent_sUnion_le_sum {m : AddContent G C} (hC : IsSetSemiring C) (J : 
Finset (Set α)) (h_ss : ↑J subseteq C) (h_mem : ⋃₀ ↑J in C) : m (⋃₀ ↑J) <= ∑ u i
n J, m u
参数：hC : IsSetSemiring C；J : Finset (Set α)；h_ss : ↑J subseteq C；h_mem : ⋃₀ ↑J in
 C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.addContent_le_sum_of_subset_sUnion`：addContent_le_sum_of_s
ubset_sUnion {m : AddContent G C} (hC : IsSetSemiring C) {J : Finset (Set α)} (h
_ss : ↑J subseteq C) (ht : t in C) (ht…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
An `addContent C` on a `SetSemiring C` is sub-additive.
-/
lemma addContent_sUnion_le_sum {m : AddContent G C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u ∈ J, m u :=
  addContent_le_sum_of_subset_sUnion hC h_ss h_mem subset_rfl

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
/-
**MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddCont
ent Real>=0∞ C} (hC : IsSetSemiring C) -- TODO: `m_subadd` is in fact equivalent
 to `m.IsSigmaSubadditive`. (m_subadd : forall (f : Nat -> Set α) (_ : forall i,
 f i in C) (_ : ⋃ i, f i in C) (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f 
i) <= ∑' i, m (f i)) (f : Nat -> Set α) (hf : forall i, f i in C) (hf_Union : (⋃
 i, f i) in C) (hf_disj : Pairwise (Disjoint on f)) : m (⋃ i, f i) = ∑' i, m (f 
i)
参数：hC : IsSetSemiring C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Summable.tsum_le_of_sum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : Summati
onFilter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topologic
alSpace α] [Orde…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_image_of_disjoint`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type 
u_4} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι]   [inst_2 : PartialOrder 
ι] [inst_3 : Order…
· 使用定理 `MeasureTheory.addContent_empty`：∀ {α : Type u_1} {C : Set (Set α)} {G : 
Type u_2} [inst : AddCommMonoid G] {m : MeasureTheory.AddContent G C}, m ∅ = 0
· 使用定理 `Pairwise.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {f : ι → α},   Pairwise (Function.onFun Disjoin
t f) → ∀ (s : S…
· 使用引理 `MeasureTheory.sum_addContent_le_of_subset`：sum_addContent_le_of_subset (
hC : IsSetSemiring C) (h_ss : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Set 
(Set α)) id) (ht : t in C) (hJt…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i

--- 原说明 ---
If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additiv
e.
-/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddContent ℝ≥0∞ C}
    (hC : IsSetSemiring C)
    -- TODO: `m_subadd` is in fact equivalent to `m.IsSigmaSubadditive`.
    (m_subadd : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : ⋃ i, f i ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine ENNReal.summable.tsum_le_of_sum_le fun I ↦ ?_
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ ↦ subset_iUnion _ i

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
/-
**MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive {m : AddConten
t Real>=0∞ C} (hC : IsSetSemiring C) (m_subadd : m.IsSigmaSubadditive) (f : Nat 
-> Set α) (hf : forall i, f i in C) (hf_Union : (⋃ i, f i) in C) (hf_disj : Pair
wise (Disjoint on f)) : m (⋃ i, f i) = ∑' i, m (f i)
参数：hC : IsSetSemiring C；m_subadd : m.IsSigmaSubadditive；f : Nat -> Set α；hf : fo
rall i, f i in C；hf_Union : (⋃ i, f i) in C；hf_disj : Pairwise (Disjoint on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion
_le`：addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddConte
nt Real>=0∞ C} (hC : IsSetSemiring C) -- TODO: `m_subadd` is in f…

--- 原说明 ---
If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additiv
e.
-/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive {m : AddContent ℝ≥0∞ C}
    (hC : IsSetSemiring C) (m_subadd : m.IsSigmaSubadditive)
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) :=
  addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le hC
    (fun _ hf hf_Union _ ↦ m_subadd hf hf_Union) f hf hf_Union hf_disj

end IsSetSemiring

section OnIoc

variable [LinearOrder α] {G : Type*} [AddCommGroup G]

open scoped Classical in
/-- The function associating to an interval `Ioc u v` the difference `f v - f u`.
Use instead `AddContent.ofIoc` which upgrades this function to an additive content. -/
/-
**MeasureTheory.AddContent.onIocAux** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Add
Content`。
形式化陈述：{α : Type u_1} → [LinearOrder α] → {G : Type u_3} → [AddCommGroup G] → (α 
→ G) → Set α → G
参数：α → G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function associating to an interval `Ioc u v` the difference `f v - f u`.
Use instead `AddContent.ofIoc` which upgrades this function to an additive conte
nt.
-/
noncomputable def AddContent.onIocAux (f : α → G) (s : Set α) : G :=
  if h : ∃ (p : α × α), p.1 ≤ p.2 ∧ s = Set.Ioc p.1 p.2
    then f h.choose.2 - f h.choose.1 else 0
/-
**MeasureTheory.AddContent.onIocAux_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AddContent`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {G : Type u_3} [inst_1 : AddCommGr
oup G] {f : α → G} {u v : α},   u ≤ v → MeasureTheory.AddContent.onIocAux f (Set
.Ioc u v) = f v - f u
参数：Set.Ioc u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Set.Ioc_eq_Ioc_iff`：Ioc_eq_Ioc_iff (hab : a < b ∨ c < d) : Ioc a b = Ioc
 c d ↔ a = c ∧ b = d
-/
lemma AddContent.onIocAux_apply {f : α → G} {u v : α} (h : u ≤ v) :
    AddContent.onIocAux f (Ioc u v) = f v - f u := by
  have h' : ∃ (p : α × α), p.1 ≤ p.2 ∧ Ioc u v = Ioc p.1 p.2 := ⟨(u, v), h, rfl⟩
  simp only [onIocAux, h', ↓reduceDIte]
  set u' := h'.choose.1
  set v' := h'.choose.2
  have hu'v' : u' ≤ v' ∧ Ioc u v = Ioc u' v' := h'.choose_spec
  rcases h.eq_or_lt with rfl | huv
  · grind [Set.Ioc_eq_empty_iff]
  rw [Ioc_eq_Ioc_iff (Or.inl huv)] at hu'v'
  grind
/-
**MeasureTheory.AddContent.onIocAux_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AddContent`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {G : Type u_3} [inst_1 : AddCommGr
oup G] (f : α → G),   MeasureTheory.AddContent.onIocAux f ∅ = 0
参数：f : α → G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AddContent.onIocAux.eq_1`：∀ {α : Type u_1} [inst : LinearO
rder α] {G : Type u_3} [inst_1 : AddCommGroup G] (f : α → G) (s : Set α),   Meas
ureTheory.AddContent.onIocAu…
· 使用定理 `dite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x :
 p → α} {y : α},   (if h : p then x h else y) = y ↔ ∀ (h : p), x h = y
-/
lemma AddContent.onIocAux_empty (f : α → G) :
    AddContent.onIocAux f ∅ = 0 := by
  classical
  rw [onIocAux, dite_eq_right_iff]
  grind [Set.Ioc_eq_empty_iff]

/-- The additive content on the set of open-closed intervals, associating to an interval `Ioc u v`
the difference `f v - f u`. -/
/-
**MeasureTheory.AddContent.onIoc** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AddCon
tent`。
形式化陈述：{α : Type u_1} →   [inst : LinearOrder α] →     {G : Type u_3} →       [in
st_1 : AddCommGroup G] → (α → G) → MeasureTheory.AddContent G {s | ∃ u v, u ≤ v 
∧ s = Set.Ioc u v}
参数：α → G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AddContent.onIocAux_empty`：∀ {α : Type u_1} [inst : Linear
Order α] {G : Type u_3} [inst_1 : AddCommGroup G] (f : α → G),   MeasureTheory.A
ddContent.onIocAux f ∅ = 0

--- 原说明 ---
The additive content on the set of open-closed intervals, associating to an inte
rval `Ioc u v`
the difference `f v - f u`.
-/
noncomputable def AddContent.onIoc (f : α → G) :
    AddContent G {s : Set α | ∃ u v, u ≤ v ∧ s = Set.Ioc u v} where
  toFun := AddContent.onIocAux f
  empty' := AddContent.onIocAux_empty f
  sUnion' := by
    /- Consider a finite union of open-closed intervals whose union is again an open-closed
    interval `(u, v]`. We have to show that the sum of `f b - f a` over the intervals gives
    `f v - f u`. Informally, `(u, v]` is an ordered
    union `(a₀, a₁] ∪ (a₁, a₂] ∪ ... ∪ (a_{n-1}, aₙ]` and there is a telescoping sum.
    For the formal argument, we argue by induction on the number of intervals, and remove the
    right-most one (i.e., the one that contains `v`) to reduce to one interval less. Denoting
    this right-most interval by `(u', v]`, then the union of the other intervals
    is exactly `(u, u']`. From this and the induction assumption, the conclusion follows. -/
    intro I hI h'I h''I
    induction hn : Finset.card I generalizing I with
    | zero =>
      have : I = ∅ := by grind
      simp [this, onIocAux_empty f]
    | succ n ih =>
      rcases h''I with ⟨u, v, huv, h'uv⟩
      -- If the interval `(u, v]` is empty, i.e., `u = v`, then the result is easy.
      rcases huv.eq_or_lt with rfl | huv
      · have : onIocAux f (Set.Ioc u u) = ∑ u ∈ I, 0 := by simp [onIocAux_empty f]
        rw [h'uv, this]
        apply Finset.sum_congr rfl fun i hi ↦ ?_
        have : i = ∅ := by grind [sUnion_eq_empty]
        grind [onIocAux_empty]
      -- otherwise, `v` is in `(u, v]`, therefore it belongs to some interval `(u', v']`
      -- featuring in the union.
      have : v ∈ ⋃₀ ↑I := by simp [h'uv, huv]
      obtain ⟨t, tI, ht⟩ : ∃ t ∈ I, v ∈ t := by simpa using this
      rcases hI tI with ⟨u', v', hu'v', rfl⟩
      -- we have `u ≤ u'` and `v' = v` since `(u', v']` is part of the union, and therefore
      -- contained in `(u, v]`.
      have ⟨_, uu'⟩ : v' ≤ v ∧ u ≤ u' := (Ioc_subset_Ioc_iff (by grind)).1 (by grind)
      obtain rfl : v = v' := by grind
      rw [h'uv, onIocAux_apply huv.le]
      -- let us remove the right-most interval `(u', v]` from the union, and let `I'` be the
      -- remaining set of intervals.
      let I' := I.erase (Set.Ioc u' v)
      have I'I : I' ⊆ I := erase_subset (Set.Ioc u' v) I
      have I_eq_insert : I = insert (Set.Ioc u' v) I' := by simp [I', tI]
      -- the intervals in `I'` cover exactly `(u, u']`.
      have UI' : ⋃₀ ↑I' = Ioc u u' := by
        have : (Ioc u' v ∪ ⋃₀ ↑I') \ Ioc u' v = ⋃₀ ↑I' := by
          refine Disjoint.sup_sdiff_cancel_left ?_
          simp only [coe_erase, disjoint_sUnion_right, Set.mem_sdiff, mem_singleton_iff, and_imp,
            I']
          intro u hu hu'
          exact (h'I hu tI hu').symm
        simp only [I_eq_insert, coe_insert, sUnion_insert] at h'uv
        grind
      -- by the inductive assumption, the sum over `I'` is exactly `f u' - f u`.
      have IH : onIocAux f (⋃₀ ↑I') = ∑ u ∈ I', onIocAux f u :=
        ih _ (Subset.trans I'I hI) (h'I.subset I'I) (by grind) (by grind)
      -- the conclusion follows.
      rw [I_eq_insert, sum_insert, ← IH, UI', onIocAux_apply hu'v', onIocAux_apply uu']
      · simp
      · simp [I']
/-
**MeasureTheory.AddContent.onIoc_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AddContent`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {G : Type u_3} [inst_1 : AddCommGr
oup G] {f : α → G} {u v : α},   u ≤ v → (MeasureTheory.AddContent.onIoc f) (Set.
Ioc u v) = f v - f u
参数：MeasureTheory.AddContent.onIoc f；Set.Ioc u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AddContent.onIocAux_apply`：∀ {α : Type u_1} [inst : Linear
Order α] {G : Type u_3} [inst_1 : AddCommGroup G] {f : α → G} {u v : α},   u ≤ v
 → MeasureTheory.AddContent.o…
-/
lemma AddContent.onIoc_apply {f : α → G} {u v : α} (h : u ≤ v) :
    AddContent.onIoc f (Ioc u v) = f v - f u :=
  AddContent.onIocAux_apply h

end OnIoc

section AddContentExtend

/-- An additive content obtained from another one on the same semiring of sets by setting the value
of each set not in the semiring at `∞`. -/
protected noncomputable
/-
**MeasureTheory.AddContent.extend** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AddCo
ntent`。
形式化陈述：{α : Type u_1} →   {C : Set (Set α)} →     MeasureTheory.IsSetSemiring C →
 MeasureTheory.AddContent ENNReal C → MeasureTheory.AddContent ENNReal C
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def AddContent.extend (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) : AddContent ℝ≥0∞ C where
  toFun := extend (fun x (_ : x ∈ C) ↦ m x)
  empty' := by rw [extend_eq, addContent_empty]; exact hC.empty_mem
  sUnion' I h_ss h_dis h_mem := by
    rw [extend_eq]
    swap; · exact h_mem
    rw [addContent_sUnion h_ss h_dis h_mem]
    refine Finset.sum_congr rfl (fun s hs ↦ ?_)
    rw [extend_eq]
    exact h_ss hs
/-
**MeasureTheory.AddContent.extend_eq_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AddContent`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} (hC : MeasureTheory.IsSetSemiring C) (m
 : MeasureTheory.AddContent ENNReal C),   ⇑(MeasureTheory.AddContent.extend hC m
) = MeasureTheory.extend fun x x_1 => m x
参数：Set α；hC : MeasureTheory.IsSetSemiring C；m : MeasureTheory.AddContent ENNReal
 C；MeasureTheory.AddContent.extend hC m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem AddContent.extend_eq_extend (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) :
    m.extend hC = extend (fun x (_ : x ∈ C) ↦ m x) := rfl
/-
**MeasureTheory.AddContent.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ad
dContent`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α} (hC : MeasureTheory.IsSetSe
miring C)   (m : MeasureTheory.AddContent ENNReal C), s ∈ C → (MeasureTheory.Add
Content.extend hC m) s = m s
参数：Set α；hC : MeasureTheory.IsSetSemiring C；m : MeasureTheory.AddContent ENNReal
 C；MeasureTheory.AddContent.extend hC m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AddContent.extend_eq_extend`：∀ {α : Type u_1} {C : Set (Se
t α)} (hC : MeasureTheory.IsSetSemiring C) (m : MeasureTheory.AddContent ENNReal
 C),   ⇑(MeasureTheory.AddConte…
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
-/
protected theorem AddContent.extend_eq (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) (hs : s ∈ C) :
    m.extend hC s = m s := by
  rwa [m.extend_eq_extend, extend_eq]
/-
**MeasureTheory.AddContent.extend_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AddContent`。
形式化陈述：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α} (hC : MeasureTheory.IsSetSe
miring C)   (m : MeasureTheory.AddContent ENNReal C), s ∉ C → (MeasureTheory.Add
Content.extend hC m) s = ⊤
参数：Set α；hC : MeasureTheory.IsSetSemiring C；m : MeasureTheory.AddContent ENNReal
 C；MeasureTheory.AddContent.extend hC m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AddContent.extend_eq_extend`：∀ {α : Type u_1} {C : Set (Se
t α)} (hC : MeasureTheory.IsSetSemiring C) (m : MeasureTheory.AddContent ENNReal
 C),   ⇑(MeasureTheory.AddConte…
· 使用定理 `MeasureTheory.extend_eq_top`：extend_eq_top {s : α} (h : ¬P s) : extend m
 s = ∞
-/
protected theorem AddContent.extend_eq_top
    (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) (hs : s ∉ C) :
    m.extend hC s = ∞ := by
  rwa [m.extend_eq_extend, extend_eq_top]

end AddContentExtend

section IsSetRing

/-
**MeasureTheory.addContent_union** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_union (hC : IsSetRing C) (hs : s in C) (ht : t in C) (h_dis : D
isjoint s t) : m (s union t) = m s + m t
参数：hC : IsSetRing C；hs : s in C；ht : t in C；h_dis : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.addContent_union'`：addContent_union' (hs : s in C) (ht : t
 in C) (hst : s union t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用定理 `MeasureTheory.IsSetRing.union_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s ∪ t ∈ C
-/
lemma addContent_union (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C)
    (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t :=
  addContent_union' hs ht (hC.union_mem hs ht) h_dis
/-
**MeasureTheory.addContent_biUnion_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_biUnion_eq {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α} {S :
 Finset ι} (hs : forall n in S, s n in C) (hS : (S : Set ι).PairwiseDisjoint s) 
: m (⋃ i in S, s i) = ∑ i in S, m (s i)
参数：hC : IsSetRing C；hs : forall n in S, s n in C；hS : (S : Set ι).PairwiseDisjoi
nt s。
该定理/引理给出了一组等式。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.addContent_empty`：∀ {α : Type u_1} {C : Set (Set α)} {G : 
Type u_2} [inst : AddCommMonoid G] {m : MeasureTheory.AddContent G C}, m ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.addContent_union`：addContent_union (hC : IsSetRing C) (hs 
: s in C) (ht : t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用引理 `MeasureTheory.IsSetRing.biUnion_mem`：biUnion_mem {ι : Type*} (hC : IsSet
Ring C) {s : ι -> Set α} (S : Finset ι) (hs : forall n in S, s n in C) : ⋃ i in 
S, s i in C
· 使用定理 `Set.disjoint_iUnion₂_right`：disjoint_iUnion₂_right {s : Set α} {t : fora
ll i, κ i -> Set α} : Disjoint s (⋃ (i) (j), t i j) ↔ forall i j, Disjoint s (t 
i j)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
lemma addContent_biUnion_eq {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    {S : Finset ι} (hs : ∀ n ∈ S, s n ∈ C) (hS : (S : Set ι).PairwiseDisjoint s) :
    m (⋃ i ∈ S, s i) = ∑ i ∈ S, m (s i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simp only [Finset.coe_insert, Set.pairwiseDisjoint_insert] at hS
    rw [← h hs.2 hS.1]
    refine addContent_union hC hs.1 (hC.biUnion_mem S hs.2) ?_
    rw [disjoint_iUnion₂_right]
    exact fun j hjS ↦ hS.2 j hjS (ne_of_mem_of_not_mem hjS hiS).symm
/-
**MeasureTheory.addContent_accumulate** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_accumulate (m : AddContent G C) (hC : IsSetRing C) {s : Nat -> 
Set α} (hs_disj : Pairwise (Disjoint on s)) (hsC : forall i, s i in C) (n : Nat)
 : m (Set.accumulate s n) = ∑ i in Finset.range (n + 1), m (s i)
参数：m : AddContent G C；hC : IsSetRing C；hs_disj : Pairwise (Disjoint on s)；hsC : 
forall i, s i in C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.accumulate_zero_nat`：accumulate_zero_nat (s : Nat -> Set β) : accumu
late s 0 = s 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.accumulate_succ`：accumulate_succ (u : Nat -> Set α) (n : Nat) : accu
mulate u (n + 1) = accumulate u n union u (n + 1)
· 使用引理 `MeasureTheory.addContent_union`：addContent_union (hC : IsSetRing C) (hs 
: s in C) (ht : t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用定理 `MeasureTheory.IsSetRing.accumulate_mem`：accumulate_mem (hC : IsSetRing C
) {s : Nat -> Set α} (hs : forall i, s i in C) (n : Nat) : accumulate s n in C
· 使用定理 `Set.disjoint_accumulate`：disjoint_accumulate [Preorder α] (hs : Pairwise
 (Disjoint on s)) {i j : α} (hij : i < j) : Disjoint (accumulate s i) (s j)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma addContent_accumulate (m : AddContent G C) (hC : IsSetRing C)
    {s : ℕ → Set α} (hs_disj : Pairwise (Disjoint on s)) (hsC : ∀ i, s i ∈ C) (n : ℕ) :
      m (Set.accumulate s n) = ∑ i ∈ Finset.range (n + 1), m (s i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, ← hn, Set.accumulate_succ, addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

/-- A function which is additive on disjoint elements in a ring of sets `C` defines an
additive content on `C`. -/
/-
**MeasureTheory.IsSetRing.addContent_of_union** 是 Mathlib 中的一个定义，位于命名空间 `Measure
Theory.IsSetRing`。
形式化陈述：{α : Type u_1} →   {C : Set (Set α)} →     {G : Type u_2} →       [inst : 
AddCommMonoid G] →         (m : Set α → G) →           MeasureTheory.IsSetRing C
 →             m ∅ = 0 →               (∀ {s t : Set α}, s ∈ C → t ∈ C → Disjoin
t s t → m (s ∪ t) = m s + m t) → MeasureTheory.AddContent G C
参数：Set α；m : Set α → G；∀ {s t : Set α}, s ∈ C → t ∈ C → Disjoint s t → m (s ∪ t)
 = m s + m t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function which is additive on disjoint elements in a ring of sets `C` defines 
an
additive content on `C`.
-/
def IsSetRing.addContent_of_union (m : Set α → G) (hC : IsSetRing C) (m_empty : m ∅ = 0)
    (m_add : ∀ {s t : Set α} (_hs : s ∈ C) (_ht : t ∈ C), Disjoint s t → m (s ∪ t) = m s + m t) :
    AddContent G C where
  toFun := m
  empty' := m_empty
  sUnion' I h_ss h_dis h_mem := by
    induction I using Finset.induction with
    | empty => simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
    | insert s I hsI h =>
      rw [Finset.coe_insert] at *
      rw [Set.insert_subset_iff] at h_ss
      rw [Set.pairwiseDisjoint_insert_of_notMem] at h_dis
      swap; · exact hsI
      have h_sUnion_mem : ⋃₀ ↑I ∈ C := by
        rw [Set.sUnion_eq_biUnion]
        apply hC.biUnion_mem
        intro n hn
        exact h_ss.2 hn
      rw [Set.sUnion_insert, m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2),
        Finset.sum_insert hsI, h h_ss.2 h_dis.1]
      rwa [Set.sUnion_insert] at h_mem

variable [PartialOrder G] [CanonicallyOrderedAdd G]
/-
**MeasureTheory.addContent_union_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_union_le (hC : IsSetRing C) (hs : s in C) (ht : t in C) : m (s 
union t) <= m s + m t
参数：hC : IsSetRing C；hs : s in C；ht : t in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用引理 `MeasureTheory.addContent_union`：addContent_union (hC : IsSetRing C) (hs 
: s in C) (ht : t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.inter_sdiff_self`：inter_sdiff_self (a b : Set α) : a inter (b \ a) =
 ∅
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用引理 `MeasureTheory.addContent_mono`：addContent_mono (hC : IsSetSemiring C) (h
s : s in C) (ht : t in C) (hst : s subseteq t) : m s <= m t
· 使用引理 `MeasureTheory.IsSetRing.isSetSemiring`：isSetSemiring (hC : IsSetRing C) 
: IsSetSemiring C where empty_mem
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma addContent_union_le (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m (s ∪ t) ≤ m s + m t := by
  rw [← union_sdiff_self, addContent_union hC hs (hC.sdiff_mem ht hs)]
  · exact add_le_add_right (addContent_mono hC.isSetSemiring (hC.sdiff_mem ht hs) ht sdiff_subset) _
  · rw [Set.disjoint_iff_inter_eq_empty, inter_sdiff_self]
/-
**MeasureTheory.addContent_biUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_biUnion_le {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α} {S :
 Finset ι} (hs : forall n in S, s n in C) : m (⋃ i in S, s i) <= ∑ i in S, m (s 
i)
参数：hC : IsSetRing C；hs : forall n in S, s n in C。
该定理/引理给出了一组等式。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.addContent_empty`：∀ {α : Type u_1} {C : Set (Set α)} {G : 
Type u_2} [inst : AddCommMonoid G] {m : MeasureTheory.AddContent G C}, m ∅ = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.addContent_union_le`：addContent_union_le (hC : IsSetRing C
) (hs : s in C) (ht : t in C) : m (s union t) <= m s + m t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MeasureTheory.IsSetRing.biUnion_mem`：biUnion_mem {ι : Type*} (hC : IsSet
Ring C) {s : ι -> Set α} (S : Finset ι) (hs : forall n in S, s n in C) : ⋃ i in 
S, s i in C
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma addContent_biUnion_le {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    {S : Finset ι} (hs : ∀ n ∈ S, s n ∈ C) :
    m (⋃ i ∈ S, s i) ≤ ∑ i ∈ S, m (s i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (addContent_union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)
/-
**MeasureTheory.le_addContent_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：le_addContent_sdiff (m : AddContent Real>=0∞ C) (hC : IsSetRing C) (hs : s
 in C) (ht : t in C) : m s - m t <= m (s \ t)
参数：m : AddContent Real>=0∞ C；hC : IsSetRing C；hs : s in C；ht : t in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用引理 `MeasureTheory.addContent_union`：addContent_union (hC : IsSetRing C) (hs 
: s in C) (ht : t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用引理 `MeasureTheory.IsSetRing.inter_mem`：inter_mem (hC : IsSetRing C) (hs : s 
in C) (ht : t in C) : s inter t in C
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
· 使用定理 `disjoint_inf_sdiff`：disjoint_inf_sdiff : Disjoint (x ⊓ y) (x \ y)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `add_tsub_le_assoc`：add_tsub_le_assoc : a + b - c <= a + (b - c)
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `MeasureTheory.addContent_mono`：addContent_mono (hC : IsSetSemiring C) (h
s : s in C) (ht : t in C) (hst : s subseteq t) : m s <= m t
· 使用引理 `MeasureTheory.IsSetRing.isSetSemiring`：isSetSemiring (hC : IsSetRing C) 
: IsSetSemiring C where empty_mem
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma le_addContent_sdiff (m : AddContent ℝ≥0∞ C) (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m s - m t ≤ m (s \ t) := by
  conv_lhs => rw [← inter_union_sdiff s t]
  rw [addContent_union hC (hC.inter_mem hs ht) (hC.sdiff_mem hs ht) disjoint_inf_sdiff, add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le
    (addContent_mono hC.isSetSemiring (hC.inter_mem hs ht) ht inter_subset_right), add_zero]

@[deprecated (since := "2026-06-03")] alias le_addContent_diff := le_addContent_sdiff
/-
**MeasureTheory.addContent_sdiff_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：addContent_sdiff_of_ne_top (m : AddContent Real>=0∞ C) (hC : IsSetRing C) 
(hm_ne_top : forall s in C, m s != ∞) {s t : Set α} (hs : s in C) (ht : t in C) 
(hts : t subseteq s) : m (s \ t) = m s - m t
参数：m : AddContent Real>=0∞ C；hC : IsSetRing C；hm_ne_top : forall s in C, m s != 
∞；hs : s in C；ht : t in C；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.addContent_union`：addContent_union (hC : IsSetRing C) (hs 
: s in C) (ht : t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `ENNReal.add_sub_cancel_left`：∀ {a b : ENNReal}, a ≠ ⊤ → a + b - a = b
-/
lemma addContent_sdiff_of_ne_top (m : AddContent ℝ≥0∞ C) (hC : IsSetRing C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    {s t : Set α} (hs : s ∈ C) (ht : t ∈ C) (hts : t ⊆ s) :
    m (s \ t) = m s - m t := by
  have h_union : m (t ∪ s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.sdiff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_sdiff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union, ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

@[deprecated (since := "2026-06-03")] alias addContent_diff_of_ne_top := addContent_sdiff_of_ne_top

/-- In a ring of sets, continuity of an additive content at `∅` implies σ-additivity.
This is not true in general in semirings, or without the hypothesis that `m` is finite. See the
examples 7 and 8 in Halmos' book Measure Theory (1974), page 40. -/
/-
**MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：addContent_iUnion_eq_sum_of_tendsto_zero (hC : IsSetRing C) (m : AddConten
t Real>=0∞ C) (hm_ne_top : forall s in C, m s != ∞) (hm_tendsto : forall ⦃s : Na
t -> Set α⦄ (_ : forall n, s n in C), Antitone s -> (⋂ n, s n) = ∅ -> Tendsto (f
un n => m (s n)) atTop (𝓝 0)) ⦃f : Nat -> Set α⦄ (hf : forall i, f i in C) (hUf 
: (⋃ i, f i) in C) (h_disj : Pairwise (Disjoint on f)) : m (⋃ i, f i) = ∑' i, m 
(f i)
参数：hC : IsSetRing C；m : AddContent Real>=0∞ C；hm_ne_top : forall s in C, m s != 
∞；hm_tendsto : forall ⦃s : Nat -> Set α⦄ (_ : forall n, s n in C), Antitone s ->
 (⋂ n, s n) = ∅ -> Tendsto (fun n => m (s n)) atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
· 使用定理 `MeasureTheory.IsSetRing.accumulate_mem`：accumulate_mem (hC : IsSetRing C
) {s : Nat -> Set α} (hs : forall i, s i in C) (n : Nat) : accumulate s n in C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
· 使用定理 `Set.iInter_inter_distrib`：iInter_inter_distrib (s : ι -> Set β) (t : ι -
> Set β) : ⋂ i, s i inter t i = (⋂ i, s i) inter ⋂ i, t i
· 使用引理 `Set.iInter_const`：iInter_const (s : Set β) : ⋂ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用引理 `MeasureTheory.addContent_sdiff_of_ne_top`：addContent_sdiff_of_ne_top (m 
: AddContent Real>=0∞ C) (hC : IsSetRing C) (hm_ne_top : forall s in C, m s != ∞
) {s t : Set α} (hs : s in C) …
· 使用定理 `Set.accumulate_subset_iUnion`：accumulate_subset_iUnion [LE α] (x : α) : 
accumulate s x subseteq ⋃ i, s i
· 使用引理 `MeasureTheory.addContent_accumulate`：addContent_accumulate (m : AddConte
nt G C) (hC : IsSetRing C) {s : Nat -> Set α} (hs_disj : Pairwise (Disjoint on s
)) (hsC : forall i, s i i…
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `ENNReal.tendsto_const_sub_nhds_zero_iff`：tendsto_const_sub_nhds_zero_iff
 {l : Filter α} {f : α -> Real>=0∞} {a : Real>=0∞} (ha : a != ∞) (hfa : forall n
, f n <= a) : Tendsto (fun n …
· 使用引理 `MeasureTheory.addContent_mono`：addContent_mono (hC : IsSetSemiring C) (h
s : s in C) (ht : t in C) (hst : s subseteq t) : m s <= m t
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `MeasureTheory.IsSetRing.isSetSemiring`：isSetSemiring (hC : IsSetRing C) 
: IsSetSemiring C where empty_mem
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
In a ring of sets, continuity of an additive content at `∅` implies σ-additivity
.
This is not true in general in semirings, or without the hypothesis that `m` is 
finite. See the
examples 7 and 8 in Halmos' book Measure Theory (1974), page 40.
-/
theorem addContent_iUnion_eq_sum_of_tendsto_zero (hC : IsSetRing C) (m : AddContent ℝ≥0∞ C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    (hm_tendsto : ∀ ⦃s : ℕ → Set α⦄ (_ : ∀ n, s n ∈ C),
      Antitone s → (⋂ n, s n) = ∅ → Tendsto (fun n ↦ m (s n)) atTop (𝓝 0))
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hUf : (⋃ i, f i) ∈ C)
    (h_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (Set.accumulate f n)`
  let s : ℕ → Set α := fun n ↦ (⋃ i, f i) \ Set.accumulate f n
  have hCs n : s n ∈ C := hC.sdiff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n ↦ m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_sdiff] at hxj ⊢
      exact ⟨hxj.1, fun hxi ↦ hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.sdiff_eq]
      rw [Set.iInter_inter_distrib, Set.iInter_const, ← Set.compl_iUnion, Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i ∈ Finset.range (n + 1), m (f i) := by
    rw [addContent_sdiff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _), addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum fun i ↦ m (f i))
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  rwa [ENNReal.tendsto_const_sub_nhds_zero_iff (hm_ne_top _ hUf) (fun n ↦ ?_)] at h_tendsto
  rw [← addContent_accumulate m hC h_disj hf]
  exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
    (Set.accumulate_subset_iUnion _)

/-- If an additive content is σ-additive on a set ring, then the content of a monotone sequence of
sets tends to the content of the union. -/
/-
**MeasureTheory.tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum {m : AddConte
nt Real>=0∞ C} (hC : IsSetRing C) (m_iUnion : forall (f : Nat -> Set α) (_ : for
all i, f i in C) (_ : (⋃ i, f i) in C) (_hf_disj : Pairwise (Disjoint on f)), m 
(⋃ i, f i) = ∑' i, m (f i)) ⦃f : Nat -> Set α⦄ (hf_mono : Monotone f) (hf : fora
ll i, f i in C) (hf_Union : ⋃ i, f i in C) : Tendsto (fun n => m (f n)) atTop (𝓝
 (m (⋃ i, f i)))
参数：hC : IsSetRing C；m_iUnion : forall (f : Nat -> Set α) (_ : forall i, f i in C
) (_ : (⋃ i, f i) in C) (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑'
 i, m (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用引理 `MeasureTheory.IsSetRing.disjointed_mem`：disjointed_mem {ι : Type*} [Preo
rder ι] [LocallyFiniteOrderBot ι] (hC : IsSetRing C) {s : ι -> Set α} (hs : fora
ll j, s j in C) (i : ι) : di…
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用引理 `MeasureTheory.addContent_accumulate`：addContent_accumulate (m : AddConte
nt G C) (hC : IsSetRing C) {s : Nat -> Set α} (hs_disj : Pairwise (Disjoint on s
)) (hsC : forall i, s i i…
· 使用定理 `Monotone.partialSups_eq`：Monotone.partialSups_eq {f : ι -> α} (hf : Mono
tone f) : partialSups f = f
· 使用定理 `partialSups_disjointed`：partialSups_disjointed (f : ι -> α) : partialSup
s (disjointed f) = partialSups f
· 使用定理 `partialSups_eq_biSup`：partialSups_eq_biSup (f : ι -> α) (i : ι) : partia
lSups f i = ⨆ j <= i, f j
· 使用定理 `Set.accumulate.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE α] (s : 
α → Set β) (x : α), Set.accumulate s x = ⋃ y, ⋃ (_ : y ≤ x), s y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `ENNReal.tendsto_nat_tsum`：tendsto_nat_tsum (f : Nat -> Real>=0∞) : Tends
to (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n))

--- 原说明 ---
If an additive content is σ-additive on a set ring, then the content of a monoto
ne sequence of
sets tends to the content of the union.
-/
theorem tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
    {m : AddContent ℝ≥0∞ C} (hC : IsSetRing C)
    (m_iUnion : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    ⦃f : ℕ → Set α⦄ (hf_mono : Monotone f) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C) :
    Tendsto (fun n ↦ m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  rw [← iUnion_disjointed, m_iUnion _ (hC.disjointed_mem hf) (by rwa [iUnion_disjointed])
      (disjoint_disjointed f)]
  have h n : m (f n) = ∑ i ∈ range (n + 1), m (disjointed f i) := by
    nth_rw 1 [← addContent_accumulate _ hC (disjoint_disjointed f) (hC.disjointed_mem hf),
    ← hf_mono.partialSups_eq, ← partialSups_disjointed, partialSups_eq_biSup, accumulate]
    rfl
  simp_rw [h]
  refine (tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i ∈ range k, m (disjointed f i))) 1).2 ?_
  exact ENNReal.tendsto_nat_tsum _

/-- If an additive content is σ-additive on a set ring, then it is σ-subadditive. -/
/-
**MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：isSigmaSubadditive_of_addContent_iUnion_eq_tsum {m : AddContent Real>=0∞ C
} (hC : IsSetRing C) (m_iUnion : forall (f : Nat -> Set α) (_ : forall i, f i in
 C) (_ : (⋃ i, f i) in C) (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = 
∑' i, m (f i)) : m.IsSigmaSubadditive
参数：hC : IsSetRing C；m_iUnion : forall (f : Nat -> Set α) (_ : forall i, f i in C
) (_ : (⋃ i, f i) in C) (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑'
 i, m (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iSup_eq_iUnion`：iSup_eq_iUnion (s : ι -> Set α) : iSup s = iUnion s
· 使用定理 `iSup_partialSups_eq`：iSup_partialSups_eq (f : ι -> α) : ⨆ i, partialSups
 f i = ⨆ i, f i
· 使用定理 `MeasureTheory.tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_ts
um`：tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum {m : AddContent
 Real>=0∞ C} (hC : IsSetRing C) (m_iUnion : forall (f : Nat -> S…
· 使用引理 `partialSups_monotone`：partialSups_monotone (f : ι -> α) : Monotone (part
ialSups f)
· 使用引理 `MeasureTheory.IsSetRing.partialSups_mem`：partialSups_mem {ι : Type*} [Pr
eorder ι] [LocallyFiniteOrderBot ι] (hC : IsSetRing C) {s : ι -> Set α} (hs : fo
rall n, s n in C) (n : ι) : p…
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `ENNReal.tendsto_nat_tsum`：tendsto_nat_tsum (f : Nat -> Real>=0∞) : Tends
to (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n))
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `partialSups_eq_biUnion_range`：partialSups_eq_biUnion_range (s : Nat -> S
et α) (n : Nat) : partialSups s n = ⋃ i in Finset.range (n + 1), s i
· 使用引理 `MeasureTheory.addContent_biUnion_le`：addContent_biUnion_le {ι : Type*} (
hC : IsSetRing C) {s : ι -> Set α} {S : Finset ι} (hs : forall n in S, s n in C)
 : m (⋃ i in S, s i) <= ∑…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
If an additive content is σ-additive on a set ring, then it is σ-subadditive.
-/
theorem isSigmaSubadditive_of_addContent_iUnion_eq_tsum {m : AddContent ℝ≥0∞ C} (hC : IsSetRing C)
    (m_iUnion : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i)) :
    m.IsSigmaSubadditive := by
  intro f hf hf_Union
  have h_tendsto : Tendsto (fun n ↦ m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion, ← iSup_partialSups_eq]
    refine tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum hC m_iUnion
      (partialSups_monotone f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' : Tendsto (fun n ↦ ∑ i ∈ range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i ∈ range k, m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun _ ↦ ?_
  rw [partialSups_eq_biUnion_range]
  exact addContent_biUnion_le hC (fun _ _ ↦ hf _)

/-- If an additive content is continuous from below on monotone sequences of sets,
then it is countably additive on pairwise disjoint sequences. -/
/-
**MeasureTheory.addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup (hC : IsSetRing C) 
(m : AddContent Real>=0∞ C) {s : Nat -> Set α} (hd : Pairwise (Disjoint on s)) (
hs : forall i, s i in C) (hm_iSup : forall ⦃s : Nat -> Set α⦄, (forall n, s n in
 C) -> Monotone s -> m (⋃ n, s n) = ⨆ n, m (s n)) : m (⋃ i, s i) = ∑' i, m (s i)
参数：hC : IsSetRing C；m : AddContent Real>=0∞ C；hd : Pairwise (Disjoint on s)；hs :
 forall i, s i in C；hm_iSup : forall ⦃s : Nat -> Set α⦄, (forall n, s n in C) ->
 Monotone s -> m (⋃ n, s n) = ⨆ n, m (s n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IsSetRing.accumulate_mem`：accumulate_mem (hC : IsSetRing C
) {s : Nat -> Set α} (hs : forall i, s i in C) (n : Nat) : accumulate s n in C
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用引理 `MeasureTheory.addContent_accumulate`：addContent_accumulate (m : AddConte
nt G C) (hC : IsSetRing C) {s : Nat -> Set α} (hs_disj : Pairwise (Disjoint on s
)) (hsC : forall i, s i i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_eq_iSup_nat'`：∀ {f : ℕ → ENNReal} {N : ℕ → ℕ},   Filter.Ten
dsto N Filter.atTop Filter.atTop → ∑' (i : ℕ), f i = ⨆ i, ∑ a ∈ Finset.range (N 
i), f a
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop

--- 原说明 ---
If an additive content is continuous from below on monotone sequences of sets,
then it is countably additive on pairwise disjoint sequences.
-/
theorem addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup
    (hC : IsSetRing C) (m : AddContent ℝ≥0∞ C)
    {s : ℕ → Set α} (hd : Pairwise (Disjoint on s)) (hs : ∀ i, s i ∈ C)
    (hm_iSup : ∀ ⦃s : ℕ → Set α⦄, (∀ n, s n ∈ C) → Monotone s → m (⋃ n, s n) = ⨆ n, m (s n)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  calc
    m (⋃ i, s i) = m (⋃ i, accumulate s i) := by simp
    _ = ⨆ i, m (accumulate s i) :=
      hm_iSup (fun n ↦ IsSetRing.accumulate_mem hC hs n) monotone_accumulate
    _ = ⨆ i, ∑ j ∈ range (i + 1), m (s j) :=
      iSup_congr fun i ↦ addContent_accumulate m hC hd hs i
    _ = ∑' i, m (s i) :=
      (ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)).symm

end IsSetRing

end MeasureTheory

