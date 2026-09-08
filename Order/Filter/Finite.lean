/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.Filter.Basic

/-!
# Results relating filters to finiteness

This file proves that finitely many conditions eventually hold if each of them eventually holds.
-/

public section

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

@[simp]
/-
**Filter.biInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：biInter_mem {β : Type v} {s : β -> Set α} {is : Set β} (hf : is.Finite) : 
(⋂ i in is, s i) in f ↔ forall i in is, s i in f
参数：hf : is.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
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
· 使用定理 `Set.iInter_iInter_eq_or_left`：iInter_iInter_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl
 rfl) inter ⋂ (x) …
-/
theorem biInter_mem {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f := by
  induction is, hf using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hs => simp [hs]

@[simp]
/-
**Filter.biInter_finset_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：biInter_finset_mem {β : Type v} {s : β -> Set α} (is : Finset β) : (⋂ i in
 is, s i) in f ↔ forall i in is, s i in f
参数：is : Finset β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem biInter_finset_mem {β : Type v} {s : β → Set α} (is : Finset β) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  biInter_mem is.finite_toSet

protected alias _root_.Finset.iInter_mem_sets := biInter_finset_mem

@[simp]
/-
**Filter.sInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s in f ↔ forall U in s
, U in f
参数：Set α；hfin : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s ∈ f ↔ ∀ U ∈ s, U ∈ f := by
  rw [sInter_eq_biInter, biInter_mem hfin]

@[simp]
/-
**Filter.iInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] : (⋂ i, s i) in f ↔ fo
rall i, s i in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.sInter_mem`：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s
 in f ↔ forall U in s, U in f
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem iInter_mem {β : Sort v} {s : β → Set α} [Finite β] : (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f :=
  (sInter_mem (finite_range _)).trans forall_mem_range

end Filter


namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section Lattice

variable {f g : Filter α} {s t : Set α}

/-
**Filter.mem_generate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_generate_iff {s : Set <| Set α} {U : Set α} : U in generate s ↔ exists
 t subseteq s, Set.Finite t ∧ ⋂₀ t subseteq U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.sInter_union`：sInter_union (S T : Set (Set α)) : ⋂₀ (S union T) = ⋂₀
 S inter ⋂₀ T
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.sInter_mem`：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s
 in f ↔ forall U in s, U in f
-/
theorem mem_generate_iff {s : Set <| Set α} {U : Set α} :
    U ∈ generate s ↔ ∃ t ⊆ s, Set.Finite t ∧ ⋂₀ t ⊆ U := by
  constructor <;> intro h
  · induction h with
    | @basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).subset⟩
    | univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    | superset _ hVW hV =>
      rcases hV with ⟨t, hts, ht, htV⟩
      exact ⟨t, hts, ht, htV.trans hVW⟩
    | inter _ _ hV hW =>
      rcases hV, hW with ⟨⟨t, hts, ht, htV⟩, u, hus, hu, huW⟩
      exact
        ⟨t ∪ u, union_subset hts hus, ht.union hu,
          (sInter_union _ _).subset.trans <| inter_subset_inter htV huW⟩
  · rcases h with ⟨t, hts, tfin, h⟩
    exact mem_of_superset ((sInter_mem tfin).2 fun V hV => GenerateSets.basic <| hts hV) h
/-
**Filter.mem_iInf_of_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U : Set α} {I : Set ι} (I_fin 
: I.Finite) {V : I -> Set α} (hV : forall (i : I), V i in s i) (hU : ⋂ i, V i su
bseteq U) : U in ⨅ i, s i
参数：I_fin : I.Finite；hV : forall (i : I), V i in s i；hU : ⋂ i, V i subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
-/
theorem mem_iInf_of_iInter {ι} {s : ι → Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite)
    {V : I → Set α} (hV : ∀ (i : I), V i ∈ s i) (hU : ⋂ i, V i ⊆ U) : U ∈ ⨅ i, s i := by
  have := I_fin.fintype
  refine mem_of_superset (iInter_mem.2 fun i => ?_) hU
  exact mem_iInf_of_mem (i : ι) (hV _)

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf {ι} {s : ι -> Filter α} {U : Set α} : (U in ⨅ i, s i) ↔ exists I 
: Set ι, I.Finite ∧ exists V : I -> Set α, (forall (i : I), V i in s i) ∧ U = ⋂ 
i, V i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.iInf_eq_generate`：iInf_eq_generate (s : ι -> Filter α) : iInf s =
 generate (⋃ i, (s i).sets)
· 使用定理 `Filter.mem_generate_iff`：mem_generate_iff {s : Set <| Set α} {U : Set α}
 : U in generate s ↔ exists t subseteq s, Set.Finite t ∧ ⋂₀ t subseteq U
· 使用定理 `Set.eq_finite_iUnion_of_finite_subset_iUnion`：eq_finite_iUnion_of_finite
_subset_iUnion {ι} {s : ι -> Set α} {t : Set α} (tfin : t.Finite) (h : t subsete
q ⋃ i, s i) : exists I : Set ι, I.…
· 使用定理 `Filter.sInter_mem`：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s
 in f ↔ forall U in s, U in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_iInter`：union_iInter (s : Set β) (t : ι -> Set β) : (s union ⋂
 i, t i) = ⋂ i, s union t i
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Set.sInter_iUnion`：sInter_iUnion (s : ι -> Set (Set α)) : ⋂₀ ⋃ i, s i = 
⋂ i, ⋂₀ s i
· 使用定理 `Filter.mem_iInf_of_iInter`：mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U
 : Set α} {I : Set ι} (I_fin : I.Finite) {V : I -> Set α} (hV : forall (i : I), 
V i in s i) (hU…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mem_iInf {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι, I.Finite ∧ ∃ V : I → Set α, (∀ (i : I), V i ∈ s i) ∧ U = ⋂ i, V i := by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U ∪ ⋂₀ σ i with hV
    have V_in : ∀ (i : I), V i ∈ s i := by
      rintro i
      have : ⋂₀ σ i ∈ s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this subset_union_right
    refine ⟨I, Ifin, V, V_in, ?_⟩
    rwa [hV, ← union_iInter, union_eq_self_of_subset_right]
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_iInf_of_iInter Ifin V_in Subset.rfl
/-
**Filter.mem_iInf'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf' {ι} {s : ι -> Filter α} {U : Set α} : (U in ⨅ i, s i) ↔ exists I
 : Set ι, I.Finite ∧ exists V : ι -> Set α, (forall i, V i in s i) ∧ (forall i ∉
 I, V i = univ) ∧ (U = ⋂ i in I, V i) ∧ U = ⋂ i, V i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iInter_dite`：iInter_dite (f : forall i, p i -> Set α) (g : forall i,
 ¬p i -> Set α) : ⋂ i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f 
i h) …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_iInf' {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι, I.Finite ∧ ∃ V : ι → Set α, (∀ i, V i ∈ s i) ∧
        (∀ i ∉ I, V i = univ) ∧ (U = ⋂ i ∈ I, V i) ∧ U = ⋂ i, V i := by
  classical
  simp only [mem_iInf, biInter_eq_iInter]
  refine ⟨?_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine ⟨I, If, fun i => if hi : i ∈ I then V ⟨i, hi⟩ else univ, fun i => ?_, fun i hi => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hV ⟨i,_⟩, univ_mem]
  · exact dif_neg hi
  · simp only [iInter_dite, biInter_eq_iInter, dif_pos (Subtype.coe_prop _), Subtype.coe_eta,
      iInter_univ, inter_univ, true_and]
/-
**Filter.exists_iInter_of_mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_iInter_of_mem_iInf {ι : Sort*} {α : Type*} {f : ι -> Filter α} {s} 
(hs : s in ⨅ i, f i) : exists t : ι -> Set α, (forall i, t i in f i) ∧ s = ⋂ i, 
t i
参数：hs : s in ⨅ i, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_iInf'`：mem_iInf' {ι} {s : ι -> Filter α} {U : Set α} : (U in 
⨅ i, s i) ↔ exists I : Set ι, I.Finite ∧ exists V : ι -> Set α, (forall i, V i i
n s i)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_range'`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : InfS
et α] (g : β → α) (f : ι → β), ⨅ b, g ↑b = ⨅ i, g (f i)
· 使用定理 `Function.Surjective.iInter_comp`：iInter_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋂ x, g (f x) = ⋂ y, g y
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem exists_iInter_of_mem_iInf {ι : Sort*} {α : Type*} {f : ι → Filter α} {s}
    (hs : s ∈ ⨅ i, f i) : ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i := by
  rw [← iInf_range' (g := (·))] at hs
  let ⟨_, _, V, hVs, _, _, hVU'⟩ := mem_iInf'.1 hs
  use V ∘ rangeFactorization f, fun i ↦ hVs (rangeFactorization f i)
  rw [hVU', ← rangeFactorization_surjective.iInter_comp, comp_def]
/-
**Filter.mem_iInf_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_of_finite {ι : Sort*} [Finite ι] {α : Type*} {f : ι -> Filter α} 
(s) : (s in ⨅ i, f i) ↔ exists t : ι -> Set α, (forall i, t i in f i) ∧ s = ⋂ i,
 t i
参数：s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_iInter_of_mem_iInf`：exists_iInter_of_mem_iInf {ι : Sort*} 
{α : Type*} {f : ι -> Filter α} {s} (hs : s in ⨅ i, f i) : exists t : ι -> Set α
, (forall i, t i in f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_iInf_of_finite {ι : Sort*} [Finite ι] {α : Type*} {f : ι → Filter α} (s) :
    (s ∈ ⨅ i, f i) ↔ ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i := by
  refine ⟨exists_iInter_of_mem_iInf, ?_⟩
  rintro ⟨t, ht, rfl⟩
  exact iInter_mem.2 fun i => mem_iInf_of_mem i (ht i)

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.mem_biInf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_biInf_principal {ι : Type*} {p : ι -> Prop} {s : ι -> Set α} {t : Set 
α} : t in ⨅ (i : ι) (_ : p i), 𝓟 (s i) ↔ exists I : Set ι, I.Finite ∧ (forall i 
in I, p i) ∧ ⋂ i in I, s i subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mem_iInf`：mem_iInf {ι} {s : ι -> Filter α} {U : Set α} : (U in ⨅ 
i, s i) ↔ exists I : Set ι, I.Finite ∧ exists V : I -> Set α, (forall (i : I), V
 i in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Set.iInter_mono''`：iInter_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iInter s subseteq iInter t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Filter.mem_iInf_of_iInter`：mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U
 : Set α} {I : Set ι} (I_fin : I.Finite) {V : I -> Set α} (hV : forall (i : I), 
V i in s i) (hU…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
-/
theorem mem_biInf_principal {ι : Type*} {p : ι → Prop} {s : ι → Set α} {t : Set α} :
    t ∈ ⨅ (i : ι) (_ : p i), 𝓟 (s i) ↔
      ∃ I : Set ι, I.Finite ∧ (∀ i ∈ I, p i) ∧ ⋂ i ∈ I, s i ⊆ t := by
  constructor
  · simp only [mem_iInf (ι := ι), mem_iInf_of_finite, mem_principal]
    rintro ⟨I, hIf, V, hV₁, hV₂, rfl⟩
    choose! t ht₁ ht₂ using hV₁
    refine ⟨I ∩ {i | p i}, hIf.inter_of_left _, fun i ↦ And.right, ?_⟩
    simp only [mem_inter_iff, iInter_and, biInter_eq_iInter, ht₂, mem_ofPred_eq]
    gcongr with i hpi
    exact ht₁ i hpi
  · rintro ⟨I, hIf, hpI, hst⟩
    rw [biInter_eq_iInter] at hst
    refine mem_iInf_of_iInter hIf (fun i ↦ ?_) hst
    simp [hpI i i.2]

/-! ### Lattice equations -/

/-
**Filter._root_.Pairwise.exists_mem_filter_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间
 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lattice equations
-/
theorem _root_.Pairwise.exists_mem_filter_of_disjoint {ι : Type*} [Finite ι] {l : ι → Filter α}
    (hd : Pairwise (Disjoint on l)) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ Pairwise (Disjoint on s) := by
  have : Pairwise fun i j => ∃ (s : {s // s ∈ l i}) (t : {t // t ∈ l j}), Disjoint s.1 t.1 := by
    simpa only [Pairwise, Function.onFun, Filter.disjoint_iff, exists_prop, Subtype.exists] using hd
  choose! s t hst using this
  refine ⟨fun i => ⋂ j, @s i j ∩ @t j i, fun i => ?_, fun i j hij => ?_⟩
  exacts [iInter_mem.2 fun j => inter_mem (@s i j).2 (@t j i).2,
    (hst hij).mono ((iInter_subset _ j).trans inter_subset_left)
      ((iInter_subset _ i).trans inter_subset_right)]
/-
**Filter._root_.Set.PairwiseDisjoint.exists_mem_filter** 是 Mathlib 中的一个定理，位于命名空间
 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.PairwiseDisjoint.exists_mem_filter {ι : Type*} {l : ι → Filter α} {t : Set ι}
    (hd : t.PairwiseDisjoint l) (ht : t.Finite) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ t.PairwiseDisjoint s := by
  have := ht.to_subtype
  rcases (hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
  lift s to (i : t) → {s // s ∈ l i} using hsl
  rcases @Subtype.exists_pi_extension ι (fun i => { s // s ∈ l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, hsd.set_of_subtype _ _⟩
/-
**Filter.iInf_sets_eq_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_sets_eq_finite {ι : Type*} (f : ι -> Filter α) : (⨅ i, f i).sets = ⋃ 
t : Finset ι, (⨅ i in t, f i).sets
参数：f : ι -> Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_eq_iInf_finset`：∀ {α : Type u_2} {ι : Type u_5} [inst : CompleteLat
tice α] (s : ι → α), ⨅ i, s i = ⨅ t, ⨅ i ∈ t, s i
· 使用定理 `Filter.iInf_sets_eq`：iInf_sets_eq {f : ι -> Filter α} (h : Directed (· >
= ·) f) [ne : Nonempty ι] : (iInf f).sets = ⋃ i, (f i).sets
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem iInf_sets_eq_finite {ι : Type*} (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i ∈ t, f i).sets := by
  rw [iInf_eq_iInf_finset, iInf_sets_eq]
  exact directed_of_isDirected_le fun _ _ => biInf_mono
/-
**Filter.iInf_sets_eq_finite'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_sets_eq_finite' (f : ι -> Filter α) : (⨅ i, f i).sets = ⋃ t : Finset 
(PLift ι), (⨅ i in t, f (PLift.down i)).sets
参数：f : ι -> Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.iInf_sets_eq_finite`：iInf_sets_eq_finite {ι : Type*} (f : ι -> Fi
lter α) : (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i in t, f i).sets
· 使用定理 `Function.Surjective.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sor
t u_5} [inst : InfSet α] {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α),
 ⨅ x, g (f x) = ⨅ y…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.plift_apply`：∀ {α : Sort u}, ⇑Equiv.plift = PLift.down
-/
theorem iInf_sets_eq_finite' (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset (PLift ι), (⨅ i ∈ t, f (PLift.down i)).sets := by
  rw [← iInf_sets_eq_finite, ← Equiv.plift.surjective.iInf_comp, Equiv.plift_apply]
/-
**Filter.mem_iInf_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_finite {ι : Type*} {f : ι -> Filter α} (s) : s in iInf f ↔ exists
 t : Finset ι, s in ⨅ i in t, f i
参数：s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Filter.iInf_sets_eq_finite`：iInf_sets_eq_finite {ι : Type*} (f : ι -> Fi
lter α) : (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i in t, f i).sets
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem mem_iInf_finite {ι : Type*} {f : ι → Filter α} (s) :
    s ∈ iInf f ↔ ∃ t : Finset ι, s ∈ ⨅ i ∈ t, f i :=
  (Set.ext_iff.1 (iInf_sets_eq_finite f) s).trans mem_iUnion
/-
**Filter.mem_iInf_finite'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_finite' {f : ι -> Filter α} (s) : s in iInf f ↔ exists t : Finset
 (PLift ι), s in ⨅ i in t, f (PLift.down i)
参数：s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Filter.iInf_sets_eq_finite'`：iInf_sets_eq_finite' (f : ι -> Filter α) : 
(⨅ i, f i).sets = ⋃ t : Finset (PLift ι), (⨅ i in t, f (PLift.down i)).sets
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem mem_iInf_finite' {f : ι → Filter α} (s) :
    s ∈ iInf f ↔ ∃ t : Finset (PLift ι), s ∈ ⨅ i ∈ t, f (PLift.down i) :=
  (Set.ext_iff.1 (iInf_sets_eq_finite' f) s).trans mem_iUnion
/-
**Filter.mem_iInf_finset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iInf_finset {s : Finset α} {f : α -> Filter β} {t : Set β} : (t in ⨅ a
 in s, f a) ↔ exists p : α -> Set β, (forall a in s, p a in f a) ∧ t = ⋂ a in s,
 p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_iInf_of_finite`：mem_iInf_of_finite {ι : Sort*} [Finite ι] {α 
: Type*} {f : ι -> Filter α} (s) : (s in ⨅ i, f i) ↔ exists t : ι -> Set α, (for
all i, t i in f…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Set.iInter_congr_of_surjective`：iInter_congr_of_surjective {f : ι -> Set
 α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h) (h2 : forall x, g (h x) 
= f x) : ⋂ x, f x = …
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mem_iInf_finset {s : Finset α} {f : α → Filter β} {t : Set β} :
    (t ∈ ⨅ a ∈ s, f a) ↔ ∃ p : α → Set β, (∀ a ∈ s, p a ∈ f a) ∧ t = ⋂ a ∈ s, p a := by
  classical
  simp only [← Finset.set_biInter_coe, biInter_eq_iInter, iInf_subtype']
  refine ⟨fun h => ?_, ?_⟩
  · rcases (mem_iInf_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine ⟨fun a => if h : a ∈ s then p ⟨a, h⟩ else univ,
            fun a ha => by simpa [ha] using hp ⟨a, ha⟩, ?_⟩
    refine iInter_congr_of_surjective id surjective_id ?_
    rintro ⟨a, ha⟩
    simp [ha]
  · rintro ⟨p, hpf, rfl⟩
    exact iInter_mem.2 fun a => mem_iInf_of_mem a (hpf a a.2)

/-! #### `principal` equations -/

@[simp]
/-
**Filter.iInf_principal_finset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_principal_finset {ι : Type w} (s : Finset ι) (f : ι -> Set α) : ⨅ i i
n s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
参数：s : Finset ι；f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.iInf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] [inst_1 : DecidableEq α] (a : α) (s : Finset α) (t : α → β),   ⨅ x ∈ inse
rt a s, …
· 使用定理 `Finset.set_biInter_insert`：set_biInter_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)

--- 原说明 ---
#### `principal` equations
-/
theorem iInf_principal_finset {ι : Type w} (s : Finset ι) (f : ι → Set α) :
    ⨅ i ∈ s, 𝓟 (f i) = 𝓟 (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs => rw [Finset.iInf_insert, Finset.set_biInter_insert, hs, inf_principal]
/-
**Filter.iInf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_principal {ι : Sort w} [Finite ι] (f : ι -> Set α) : ⨅ i, 𝓟 (f i) = 𝓟
 (⋂ i, f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_plift_down`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] (f : 
ι → α), ⨅ i, f i.down = ⨅ i, f i
· 使用定理 `Set.iInter_plift_down`：iInter_plift_down (f : ι -> Set α) : ⋂ i, f (PLif
t.down i) = ⋂ i, f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `Filter.iInf_principal_finset`：iInf_principal_finset {ι : Type w} (s : Fi
nset ι) (f : ι -> Set α) : ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
-/
theorem iInf_principal {ι : Sort w} [Finite ι] (f : ι → Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iInf_plift_down, ← iInter_plift_down]
  simpa using iInf_principal_finset Finset.univ (f <| PLift.down ·)

/-- A special case of `iInf_principal` that is safe to mark `simp`. -/
@[simp]
/-
**Filter.iInf_principal'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_principal' {ι : Type w} [Finite ι] (f : ι -> Set α) : ⨅ i, 𝓟 (f i) = 
𝓟 (⋂ i, f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.iInf_principal`：iInf_principal {ι : Sort w} [Finite ι] (f : ι -> 
Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i)

--- 原说明 ---
A special case of `iInf_principal` that is safe to mark `simp`.
-/
theorem iInf_principal' {ι : Type w} [Finite ι] (f : ι → Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) :=
  iInf_principal _
/-
**Filter.iInf_principal_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι -> S
et α) : ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
参数：hs : s.Finite；f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Filter.iInf_principal_finset`：iInf_principal_finset {ι : Type w} (s : Fi
nset ι) (f : ι -> Set α) : ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
-/
theorem iInf_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι → Set α) :
    ⨅ i ∈ s, 𝓟 (f i) = 𝓟 (⋂ i ∈ s, f i) := by
  lift s to Finset ι using hs
  exact mod_cast iInf_principal_finset s f

/-- If a filter has finitely many sets, then it is principal. -/
/-
**Filter.eq_principal_of_finite_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_principal_of_finite_sets (hf : f.sets.Finite) : exists s, f = 𝓟 s
参数：hf : f.sets.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.sInter_mem`：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s
 in f ↔ forall U in s, U in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If a filter has finitely many sets, then it is principal.
-/
theorem eq_principal_of_finite_sets (hf : f.sets.Finite) : ∃ s, f = 𝓟 s := by
  use ⋂₀ f.sets
  exact Filter.ext fun B ↦ ⟨sInter_subset_of_mem, mem_of_superset ((sInter_mem hf).2 (by simp))⟩

/-- Any filter on a finite type is principal. -/
/-
**Filter.eq_principal_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eq_principal_of_finite [Finite α] (f : Filter α) : exists s, f = 𝓟 s
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_principal_of_finite_sets`：eq_principal_of_finite_sets (hf : f.
sets.Finite) : exists s, f = 𝓟 s
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.powerset`：∀ {α : Type u} {s : Set α}, s.Finite → (𝒫 s).Finite
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.powerset_univ`：powerset_univ : 𝒫 (univ : Set α) = univ

--- 原说明 ---
Any filter on a finite type is principal.
-/
theorem eq_principal_of_finite [Finite α] (f : Filter α) : ∃ s, f = 𝓟 s :=
  eq_principal_of_finite_sets (finite_univ.powerset.subset (by simp))
/-
**Filter.principal_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_surjective [Finite α] : Surjective (𝓟 : Set α -> Filter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eq_principal_of_finite`：eq_principal_of_finite [Finite α] (f : Fi
lter α) : exists s, f = 𝓟 s
-/
theorem principal_surjective [Finite α] : Surjective (𝓟 : Set α → Filter α) :=
  fun f ↦ (eq_principal_of_finite f).imp fun _ ↦ .symm

end Lattice

/-! ### Eventually and Frequently -/

@[simp]
/-
**Filter.eventually_all** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι -> α -> Prop} : (forallᶠ 
x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f

--- 原说明 ---
### Eventually and Frequently
-/
theorem eventually_all {ι : Sort*} [Finite ι] {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, ofPred_forall] using iInter_mem

@[simp]
/-
**Filter.eventually_all_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι -> α -> P
rop} : (forallᶠ x in l, forall i in I, p i x) ↔ forall i in I, forallᶠ x in l, p
 i x
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
-/
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, ofPred_forall] using biInter_mem hI

protected alias _root_.Set.Finite.eventually_all := eventually_all_finite
/-
**Filter.eventually_all_finset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {ι : Type u_2} (I : Finset ι) {l : Filter α} {p : ι → α → P
rop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ (x : α) in l, p i x
参数：I : Finset ι；∀ᶠ (x : α) in l, ∀ i ∈ I, p i x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
@[simp] theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x :=
  I.finite_toSet.eventually_all

protected alias _root_.Finset.eventually_all := eventually_all_finset

@[simp]
/-
**Filter.frequently_exists** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_exists {ι : Sort*} [Finite ι] {l} {p : ι -> α -> Prop} : (exist
sᶠ x in l, exists i, p i x) ↔ exists i, existsᶠ x in l, p i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_exists {ι : Sort*} [Finite ι] {l} {p : ι → α → Prop} :
    (∃ᶠ x in l, ∃ i, p i x) ↔ ∃ i, ∃ᶠ x in l, p i x := by
  rw [← not_iff_not]
  simp

@[simp]
/-
**Filter.frequently_exists_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_exists_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι -> α -
> Prop} : (existsᶠ x in l, exists i in I, p i x) ↔ exists i in I, existsᶠ x in l
, p i x
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_exists_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∃ᶠ x in l, ∃ i ∈ I, p i x) ↔ ∃ i ∈ I, ∃ᶠ x in l, p i x := by
  rw [← not_iff_not]
  simp [hI]

protected alias _root_.Set.Finite.frequently_exists := frequently_exists_finite
/-
**Filter.frequently_exists_finset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {ι : Type u_2} (I : Finset ι) {l : Filter α} {p : ι → α → P
rop},   (∃ᶠ (x : α) in l, ∃ i ∈ I, p i x) ↔ ∃ i ∈ I, ∃ᶠ (x : α) in l, p i x
参数：I : Finset ι；∃ᶠ (x : α) in l, ∃ i ∈ I, p i x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.frequently_exists`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},
   I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∃ᶠ (x : α) in l, ∃ i ∈ I, p 
i x) ↔ ∃ i ∈ I, ∃ᶠ…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
@[simp] theorem frequently_exists_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∃ᶠ x in l, ∃ i ∈ I, p i x) ↔ ∃ i ∈ I, ∃ᶠ x in l, p i x :=
  I.finite_toSet.frequently_exists

protected alias _root_.Finset.frequently_exists := frequently_exists_finset
/-
**Filter.eventually_subset_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventually_subset_of_finite {ι : Type*} {f : Filter ι} {s : ι -> Set α} {t
 : Set α} (ht : t.Finite) (hs : forall a in t, forallᶠ i in f, a in s i) : foral
lᶠ i in f, t subseteq s i
参数：ht : t.Finite；hs : forall a in t, forallᶠ i in f, a in s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_all_finite`：eventually_all_finite {ι} {I : Set ι} (hI 
: I.Finite) {l} {p : ι -> α -> Prop} : (forallᶠ x in l, forall i in I, p i x) ↔ 
forall i in I, for…
-/
lemma eventually_subset_of_finite {ι : Type*} {f : Filter ι} {s : ι → Set α} {t : Set α}
    (ht : t.Finite) (hs : ∀ a ∈ t, ∀ᶠ i in f, a ∈ s i) : ∀ᶠ i in f, t ⊆ s i := by
  simpa [Set.subset_def, eventually_all_finite ht] using hs

/-!
### Relation “eventually equal”
-/

section EventuallyEq
variable {l : Filter α} {f g : α → β}

variable {l : Filter α}

/-
**Filter.EventuallyLE.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {ι : Sort x} {l : Filter α} [Finite ι] {s t : ι → Set α},  
 (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋃ i, s i ≤ᶠ[l] ⋃ i, t i
参数：∀ (i : ι), s i ≤ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
protected lemma EventuallyLE.iUnion [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i ≤ᶠ[l] t i) : (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' ↦
    let ⟨i, hi⟩ := mem_iUnion.1 hx'; mem_iUnion.2 ⟨i, hx i hi⟩
/-
**Filter.EventuallyEq.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {ι : Sort x} {l : Filter α} [Finite ι] {s t : ι → Set α},  
 (∀ (i : ι), s i =ᶠ[l] t i) → ⋃ i, s i =ᶠ[l] ⋃ i, t i
参数：∀ (i : ι), s i =ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.iUnion`：∀ {α : Type u} {ι : Sort x} {l : Filter α} [
Finite ι] {s t : ι → Set α},   (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋃ i, s i ≤ᶠ[l] ⋃ i, 
t i
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
protected lemma EventuallyEq.iUnion [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i =ᶠ[l] t i) : (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.iUnion fun i ↦ (h i).le).antisymm <| .iUnion fun i ↦ (h i).symm.le
/-
**Filter.EventuallyLE.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u} {ι : Sort x} {l : Filter α} [Finite ι] {s t : ι → Set α},  
 (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋂ i, s i ≤ᶠ[l] ⋂ i, t i
参数：∀ (i : ι), s i ≤ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
protected lemma EventuallyLE.iInter [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i ≤ᶠ[l] t i) : (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' ↦ mem_iInter.2 fun i ↦ hx i (mem_iInter.1 hx' i)
/-
**Filter.EventuallyEq.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u} {ι : Sort x} {l : Filter α} [Finite ι] {s t : ι → Set α},  
 (∀ (i : ι), s i =ᶠ[l] t i) → ⋂ i, s i =ᶠ[l] ⋂ i, t i
参数：∀ (i : ι), s i =ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.iInter`：∀ {α : Type u} {ι : Sort x} {l : Filter α} [
Finite ι] {s t : ι → Set α},   (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋂ i, s i ≤ᶠ[l] ⋂ i, 
t i
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
protected lemma EventuallyEq.iInter [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i =ᶠ[l] t i) : (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.iInter fun i ↦ (h i).le).antisymm <| .iInter fun i ↦ (h i).symm.le
/-
**Filter._root_.Set.Finite.eventuallyLE_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Filter
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.eventuallyLE_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋃ i ∈ s, f i) ≤ᶠ[l] (⋃ i ∈ s, g i) := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion, biUnion_eq_iUnion]
  exact .iUnion fun i ↦ hle i.1 i.2

alias EventuallyLE.biUnion := Set.Finite.eventuallyLE_iUnion
/-
**Filter._root_.Set.Finite.eventuallyEq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Filter
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.eventuallyEq_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋃ i ∈ s, f i) =ᶠ[l] (⋃ i ∈ s, g i) :=
  (EventuallyLE.biUnion hs fun i hi ↦ (heq i hi).le).antisymm <|
    .biUnion hs fun i hi ↦ (heq i hi).symm.le

alias EventuallyEq.biUnion := Set.Finite.eventuallyEq_iUnion
/-
**Filter._root_.Set.Finite.eventuallyLE_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Filter
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.eventuallyLE_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋂ i ∈ s, f i) ≤ᶠ[l] (⋂ i ∈ s, g i) := by
  have := hs.to_subtype
  rw [biInter_eq_iInter, biInter_eq_iInter]
  exact .iInter fun i ↦ hle i.1 i.2

alias EventuallyLE.biInter := Set.Finite.eventuallyLE_iInter
/-
**Filter._root_.Set.Finite.eventuallyEq_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Filter
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.eventuallyEq_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋂ i ∈ s, f i) =ᶠ[l] (⋂ i ∈ s, g i) :=
  (EventuallyLE.biInter hs fun i hi ↦ (heq i hi).le).antisymm <|
    .biInter hs fun i hi ↦ (heq i hi).symm.le

alias EventuallyEq.biInter := Set.Finite.eventuallyEq_iInter
/-
**Filter._root_.Finset.eventuallyLE_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.eventuallyLE_iUnion {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋃ i ∈ s, f i) ≤ᶠ[l] (⋃ i ∈ s, g i) :=
  .biUnion s.finite_toSet hle
/-
**Filter._root_.Finset.eventuallyEq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.eventuallyEq_iUnion {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋃ i ∈ s, f i) =ᶠ[l] (⋃ i ∈ s, g i) :=
  .biUnion s.finite_toSet heq
/-
**Filter._root_.Finset.eventuallyLE_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.eventuallyLE_iInter {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋂ i ∈ s, f i) ≤ᶠ[l] (⋂ i ∈ s, g i) :=
  .biInter s.finite_toSet hle
/-
**Filter._root_.Finset.eventuallyEq_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.eventuallyEq_iInter {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋂ i ∈ s, f i) =ᶠ[l] (⋂ i ∈ s, g i) :=
  .biInter s.finite_toSet heq

end EventuallyEq

end Filter

