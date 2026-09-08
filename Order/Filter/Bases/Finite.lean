/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Finiteness results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection.
-/

@[expose] public section

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

namespace Filter

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

/-
**Filter.hasBasis_generate** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_generate (s : Set (Set α)) : (generate s).HasBasis (fun t => Set.
Finite t ∧ t subseteq s) fun t => ⋂₀ t
参数：s : Set (Set α)。
该定理/引理给出了一组等式。
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
theorem hasBasis_generate (s : Set (Set α)) :
    (generate s).HasBasis (fun t => Set.Finite t ∧ t ⊆ s) fun t => ⋂₀ t :=
  ⟨fun U => by simp only [mem_generate_iff, and_assoc, and_left_comm]⟩

/-- The smallest filter basis containing a given collection of sets. -/
/-
**Filter.FilterBasis.ofSets** 是 Mathlib 中的一个定义，位于命名空间 `Filter.FilterBasis`。
形式化陈述：{α : Type u_1} → Set (Set α) → FilterBasis α
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest filter basis containing a given collection of sets.
-/
def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α where
  sets := sInter '' { t | Set.Finite t ∧ t ⊆ s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInter_union _ _).subset⟩
/-
**Filter.FilterBasis.ofSets_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.FilterBasis`。
形式化陈述：∀ {α : Type u_1} (s : Set (Set α)), (Filter.FilterBasis.ofSets s).sets = S
et.sInter '' {t | t.Finite ∧ t ⊆ s}
参数：s : Set (Set α)；Filter.FilterBasis.ofSets s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FilterBasis.ofSets_sets (s : Set (Set α)) :
    (FilterBasis.ofSets s).sets = sInter '' { t | Set.Finite t ∧ t ⊆ s } :=
  rfl
/-
**Filter.generate_eq_generate_inter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_eq_generate_inter (s : Set (Set α)) : generate s = generate (sInt
er '' { t | Set.Finite t ∧ t subseteq s })
参数：s : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.FilterBasis.ofSets_sets`：∀ {α : Type u_1} (s : Set (Set α)), (Fil
ter.FilterBasis.ofSets s).sets = Set.sInter '' {t | t.Finite ∧ t ⊆ s}
· 使用定理 `FilterBasis.generate`：∀ {α : Type u_1} (B : FilterBasis α), Filter.gener
ate B.sets = B.filter
· 使用定理 `Filter.HasBasis.isBasis`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → Filter.IsBasis p s
· 使用定理 `Filter.hasBasis_generate`：hasBasis_generate (s : Set (Set α)) : (generat
e s).HasBasis (fun t => Set.Finite t ∧ t subseteq s) fun t => ⋂₀ t
· 使用定理 `Filter.HasBasis.filter_eq`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α} (h : l.HasBasis p s), ⋯.filter = l
-/
theorem generate_eq_generate_inter (s : Set (Set α)) :
    generate s = generate (sInter '' { t | Set.Finite t ∧ t ⊆ s }) := by
  rw [← FilterBasis.ofSets_sets, FilterBasis.generate, ← (hasBasis_generate s).filter_eq]; rfl
/-
**Filter.ofSets_filter_eq_generate** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ofSets_filter_eq_generate (s : Set (Set α)) : (FilterBasis.ofSets s).filte
r = generate s
参数：s : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FilterBasis.generate`：∀ {α : Type u_1} (B : FilterBasis α), Filter.gener
ate B.sets = B.filter
· 使用定理 `Filter.FilterBasis.ofSets_sets`：∀ {α : Type u_1} (s : Set (Set α)), (Fil
ter.FilterBasis.ofSets s).sets = Set.sInter '' {t | t.Finite ∧ t ⊆ s}
· 使用定理 `Filter.generate_eq_generate_inter`：generate_eq_generate_inter (s : Set (
Set α)) : generate s = generate (sInter '' { t | Set.Finite t ∧ t subseteq s })
-/
theorem ofSets_filter_eq_generate (s : Set (Set α)) :
    (FilterBasis.ofSets s).filter = generate s := by
  rw [← (FilterBasis.ofSets s).generate, FilterBasis.ofSets_sets, ← generate_eq_generate_inter]
/-
**Filter.generate_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：generate_neBot_iff {s : Set (Set α)} : NeBot (generate s) ↔ forall t, t su
bseteq s -> t.Finite -> (⋂₀ t).Nonempty
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `Filter.hasBasis_generate`：hasBasis_generate (s : Set (Set α)) : (generat
e s).HasBasis (fun t => Set.Finite t ∧ t subseteq s) fun t => ⋂₀ t
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
theorem generate_neBot_iff {s : Set (Set α)} :
    NeBot (generate s) ↔ ∀ t, t ⊆ s → t.Finite → (⋂₀ t).Nonempty :=
  (hasBasis_generate s).neBot_iff.trans <| by simp only [← and_imp, and_comm]
/-
**Filter.HasBasis.iInf'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_6} {ι' : ι → Type u_7} {l : ι → Filter α} {p 
: (i : ι) → ι' i → Prop}   {s : (i : ι) → ι' i → Set α},   (∀ (i : ι), (l i).Has
Basis (p i) (s i)) →     (⨅ i, l i).HasBasis (fun If => If.1.Finite ∧ ∀ i ∈ If.1
, p i (If.2 i)) fun If => ⋂ i ∈ If.1, s i (If.2 i)
参数：i : ι；i : ι；∀ (i : ι), (l i).HasBasis (p i) (s i)；⨅ i, l i；fun If => If.1.Fin
ite ∧ ∀ i ∈ If.1, p i (If.2 i)；If.2 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
protected theorem HasBasis.iInf' {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α}
    {p : ∀ i, ι' i → Prop} {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => ⋂ i ∈ If.1, s i (If.2 i) :=
  ⟨by
    intro t
    constructor
    · simp only [mem_iInf', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, iInter₂_mono fun i _ => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      grw [← hsub]
      exact (biInter_mem hI₁).mpr fun i hi => mem_iInf_of_mem i <| (hl i).mem_of_mem <| hI₂ _ hi⟩
/-
**Filter.HasBasis.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_6} {ι' : ι → Type u_7} {l : ι → Filter α} {p 
: (i : ι) → ι' i → Prop}   {s : (i : ι) → ι' i → Set α},   (∀ (i : ι), (l i).Has
Basis (p i) (s i)) →     (⨅ i, l i).HasBasis (fun If => If.fst.Finite ∧ ∀ (i : ↑
If.fst), p (↑i) (If.snd i)) fun If => ⋂ i, s (↑i) (If.snd i)
参数：i : ι；i : ι；∀ (i : ι), (l i).HasBasis (p i) (s i)；⨅ i, l i；fun If => If.fst.F
inite ∧ ∀ (i : ↑If.fst), p (↑i) (If.snd i)；↑i；If.snd i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.iInf'`：∀ {α : Type u_1} {ι : Type u_6} {ι' : ι → Type u_
7} {l : ι → Filter α} {p : (i : ι) → ι' i → Prop}   {s : (i : ι) → ι' i → Set α}
,   (∀ (i :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Set.Finite.nonempty_fintype`：∀ {α : Type u} {s : Set α}, s.Finite → None
mpty (Fintype ↑s)
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
protected theorem HasBasis.iInf {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α}
    {p : ∀ i, ι' i → Prop} {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis
      (fun If : Σ I : Set ι, ∀ i : I, ι' i => If.1.Finite ∧ ∀ i : If.1, p i (If.2 i)) fun If =>
      ⋂ i : If.1, s i (If.2 i) := by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · rcases (HasBasis.iInf' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact ⟨⟨I, fun i => f i⟩, ⟨hI, Subtype.forall.mpr hf⟩, trans (iInter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    grw [← hsub]
    cases hI.nonempty_fintype
    exact iInter_mem.2 fun i => mem_iInf_of_mem ↑i <| (hl i).mem_of_mem <| hf _

open scoped Function in -- required for scoped `on` notation
/-
**Filter._root_.Pairwise.exists_mem_filter_basis_of_disjoint** 是 Mathlib 中的一个定理，
位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pairwise.exists_mem_filter_basis_of_disjoint {I} [Finite I] {l : I → Filter α}
    {ι : I → Sort*} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} (hd : Pairwise (Disjoint on l))
    (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ Pairwise (Disjoint on fun i => s i (ind i)) := by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩
/-
**Filter._root_.Set.PairwiseDisjoint.exists_mem_filter_basis** 是 Mathlib 中的一个定理，
位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.PairwiseDisjoint.exists_mem_filter_basis {I : Type*} {l : I → Filter α}
    {ι : I → Sort*} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} {S : Set I}
    (hd : S.PairwiseDisjoint l) (hS : S.Finite) (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ S.PairwiseDisjoint fun i => s i (ind i) := by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩

/-- If `s : ι → Set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`. -/
/-
**Filter.hasBasis_iInf_principal_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_iInf_principal_finite {ι : Type*} (s : ι -> Set α) : (⨅ i, 𝓟 (s i
)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i in t, s i
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.mem_iInf_finite`：mem_iInf_finite {ι : Type*} {f : ι -> Filter α} 
(s) : s in iInf f ↔ exists t : Finset ι, s in ⨅ i in t, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.iInf_principal_finset`：iInf_principal_finset {ι : Type w} (s : Fi
nset ι) (f : ι -> Set α) : ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `s : ι → Set α` is an indexed family of sets, then finite intersections of `s
 i` form a basis
of `⨅ i, 𝓟 (s i)`.
-/
theorem hasBasis_iInf_principal_finite {ι : Type*} (s : ι → Set α) :
    (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i ∈ t, s i := by
  refine ⟨fun U => (mem_iInf_finite _).trans ?_⟩
  simp only [iInf_principal_finset, mem_principal,
    exists_finite_iff_finset, Finset.set_biInter_coe]

end SameType

end Filter

