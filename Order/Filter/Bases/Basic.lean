/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Set.Sigma
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Interval.Set.Basic

/-!
# Basic results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : Filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → Set α`,
the proposition `h : Filter.IsBasis p s` makes sure the range of `s` bounded by `p`
(i.e. `s '' Set.ofPred p`) defines a filter basis `h.filterBasis`.

If one already has a filter `l` on `α`, `Filter.HasBasis l p s` (where `p : ι → Prop`
and `s : ι → Set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : Filter.IsBasis p s`, and
`l = h.filterBasis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `HasBasis.index (h : Filter.HasBasis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

## Main statements

* `Filter.HasBasis.mem_iff`, `HasBasis.mem_of_superset`, `HasBasis.mem_of_mem` : restate `t ∈ f` in
  terms of a basis;

* `Filter.HasBasis.le_iff`, `Filter.HasBasis.ge_iff`, `Filter.HasBasis.le_basis_iff` : restate
  `l ≤ l'` in terms of bases.

* `Filter.basis_sets` : all sets of a filter form a basis;

* `Filter.HasBasis.inf`, `Filter.HasBasis.inf_principal`, `Filter.HasBasis.prod`,
  `Filter.HasBasis.prod_self`, `Filter.HasBasis.map`, `Filter.HasBasis.comap` : combinators to
  construct filters of `l ⊓ l'`, `l ⊓ 𝓟 t`, `l ×ˢ l'`, `l ×ˢ l`, `l.map f`, `l.comap f`
  respectively;

* `Filter.HasBasis.tendsto_right_iff`, `Filter.HasBasis.tendsto_left_iff`,
  `Filter.HasBasis.tendsto_iff` : restate `Tendsto f l l'` in terms of bases.

## Implementation notes

As with `Set.iUnion`/`biUnion`/`Set.sUnion`, there are three different approaches to filter bases:

* `Filter.HasBasis l s`, `s : Set (Set α)`;
* `Filter.HasBasis l s`, `s : ι → Set α`;
* `Filter.HasBasis l p s`, `p : ι → Prop`, `s : ι → Set α`.

We use the latter one because, e.g., `𝓝 x` in an `EMetricSpace` or in a `MetricSpace` has a basis
of this form. The other two can be emulated using `s = id` or `p = fun _ ↦ True`.

With this approach sometimes one needs to `simp` the statement provided by the `Filter.HasBasis`
machinery, e.g., `simp only [true_and_iff]` or `simp only [forall_const]` can help with the case
`p = fun _ ↦ True`.

## Main statements
-/

@[expose] public section

assert_not_exists Finset

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
/-
**FilterBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_6 → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some elem
ent
of the collection.
-/
structure FilterBasis (α : Type*) where
  /-- Sets of a filter basis. -/
  sets : Set (Set α)
  /-- The set of filter basis sets is nonempty. -/
  nonempty : sets.Nonempty
  /-- The set of filter basis sets is directed downwards. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y
/-
**FilterBasis.nonempty_sets** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets
参数：B : FilterBasis α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `FilterBasis.nonempty`：∀ {α : Type u_6} (self : FilterBasis α), self.sets
.Nonempty
-/
instance FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets :=
  B.nonempty.to_subtype

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ 
B` as
on paper.
-/
instance {α : Type*} : Membership (Set α) (FilterBasis α) :=
  ⟨fun B U => U ∈ B.sets⟩
/-
**FilterBasis.mem_sets** 是 Mathlib 中的一个定理，位于命名空间 `FilterBasis`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {B : FilterBasis α}, s ∈ B.sets ↔ s ∈ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem FilterBasis.mem_sets {s : Set α} {B : FilterBasis α} : s ∈ B.sets ↔ s ∈ B := Iff.rfl

-- For illustration purposes, the filter basis defining `(atTop : Filter ℕ)`
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FilterBasis ℕ) :=
  ⟨{  sets := range Ici
      nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        exact ⟨Ici (max n m), mem_range_self _, Ici_inter_Ici.symm.subset⟩ }⟩

/-- View a filter as a filter basis. -/
/-
**Filter.asBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.asBasis (f : Filter α) : FilterBasis α
参数：f : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
View a filter as a filter basis.
-/
def Filter.asBasis (f : Filter α) : FilterBasis α :=
  ⟨f.sets, ⟨univ, univ_mem⟩, fun {x y} hx hy => ⟨x ∩ y, inter_mem hx hy, subset_rfl⟩⟩

-- TODO: consider adding `protected`?
/-- `IsBasis p s` means the image of `s` bounded by `p` is a filter basis. -/
/-
**Filter.IsBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {ι : Sort u_4} → (ι → Prop) → (ι → Set α) → Prop
参数：ι → Prop；ι → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsBasis p s` means the image of `s` bounded by `p` is a filter basis.
-/
structure Filter.IsBasis (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- There exists at least one `i` that satisfies `p`. -/
  nonempty : ∃ i, p i
  /-- `s` is directed downwards on `i` such that `p i`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j

namespace Filter

namespace IsBasis

/-- Constructs a filter basis from an indexed family of sets satisfying `IsBasis`. -/
/-
**Filter.IsBasis.filterBasis** 是 Mathlib 中的一个定义，位于命名空间 `Filter.IsBasis`。
形式化陈述：{α : Type u_1} → {ι : Sort u_4} → {p : ι → Prop} → {s : ι → Set α} → Filte
r.IsBasis p s → FilterBasis α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a filter basis from an indexed family of sets satisfying `IsBasis`.
-/
protected def filterBasis {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s) : FilterBasis α where
  sets := { t | ∃ i, p i ∧ s i = t }
  nonempty :=
    let ⟨i, hi⟩ := h.nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩

variable {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s)
/-
**Filter.IsBasis.mem_filterBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBasis`。
形式化陈述：mem_filterBasis_iff {U : Set α} : U in h.filterBasis ↔ exists i, p i ∧ s i
 = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_filterBasis_iff {U : Set α} : U ∈ h.filterBasis ↔ ∃ i, p i ∧ s i = U :=
  Iff.rfl

end IsBasis

end Filter

namespace FilterBasis

/-- The filter associated to a filter basis. -/
/-
**FilterBasis.filter** 是 Mathlib 中的一个定义，位于命名空间 `FilterBasis`。
形式化陈述：{α : Type u_1} → FilterBasis α → Filter α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filter associated to a filter basis.
-/
protected def filter (B : FilterBasis α) : Filter α where
  sets := { s | ∃ t ∈ B, t ⊆ s }
  univ_sets := B.nonempty.imp fun s s_in => ⟨s_in, s.subset_univ⟩
  sets_of_superset := fun ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun ⟨_s, s_in, hs⟩ ⟨_t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, u_sub.trans (inter_subset_inter hs ht)⟩
/-
**FilterBasis.mem_filter_iff** 是 Mathlib 中的一个定理，位于命名空间 `FilterBasis`。
形式化陈述：mem_filter_iff (B : FilterBasis α) {U : Set α} : U in B.filter ↔ exists s 
in B, s subseteq U
参数：B : FilterBasis α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_filter_iff (B : FilterBasis α) {U : Set α} : U ∈ B.filter ↔ ∃ s ∈ B, s ⊆ U :=
  Iff.rfl
/-
**FilterBasis.mem_filter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `FilterBasis`。
形式化陈述：mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U in B -> U in B.filte
r
参数：B : FilterBasis α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U ∈ B → U ∈ B.filter := fun U_in =>
  ⟨U, U_in, Subset.refl _⟩
/-
**FilterBasis.eq_iInf_principal** 是 Mathlib 中的一个定理，位于命名空间 `FilterBasis`。
形式化陈述：eq_iInf_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s
参数：B : FilterBasis α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FilterBasis.inter_sets`：∀ {α : Type u_6} (self : FilterBasis α) {x y : S
et α}, x ∈ self.sets → y ∈ self.sets → ∃ z ∈ self.sets, z ⊆ x ∩ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_iInf_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s := by
  have : Directed (· ≥ ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [le_principal_iff, mem_principal]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of_directed this]
/-
**FilterBasis.generate** 是 Mathlib 中的一个定理，位于命名空间 `FilterBasis`。
形式化陈述：∀ {α : Type u_1} (B : FilterBasis α), Filter.generate B.sets = B.filter
参数：B : FilterBasis α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FilterBasis.mem_filter_iff`：mem_filter_iff (B : FilterBasis α) {U : Set 
α} : U in B.filter ↔ exists s in B, s subseteq U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_generate_iff`：le_generate_iff {s : Set (Set α)} {f : Filter α}
 : f <= generate s ↔ s subseteq f.sets
· 使用定理 `FilterBasis.mem_filter_of_mem`：mem_filter_of_mem (B : FilterBasis α) {U 
: Set α} : U in B -> U in B.filter
-/
protected theorem generate (B : FilterBasis α) : generate B.sets = B.filter := by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem
/-
**FilterBasis.ker_filter** 是 Mathlib 中的一个引理，位于命名空间 `FilterBasis`。
形式化陈述：ker_filter (F : FilterBasis α) : F.filter.ker = ⋂₀ F.sets
参数：F : FilterBasis α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma ker_filter (F : FilterBasis α) : F.filter.ker = ⋂₀ F.sets := by
  aesop (add simp [ker, FilterBasis.filter])

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι → Prop} {s : ι → Set α}

/-- Constructs a filter from an indexed family of sets satisfying `IsBasis`. -/
/-
**Filter.IsBasis.filter** 是 Mathlib 中的一个定义，位于命名空间 `Filter.IsBasis`。
形式化陈述：{α : Type u_1} → {ι : Sort u_4} → {p : ι → Prop} → {s : ι → Set α} → Filte
r.IsBasis p s → Filter α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a filter from an indexed family of sets satisfying `IsBasis`.
-/
protected def filter (h : IsBasis p s) : Filter α :=
  h.filterBasis.filter
/-
**Filter.IsBasis.mem_filter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {p : ι → Prop} {s : ι → Set α} (h : Filter
.IsBasis p s) {U : Set α},   U ∈ h.filter ↔ ∃ i, p i ∧ s i ⊆ U
参数：h : Filter.IsBasis p s。
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
protected theorem mem_filter_iff (h : IsBasis p s) {U : Set α} :
    U ∈ h.filter ↔ ∃ i, p i ∧ s i ⊆ U := by
  simp only [IsBasis.filter, FilterBasis.mem_filter_iff, mem_filterBasis_iff,
    exists_exists_and_eq_and]
/-
**Filter.IsBasis.filter_eq_generate** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBasis`。
形式化陈述：filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | exists i,
 p i ∧ s i = U }
参数：h : IsBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.IsBasis.filter.eq_1`：∀ {α : Type u_1} {ι : Sort u_4} {p : ι → Pro
p} {s : ι → Set α} (h : Filter.IsBasis p s), h.filter = h.filterBasis.filter
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FilterBasis.generate`：∀ {α : Type u_1} (B : FilterBasis α), Filter.gener
ate B.sets = B.filter
· 使用定理 `Filter.IsBasis.filterBasis.eq_1`：∀ {α : Type u_1} {ι : Sort u_4} {p : ι 
→ Prop} {s : ι → Set α} (h : Filter.IsBasis p s),   h.filterBasis = { sets := {t
 | ∃ i, p i ∧ s i = t…
-/
theorem filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [IsBasis.filter, ← h.filterBasis.generate, IsBasis.filterBasis]

end IsBasis

-- TODO: consider adding `protected`?
/-- We say that a filter `l` has a basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
/-
**Filter.HasBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {ι : Sort u_4} → Filter α → (ι → Prop) → (ι → Set α) → Pr
op
参数：ι → Prop；ι → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a filter `l` has a basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`.
-/
structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

/-- Definition of `HasBasis` unfolded with implicit set argument. -/
/-
**Filter.HasBasis.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t)
参数：t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t

--- 原说明 ---
Definition of `HasBasis` unfolded with implicit set argument.
-/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  hl.mem_iff' t
/-
**Filter.HasBasis.eq_of_same_basis** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l l' : Filter α} {p : ι → Prop} {s : ι → 
Set α},   l.HasBasis p s → l'.HasBasis p s → l = l'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' := by
  ext t
  rw [hl.mem_iff, hl'.mem_iff]
/-
**Filter.hasBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_iff : l.HasBasis p s ↔ forall t, t in l ↔ exists i, p i ∧ s i sub
seteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasBasis_iff : l.HasBasis p s ↔ ∀ t, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
/-
**Filter.HasBasis.ex_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α}, l.HasBasis p s → ∃ i, p i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem HasBasis.ex_mem (h : l.HasBasis p s) : ∃ i, p i :=
  (h.mem_iff.mp univ_mem).imp fun _ => And.left
/-
**Filter.HasBasis.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α}, l.HasBasis p s → Nonempty ι
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Filter.HasBasis.ex_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {
p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → ∃ i, p i
-/
protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  h.ex_mem.nonempty
/-
**Filter.IsBasis.hasBasis** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {p : ι → Prop} {s : ι → Set α} (h : Filter
.IsBasis p s), h.filter.HasBasis p s
参数：h : Filter.IsBasis p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.IsBasis.mem_filter_iff`：∀ {α : Type u_1} {ι : Sort u_4} {p : ι → 
Prop} {s : ι → Set α} (h : Filter.IsBasis p s) {U : Set α},   U ∈ h.filter ↔ ∃ i
, p i ∧ s i ⊆ U
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filter p s :=
  ⟨fun t => by simp only [h.mem_filter_iff]⟩
/-
**Filter.HasBasis.mem_of_superset** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {t : Set α} {i : ι},   l.HasBasis p s → p i → s i ⊆ t → t ∈ l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
protected theorem HasBasis.mem_of_superset (hl : l.HasBasis p s) (hi : p i) (ht : s i ⊆ t) :
    t ∈ l :=
  hl.mem_iff.2 ⟨i, hi, ht⟩
/-
**Filter.HasBasis.mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_superset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι},   l.HasBasis p s → p
 i → s i ⊆ t → t ∈ l
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem HasBasis.mem_of_mem (hl : l.HasBasis p s) (hi : p i) : s i ∈ l :=
  hl.mem_of_superset hi Subset.rfl

/-- Index of a basis set such that `s i ⊆ t` as an element of `Subtype p`. -/
/-
**Filter.HasBasis.index** 是 Mathlib 中的一个定义，位于命名空间 `Filter.HasBasis`。
形式化陈述：{α : Type u_1} →   {ι : Sort u_4} →     {l : Filter α} → {p : ι → Prop} → 
{s : ι → Set α} → l.HasBasis p s → (t : Set α) → t ∈ l → { i // p i }
参数：t : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Index of a basis set such that `s i ⊆ t` as an element of `Subtype p`.
-/
noncomputable def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t ∈ l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩
/-
**Filter.HasBasis.property_index** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {t : Set α} (h : l.HasBasis p s)   (ht : t ∈ l), p ↑(h.index t ht)
参数：h : l.HasBasis p s；ht : t ∈ l；h.index t ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem HasBasis.property_index (h : l.HasBasis p s) (ht : t ∈ l) : p (h.index t ht) :=
  (h.index t ht).2
/-
**Filter.HasBasis.set_index_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {t : Set α} (h : l.HasBasis p s)   (ht : t ∈ l), s ↑(h.index t ht) ∈ l
参数：h : l.HasBasis p s；ht : t ∈ l；h.index t ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Filter.HasBasis.property_index`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} (h : l.HasBasis p s)   (ht : t
 ∈ l), p ↑(h.index t…
-/
theorem HasBasis.set_index_mem (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ∈ l :=
  h.mem_of_mem <| h.property_index _
/-
**Filter.HasBasis.set_index_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {t : Set α} (h : l.HasBasis p s)   (ht : t ∈ l), s ↑(h.index t ht) ⊆ t
参数：h : l.HasBasis p s；ht : t ∈ l；h.index t ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem HasBasis.set_index_subset (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ⊆ t :=
  (h.mem_iff.1 ht).choose_spec.2
/-
**Filter.HasBasis.isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α}, l.HasBasis p s → Filter.IsBasis p s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.ex_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {
p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → ∃ i, p i
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem HasBasis.isBasis (h : l.HasBasis p s) : IsBasis p s where
  nonempty := h.ex_mem
  inter hi hj := by
    simpa only [h.mem_iff] using inter_mem (h.mem_of_mem hi) (h.mem_of_mem hj)
/-
**Filter.HasBasis.filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} (h : l.HasBasis p s), ⋯.filter = l
参数：h : l.HasBasis p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Filter.HasBasis.isBasis`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → Filter.IsBasis p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.filter_eq (h : l.HasBasis p s) : h.isBasis.filter = l := by
  ext U
  simp [h.mem_iff, IsBasis.mem_filter_iff]
/-
**Filter.HasBasis.eq_generate** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → l = Filter.generate {U | ∃ i, p i ∧ s i = U}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.isBasis`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → Filter.IsBasis p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.IsBasis.filter_eq_generate`：filter_eq_generate (h : IsBasis p s) 
: h.filter = generate { U | exists i, p i ∧ s i = U }
· 使用定理 `Filter.HasBasis.filter_eq`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α} (h : l.HasBasis p s), ⋯.filter = l
-/
theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [← h.isBasis.filter_eq_generate, h.filter_eq]
/-
**Filter._root_.FilterBasis.hasBasis** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.FilterBasis.hasBasis (B : FilterBasis α) :
    HasBasis B.filter (fun s : Set α => s ∈ B) id :=
  ⟨fun _ => B.mem_filter_iff⟩
/-
**Filter.HasBasis.to_hasBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l : Filter α} {p : ι → Pr
op} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → (∀ 
(i : ι), p i → ∃ i', p' i' ∧ s' i' ⊆ s i) → (∀ (i' : ι'), p' i' → s' i' ∈ l) → l
.HasBasis p' s'
参数：∀ (i : ι), p i → ∃ i', p' i' ∧ s' i' ⊆ s i；∀ (i' : ι'), p' i' → s' i' ∈ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem HasBasis.to_hasBasis' (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → s' i' ∈ l) : l.HasBasis p' s' := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', hs's.trans ht⟩
/-
**Filter.HasBasis.to_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l : Filter α} {p : ι → Pr
op} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s →    
 (∀ (i : ι), p i → ∃ i', p' i' ∧ s' i' ⊆ s i) → (∀ (i' : ι'), p' i' → ∃ i, p i ∧
 s i ⊆ s' i') → l.HasBasis p' s'
参数：∀ (i : ι), p i → ∃ i', p' i' ∧ s' i' ⊆ s i；∀ (i' : ι'), p' i' → ∃ i, p i ∧ s 
i ⊆ s' i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
theorem HasBasis.to_hasBasis (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l.HasBasis p' s' :=
  hl.to_hasBasis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩
/-
**Filter.HasBasis.congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s →     ∀ {p' : ι → Prop} {s' : ι → Set α}, (∀ (i : ι), p i 
↔ p' i) → (∀ (i : ι), p i → s i = s' i) → l.HasBasis p' s'
参数：∀ (i : ι), p i ↔ p' i；∀ (i : ι), p i → s i = s' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma HasBasis.congr (hl : l.HasBasis p s) {p' s'} (hp : ∀ i, p i ↔ p' i)
    (hs : ∀ i, p i → s i = s' i) : l.HasBasis p' s' :=
  ⟨fun t ↦ by simp only [hl.mem_iff, ← hp]; exact exists_congr fun i ↦
    and_congr_right fun hi ↦ hs i hi ▸ Iff.rfl⟩
/-
**Filter.HasBasis.to_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {t : ι → Set α}, (∀ (i : ι), p i → t i ⊆ s i) → (∀ (i 
: ι), p i → t i ∈ l) → l.HasBasis p t
参数：∀ (i : ι), p i → t i ⊆ s i；∀ (i : ι), p i → t i ∈ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
-/
theorem HasBasis.to_subset (hl : l.HasBasis p s) {t : ι → Set α} (h : ∀ i, p i → t i ⊆ s i)
    (ht : ∀ i, p i → t i ∈ l) : l.HasBasis p t :=
  hl.to_hasBasis' (fun i hi => ⟨i, hi, h i hi⟩) ht
/-
**Filter.HasBasis.eventually_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ (x : α) in l, q x) ↔ ∃ i, p i ∧ ∀ 
⦃x : α⦄, x ∈ s i → q x
参数：∀ᶠ (x : α) in l, q x。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
theorem HasBasis.eventually_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x := by simpa using! hl.mem_iff
/-
**Filter.HasBasis.frequently_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ (x : α) in l, q x) ↔ ∀ (i : ι), p 
i → ∃ x ∈ s i, q x
参数：∃ᶠ (x : α) in l, q x；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasBasis.frequently_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∃ᶠ x in l, q x) ↔ ∀ i, p i → ∃ x ∈ s i, q x := by
  simp only [Filter.Frequently, hl.eventually_iff]; push Not; rfl
/-
**Filter.HasBasis.exists_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃s t : Set α⦄, s ⊆ t → P t → P 
s) → ((∃ s ∈ l, P s) ↔ ∃ i, p i ∧ P (s i))
参数：∀ ⦃s t : Set α⦄, s ⊆ t → P t → P s；(∃ s ∈ l, P s) ↔ ∃ i, p i ∧ P (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem HasBasis.exists_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P t → P s) : (∃ s ∈ l, P s) ↔ ∃ i, p i ∧ P (s i) :=
  ⟨fun ⟨_s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩
/-
**Filter.HasBasis.forall_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, (∀ ⦃s t : Set α⦄, s ⊆ t → P s 
→ P t) → ((∀ s ∈ l, P s) ↔ ∀ (i : ι), p i → P (s i))
参数：∀ ⦃s t : Set α⦄, s ⊆ t → P s → P t；(∀ s ∈ l, P s) ↔ ∀ (i : ι), p i → P (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
theorem HasBasis.forall_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P s → P t) : (∀ s ∈ l, P s) ↔ ∀ i, p i → P (s i) :=
  ⟨fun H i hi => H (s i) <| hl.mem_of_mem hi, fun H _s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩
/-
**Filter.HasBasis.neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i → (s i).Nonempty)
参数：l.NeBot ↔ ∀ {i : ι}, p i → (s i).Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.forall_mem_nonempty_iff_neBot`：forall_mem_nonempty_iff_neBot {f :
 Filter α} : (forall s : Set α, s in f -> s.Nonempty) ↔ NeBot f
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
-/
protected theorem HasBasis.neBot_iff (hl : l.HasBasis p s) :
    NeBot l ↔ ∀ {i}, p i → (s i).Nonempty :=
  forall_mem_nonempty_iff_neBot.symm.trans <| hl.forall_iff fun _ _ => Nonempty.mono
/-
**Filter.HasBasis.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → (l = ⊥ ↔ ∃ i, p i ∧ s i = ∅)
参数：l = ⊥ ↔ ∃ i, p i ∧ s i = ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
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
theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
  not_iff_not.1 <| neBot_iff.symm.trans <|
    hl.neBot_iff.trans <| by simp only [not_exists, not_and, nonempty_iff_ne_empty]
/-
**Filter.basis_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s in l) id
参数：l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
-/
theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s ∈ l) id :=
  ⟨fun _ => exists_mem_subset_iff.symm⟩
/-
**Filter.asBasis_filter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：asBasis_filter (f : Filter α) : f.asBasis.filter = f
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
-/
theorem asBasis_filter (f : Filter α) : f.asBasis.filter = f :=
  Filter.ext fun _ => exists_mem_subset_iff
/-
**Filter.hasBasis_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_self {l : Filter α} {P : Set α -> Prop} : HasBasis l (fun s => s 
in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem hasBasis_self {l : Filter α} {P : Set α → Prop} :
    HasBasis l (fun s => s ∈ l ∧ P s) id ↔ ∀ t ∈ l, ∃ r ∈ l, P r ∧ r ⊆ t := by
  simp only [hasBasis_iff, id, and_assoc]
  exact forall_congr' fun s =>
    ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, _, hts⟩ => mem_of_superset hl hts⟩⟩
/-
**Filter.HasBasis.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l : Filter α} {p : ι → Pr
op} {s : ι → Set α},   l.HasBasis p s → ∀ {g : ι' → ι}, Function.Surjective g → 
l.HasBasis (p ∘ g) (s ∘ g)
参数：p ∘ g；s ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
-/
theorem HasBasis.comp_surjective (h : l.HasBasis p s) {g : ι' → ι} (hg : Function.Surjective g) :
    l.HasBasis (p ∘ g) (s ∘ g) :=
  ⟨fun _ => h.mem_iff.trans hg.exists⟩
/-
**Filter.HasBasis.comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l : Filter α} {p : ι → Pr
op} {s : ι → Set α},   l.HasBasis p s → ∀ (e : ι' ≃ ι), l.HasBasis (p ∘ ⇑e) (s ∘
 ⇑e)
参数：e : ι' ≃ ι；p ∘ ⇑e；s ∘ ⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comp_surjective`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : S
ort u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {g 
: ι' → ι}, Function.S…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem HasBasis.comp_equiv (h : l.HasBasis p s) (e : ι' ≃ ι) : l.HasBasis (p ∘ e) (s ∘ e) :=
  h.comp_surjective e.surjective
/-
**Filter.HasBasis.to_image_id'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → l.HasBasis (fun t => ∃ i, p i ∧ s i = t) id
参数：fun t => ∃ i, p i ∧ s i = t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.to_image_id' (h : l.HasBasis p s) : l.HasBasis (fun t ↦ ∃ i, p i ∧ s i = t) id :=
  ⟨fun _ ↦ by simp [h.mem_iff]⟩
/-
**Filter.HasBasis.to_image_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Type u_6} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → l.HasBasis (fun x => x ∈ s '' {i | p i}) id
参数：fun x => x ∈ s '' {i | p i}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_image_id'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filte
r α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.HasBasis (fun t => ∃ i
, p i ∧ s i = t) i…
-/
theorem HasBasis.to_image_id {ι : Type*} {p : ι → Prop} {s : ι → Set α} (h : l.HasBasis p s) :
    l.HasBasis (· ∈ s '' {i | p i}) id :=
  h.to_image_id'

/-- If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such that
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`. -/
/-
**Filter.HasBasis.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {q : ι → Prop}, (∀ (i : ι), p i → ∃ j, p j ∧ q j ∧ s j
 ⊆ s i) → l.HasBasis (fun i => p i ∧ q i) s
参数：∀ (i : ι), p i → ∃ j, p j ∧ q j ∧ s j ⊆ s i；fun i => p i ∧ q i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such t
hat
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`.
-/
theorem HasBasis.restrict (h : l.HasBasis p s) {q : ι → Prop}
    (hq : ∀ i, p i → ∃ j, p j ∧ q j ∧ s j ⊆ s i) : l.HasBasis (fun i => p i ∧ q i) s := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, hji.trans hti⟩

/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
/-
**Filter.HasBasis.restrict_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l → l.HasBasis (fun i => p i ∧ s i ⊆ 
V) s
参数：fun i => p i ∧ s i ⊆ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.restrict`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : ι → Prop}, (∀ (i : ι)
, p i → ∃ j, p…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l

--- 原说明 ---
If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i 
⊆ V}`
is a basis of `l`.
-/
theorem HasBasis.restrict_subset (h : l.HasBasis p s) {V : Set α} (hV : V ∈ l) :
    l.HasBasis (fun i => p i ∧ s i ⊆ V) s :=
  h.restrict fun _i hi => (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun _j hj =>
    ⟨hj.1, subset_inter_iff.1 hj.2⟩
/-
**Filter.HasBasis.hasBasis_self_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {p : Set α → Prop},   l.HasBasis (fun s =>
 s ∈ l ∧ p s) id → ∀ {V : Set α}, V ∈ l → l.HasBasis (fun s => s ∈ l ∧ p s ∧ s ⊆
 V) id
参数：fun s => s ∈ l ∧ p s；fun s => s ∈ l ∧ p s ∧ s ⊆ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.restrict_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun i =…
-/
theorem HasBasis.hasBasis_self_subset {p : Set α → Prop} (h : l.HasBasis (fun s => s ∈ l ∧ p s) id)
    {V : Set α} (hV : V ∈ l) : l.HasBasis (fun s => s ∈ l ∧ p s ∧ s ⊆ V) id := by
  simpa only [and_assoc] using! h.restrict_subset hV
/-
**Filter.HasBasis.ge_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter α} {p' : ι' → Prop} {s' : 
ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι'), p' i' → s' i' ∈ l)
参数：l ≤ l' ↔ ∀ (i' : ι'), p' i' → s' i' ∈ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem HasBasis.ge_iff (hl' : l'.HasBasis p' s') : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
  ⟨fun h _i' hi' => h <| hl'.mem_of_mem hi', fun h _s hs =>
    let ⟨_i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩
/-
**Filter.HasBasis.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l l' : Filter α} {p : ι → Prop} {s : ι → 
Set α},   l.HasBasis p s → (l ≤ l' ↔ ∀ t ∈ l', ∃ i, p i ∧ s i ⊆ t)
参数：l ≤ l' ↔ ∀ t ∈ l', ∃ i, p i ∧ s i ⊆ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.le_iff (hl : l.HasBasis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i, p i ∧ s i ⊆ t := by
  simp only [le_def, hl.mem_iff]
/-
**Filter.HasBasis.le_basis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l l' : Filter α} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α}, l.HasBasis p s → l'
.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι'), p' i' → ∃ i, p i ∧ s i ⊆ s' i')
参数：l ≤ l' ↔ ∀ (i' : ι'), p' i' → ∃ i, p i ∧ s i ⊆ s' i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l ≤ l' ↔ ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i' := by
  simp only [hl'.ge_iff, hl.mem_iff]
/-
**Filter.HasBasis.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → (l = ⊤ ↔ ∀ (i : ι), p i → s i = Set.univ)
参数：l = ⊤ ↔ ∀ (i : ι), p i → s i = Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.eq_top_iff (h : l.HasBasis p s) : l = ⊤ ↔ ∀ i, p i → s i = univ := by
  simp [← top_le_iff, h.ge_iff]
/-
**Filter.HasBasis.ext** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l l' : Filter α} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
    l'.HasBasis p' s' →       (∀ (i : ι), p i → ∃ i', p' i' ∧ s' i' ⊆ s i) → (∀ 
(i' : ι'), p' i' → ∃ i, p i ∧ s i ⊆ s' i') → l = l'
参数：∀ (i : ι), p i → ∃ i', p' i' ∧ s' i' ⊆ s i；∀ (i' : ι'), p' i' → ∃ i, p i ∧ s 
i ⊆ s' i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
-/
theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i) (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h
/-
**Filter.HasBasis.inf'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l l' : Filter α} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
l'.HasBasis p' s' → (l ⊓ l').HasBasis (fun i => p i.fst ∧ p' i.snd) fun i => s i
.fst ∩ s' i.snd
参数：l ⊓ l'；fun i => p i.fst ∧ p' i.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_inf_of_inter`：mem_inf_of_inter {f g : Filter α} {s t u : Set 
α} (hs : s in f) (ht : t in g) (h : s inter t subseteq u) : u in f ⊓ g
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem HasBasis.inf' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      exact ⟨⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'⟩
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H⟩
/-
**Filter.HasBasis.inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {ι' : Type u_7} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
l'.HasBasis p' s' → (l ⊓ l').HasBasis (fun i => p i.1 ∧ p' i.2) fun i => s i.1 ∩
 s' i.2
参数：l ⊓ l'；fun i => p i.1 ∧ p' i.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comp_equiv`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u
_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (e : ι' 
≃ ι), l.HasBasis…
· 使用定理 `Filter.HasBasis.inf'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l
 l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set
 α},   l.H…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem HasBasis.inf {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm
/-
**Filter.hasBasis_iInf_of_directed'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_iInf_of_directed' {ι : Type*} {ι' : ι -> Sort _} [Nonempty ι] {l 
: ι -> Filter α} (s : forall i, ι' i -> Set α) (p : forall i, ι' i -> Prop) (hl 
: forall i, (l i).HasBasis (p i) (s i)) (h : Directed (· >= ·) l) : (⨅ i, l i).H
asBasis (fun ii' : Σ i, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2
参数：s : forall i, ι' i -> Set α；p : forall i, ι' i -> Prop；hl : forall i, (l i).H
asBasis (p i) (s i)；h : Directed (· >= ·) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `Sigma.exists`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop}, (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
theorem hasBasis_iInf_of_directed' {ι : Type*} {ι' : ι → Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σ i, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff
/-
**Filter.hasBasis_iInf_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_iInf_of_directed {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι ->
 Filter α} (s : ι -> ι' -> Set α) (p : ι -> ι' -> Prop) (hl : forall i, (l i).Ha
sBasis (p i) (s i)) (h : Directed (· >= ·) l) : (⨅ i, l i).HasBasis (fun ii' : ι
 × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2
参数：s : ι -> ι' -> Set α；p : ι -> ι' -> Prop；hl : forall i, (l i).HasBasis (p i) 
(s i)；h : Directed (· >= ·) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
theorem hasBasis_iInf_of_directed {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ι → ι' → Set α) (p : ι → ι' → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff
/-
**Filter.hasBasis_biInf_of_directed'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_biInf_of_directed' {ι : Type*} {ι' : ι -> Sort _} {dom : Set ι} (
hdom : dom.Nonempty) {l : ι -> Filter α} (s : forall i, ι' i -> Set α) (p : fora
ll i, ι' i -> Prop) (hl : forall i in dom, (l i).HasBasis (p i) (s i)) (h : Dire
ctedOn (l ⁻¹'o GE.ge) dom) : (⨅ i in dom, l i).HasBasis (fun ii' : Σ i, ι' i => 
ii'.1 in dom ∧ p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2
参数：hdom : dom.Nonempty；s : forall i, ι' i -> Set α；p : forall i, ι' i -> Prop；hl
 : forall i in dom, (l i).HasBasis (p i) (s i)；h : DirectedOn (l ⁻¹'o GE.ge) dom
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_biInf_of_directed`：mem_biInf_of_directed {f : β -> Filter α} 
{s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s) (ne : s.Nonempty) {t : Set α} :
 (t in ⨅ i in s, f…
· 使用定理 `Sigma.exists`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop}, (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩
-/
theorem hasBasis_biInf_of_directed' {ι : Type*} {ι' : ι → Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι → Filter α} (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : Σ i, ι' i => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Sigma.exists]
  grind +splitIndPred
/-
**Filter.hasBasis_biInf_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_biInf_of_directed {ι : Type*} {ι' : Sort _} {dom : Set ι} (hdom :
 dom.Nonempty) {l : ι -> Filter α} (s : ι -> ι' -> Set α) (p : ι -> ι' -> Prop) 
(hl : forall i in dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge
) dom) : (⨅ i in dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 in dom ∧ p ii'.1 
ii'.2) fun ii' => s ii'.1 ii'.2
参数：hdom : dom.Nonempty；s : ι -> ι' -> Set α；p : ι -> ι' -> Prop；hl : forall i in
 dom, (l i).HasBasis (p i) (s i)；h : DirectedOn (l ⁻¹'o GE.ge) dom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_biInf_of_directed`：mem_biInf_of_directed {f : β -> Filter α} 
{s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s) (ne : s.Nonempty) {t : Set α} :
 (t in ⨅ i in s, f…
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
-/
theorem hasBasis_biInf_of_directed {ι : Type*} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
    {l : ι → Filter α} (s : ι → ι' → Set α) (p : ι → ι' → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Prod.exists]
  grind +splitIndPred
/-
**Filter.hasBasis_top** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：hasBasis_top : (⊤ : Filter α).HasBasis (fun _ : Unit => True) (fun _ => Se
t.univ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasBasis_top :
    (⊤ : Filter α).HasBasis (fun _ : Unit ↦ True) (fun _ ↦ Set.univ) :=
  ⟨fun U => by simp⟩
/-
**Filter.hasBasis_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun _ : Unit => True) fun
 _ => t
参数：t : Set α。
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t :=
  ⟨fun U => by simp⟩
/-
**Filter.hasBasis_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_pure (x : α) : (pure x : Filter α).HasBasis (fun _ : Unit => True
) fun _ => {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hasBasis_pure (x : α) :
    (pure x : Filter α).HasBasis (fun _ : Unit => True) fun _ => {x} := by
  simp only [← principal_singleton, hasBasis_principal]
/-
**Filter.HasBasis.sup'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l l' : Filter α} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
l'.HasBasis p' s' → (l ⊔ l').HasBasis (fun i => p i.fst ∧ p' i.snd) fun i => s i
.fst ∪ s' i.snd
参数：l ⊔ l'；fun i => p i.fst ∧ p' i.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩
/-
**Filter.HasBasis.sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {ι' : Type u_7} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
l'.HasBasis p' s' → (l ⊔ l').HasBasis (fun i => p i.1 ∧ p' i.2) fun i => s i.1 ∪
 s' i.2
参数：l ⊔ l'；fun i => p i.1 ∧ p' i.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comp_equiv`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u
_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (e : ι' 
≃ ι), l.HasBasis…
· 使用定理 `Filter.HasBasis.sup'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l
 l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set
 α},   l.H…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem HasBasis.sup {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm
/-
**Filter.hasBasis_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_iSup {ι : Sort*} {ι' : ι -> Type*} {l : ι -> Filter α} {p : foral
l i, ι' i -> Prop} {s : forall i, ι' i -> Set α} (hl : forall i, (l i).HasBasis 
(p i) (s i)) : (⨆ i, l i).HasBasis (fun f : forall i, ι' i => forall i, p i (f i
)) fun f : forall i, ι' i => ⋃ i, s i (f i)
参数：hl : forall i, (l i).HasBasis (p i) (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_iff`：hasBasis_iff : l.HasBasis p s ↔ forall t, t in l ↔ 
exists i, p i ∧ s i subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasBasis_iSup {ι : Sort*} {ι' : ι → Type*} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : ∀ i, ι' i => ∀ i, p i (f i)) fun f : ∀ i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [(hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]
/-
**Filter.HasBasis.sup_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ (t : Set α), (l ⊔ Filter.principal t).HasBasis p fun i
 => s i ∪ t
参数：t : Set α；l ⊔ Filter.principal t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.sup'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l
 l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set
 α},   l.H…
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i ∪ t :=
  ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, and_true,
      Unique.exists_iff]⟩
/-
**Filter.HasBasis.sup_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ (x : α), (l ⊔ pure x).HasBasis p fun i => s i ∪ {x}
参数：x : α；l ⊔ pure x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.HasBasis.sup_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), (l ⊔ Fil
ter.principal t).Ha…
-/
theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i ∪ {x} := by
  simp only [← principal_singleton, hl.sup_principal]
/-
**Filter.HasBasis.inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Filter.principal s').HasBasis p fun
 i => s i ∩ s'
参数：s' : Set α；l ⊓ Filter.principal s'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i ∩ s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_ofPred_eq, mem_inter_iff, and_imp]⟩
/-
**Filter.HasBasis.principal_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ (s' : Set α), (Filter.principal s' ⊓ l).HasBasis p fun
 i => s' ∩ s i
参数：s' : Set α；Filter.principal s' ⊓ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
-/
theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' ∩ s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'
/-
**Filter.HasBasis.inf_basis_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis
`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l l' : Filter α} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
l'.HasBasis p' s' → ((l ⊓ l').NeBot ↔ ∀ ⦃i : ι⦄, p i → ∀ ⦃i' : ι'⦄, p' i' → (s i
 ∩ s' i').Nonempty)
参数：(l ⊓ l').NeBot ↔ ∀ ⦃i : ι⦄, p i → ∀ ⦃i' : ι'⦄, p' i' → (s i ∩ s' i').Nonempty
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `Filter.HasBasis.inf'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l
 l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set
 α},   l.H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃i'⦄, p' i' → (s i ∩ s' i').Nonempty :=
  (hl.inf' hl').neBot_iff.trans <| by simp [@forall_comm _ ι']
/-
**Filter.HasBasis.inf_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l l' : Filter α} {p : ι → Prop} {s : ι → 
Set α},   l.HasBasis p s → ((l ⊓ l').NeBot ↔ ∀ ⦃i : ι⦄, p i → ∀ ⦃s' : Set α⦄, s'
 ∈ l' → (s i ∩ s').Nonempty)
参数：(l ⊓ l').NeBot ↔ ∀ ⦃i : ι⦄, p i → ∀ ⦃s' : Set α⦄, s' ∈ l' → (s i ∩ s').Nonemp
ty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_basis_neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι'
 : Sort u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}  
 {s' : ι' → Set α},   l.H…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃s'⦄, s' ∈ l' → (s i ∩ s').Nonempty :=
  hl.inf_basis_neBot_iff l'.basis_sets
/-
**Filter.HasBasis.inf_principal_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasB
asis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {t : Set α}, (l ⊓ Filter.principal t).NeBot ↔ ∀ ⦃i : ι
⦄, p i → (s i ∩ t).Nonempty
参数：l ⊓ Filter.principal t。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
-/
theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄, p i → (s i ∩ t).Nonempty :=
  (hl.inf_principal t).neBot_iff
/-
**Filter.HasBasis.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l l' : Filter α} {p : ι →
 Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set α},   l.HasBasis p s → 
l'.HasBasis p' s' → (Disjoint l l' ↔ ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s'
 i'))
参数：Disjoint l l' ↔ ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.inf_basis_neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι'
 : Sort u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}  
 {s' : ι' → Set α},   l.H…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  not_iff_not.mp <| by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]
/-
**Filter._root_.Disjoint.exists_mem_filter_basis** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h
/-
**Filter.inf_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_neBot_iff : NeBot (l ⊓ l') ↔ forall ⦃s : Set α⦄, s in l -> forall ⦃s'⦄
, s' in l' -> (s inter s').Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l l' : F
ilter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ((l ⊓ l').NeBot ↔ ∀ 
⦃i : ι⦄, p i → ∀ ⦃s…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ ∀ ⦃s : Set α⦄, s ∈ l → ∀ ⦃s'⦄, s' ∈ l' → (s ∩ s').Nonempty :=
  l.basis_sets.inf_neBot_iff
/-
**Filter.inf_principal_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ forall U in l, (U 
inter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_principal_neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4}
 {l : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {t : Set α}
, (l ⊓ Filter.principal t).Ne…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).Nonempty :=
  l.basis_sets.inf_principal_neBot_iff
/-
**Filter.mem_iff_inf_principal_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s in f ↔ f ⊓ 𝓟 sᶜ
 = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.inf_principal_neBot_iff`：inf_principal_neBot_iff {s : Set α} : Ne
Bot (l ⊓ 𝓟 s) ↔ forall U in l, (U inter s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_compl_nonempty_iff`：inter_compl_nonempty_iff {s t : Set α} : (
s inter tᶜ).Nonempty ↔ ¬s subseteq t
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
-/
theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∈ f ↔ f ⊓ 𝓟 sᶜ = ⊥ := by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
      inter_compl_nonempty_iff.2 fun hts => hs <| mem_of_superset ht hts⟩
/-
**Filter.notMem_iff_inf_principal_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：notMem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot 
(f ⊓ 𝓟 sᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Filter.mem_iff_inf_principal_compl`：mem_iff_inf_principal_compl {f : Fil
ter α} {s : Set α} : s in f ↔ f ⊓ 𝓟 sᶜ = ⊥
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
-/
theorem notMem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ) :=
  (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm

@[simp]
/-
**Filter.disjoint_principal_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ s
ᶜ in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_iff_inf_principal_compl`：mem_iff_inf_principal_compl {f : Fil
ter α} {s : Set α} : s in f ↔ f ⊓ 𝓟 sᶜ = ⊥
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ ∈ f := by
  rw [mem_iff_inf_principal_compl, compl_compl, disjoint_iff]

@[simp]
/-
**Filter.disjoint_principal_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ
 in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ ∈ f := by
  rw [disjoint_comm, disjoint_principal_right]

@[simp high] -- This should fire before `disjoint_principal_left` and `disjoint_principal_right`.
/-
**Filter.disjoint_principal_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoi
nt s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : s s
ubseteq tᶜ ↔ Disjoint t s
· 使用定理 `Filter.disjoint_principal_left`：disjoint_principal_left {f : Filter α} {
s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ in f
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  rw [← subset_compl_iff_disjoint_left, disjoint_principal_left, mem_principal]

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal

@[simp]
/-
**Filter.disjoint_pure_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x !
= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x ≠ y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]
/-
**Filter.HasBasis.disjoint_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l l' : Filter α} {p : ι → Prop} {s : ι → 
Set α},   l.HasBasis p s → (Disjoint l l' ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l')
参数：Disjoint l l' ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' := by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]
/-
**Filter.HasBasis.disjoint_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`
。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l l' : Filter α} {p : ι → Prop} {s : ι → 
Set α},   l.HasBasis p s → (Disjoint l' l ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l')
参数：Disjoint l' l ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
-/
theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' :=
  disjoint_comm.trans h.disjoint_iff_left
/-
**Filter.le_iff_forall_inf_principal_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_iff_forall_inf_principal_compl {f g : Filter α} : f <= g ↔ forall V in 
g, f ⊓ 𝓟 Vᶜ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Filter.mem_iff_inf_principal_compl`：mem_iff_inf_principal_compl {f : Fil
ter α} {s : Set α} : s in f ↔ f ⊓ 𝓟 sᶜ = ⊥
-/
theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 Vᶜ = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl
/-
**Filter.inf_neBot_iff_frequently_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_neBot_iff_frequently_left {f g : Filter α} : NeBot (f ⊓ g) ↔ forall {p
 : α -> Prop}, (forallᶠ x in f, p x) -> existsᶠ x in g, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x := by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl
/-
**Filter.inf_neBot_iff_frequently_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_neBot_iff_frequently_right {f g : Filter α} : NeBot (f ⊓ g) ↔ forall {
p : α -> Prop}, (forallᶠ x in g, p x) -> existsᶠ x in f, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Filter.inf_neBot_iff_frequently_left`：inf_neBot_iff_frequently_left {f g
 : Filter α} : NeBot (f ⊓ g) ↔ forall {p : α -> Prop}, (forallᶠ x in f, p x) -> 
existsᶠ x in g, p x
-/
theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x := by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left
/-
**Filter.HasBasis.eq_biInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter.principal (s i)
参数：_ : p i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_biInf_of_mem_iff_exists_mem`：eq_biInf_of_mem_iff_exists_mem {f
 : ι -> Filter α} {p : ι -> Prop} {l : Filter α} (h : forall {s}, s in l ↔ exist
s i, p i ∧ s in f i) : l = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.eq_biInf (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal]
/-
**Filter.HasBasis.eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {s : ι → Set α},   l.HasBas
is (fun x => True) s → l = ⨅ i, Filter.principal (s i)
参数：fun x => True；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_true`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : True → α}, i
Inf s = s trivial
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
-/
theorem HasBasis.eq_iInf (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [iInf_true] using h.eq_biInf
/-
**Filter.hasBasis_iInf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_iInf_principal {s : ι -> Set α} (h : Directed (· >= ·) s) [Nonemp
ty ι] : (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s
参数：h : Directed (· >= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem hasBasis_iInf_principal {s : ι → Set α} (h : Directed (· ≥ ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨fun t => by
    simpa only [true_and] using! mem_iInf_of_directed (h.mono_comp _ monotone_principal.dual) t⟩
/-
**Filter.hasBasis_biInf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_biInf_principal {s : β -> Set α} {S : Set β} (h : DirectedOn (s ⁻
¹'o (· >= ·)) S) (ne : S.Nonempty) : (⨅ i in S, 𝓟 (s i)).HasBasis (fun i => i in
 S) s
参数：h : DirectedOn (s ⁻¹'o (· >= ·)) S；ne : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_biInf_of_directed`：mem_biInf_of_directed {f : β -> Filter α} 
{s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s) (ne : s.Nonempty) {t : Set α} :
 (t in ⨅ i in s, f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `directed_comp`：directed_comp {ι} {f : ι -> β} {g : β -> α} : Directed r 
(g ∘ f) ↔ Directed (g ⁻¹'o r) f
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem hasBasis_biInf_principal {s : β → Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· ≥ ·)) S)
    (ne : S.Nonempty) : (⨅ i ∈ S, 𝓟 (s i)).HasBasis (fun i => i ∈ S) s :=
  ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed, ← directed_comp] at h ⊢
    refine h.mono_comp _ ?_
    exact fun _ _ => principal_mono.2⟩
/-
**Filter.hasBasis_biInf_principal'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_biInf_principal' {ι : Type*} {p : ι -> Prop} {s : ι -> Set α} (h 
: forall i, p i -> forall j, p j -> exists k, p k ∧ s k subseteq s i ∧ s k subse
teq s j) (ne : exists i, p i) : (⨅ (i) (_ : p i), 𝓟 (s i)).HasBasis p s
参数：h : forall i, p i -> forall j, p j -> exists k, p k ∧ s k subseteq s i ∧ s k 
subseteq s j；ne : exists i, p i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_biInf_principal`：hasBasis_biInf_principal {s : β -> Set 
α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· >= ·)) S) (ne : S.Nonempty) : (⨅ i in 
S, 𝓟 (s i)).HasBasis …
-/
theorem hasBasis_biInf_principal' {ι : Type*} {p : ι → Prop} {s : ι → Set α}
    (h : ∀ i, p i → ∀ j, p j → ∃ k, p k ∧ s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
    (⨅ (i) (_ : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_biInf_principal h ne
/-
**Filter.HasBasis.map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l : Filter α} {p : ι → Pro
p} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filter.map f l).HasBasis p f
un i => f '' s i
参数：f : α → β；Filter.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.map (f : α → β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩
/-
**Filter.HasBasis.comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l : Filter α} {p : ι → Pro
p} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Filter.comap f l).HasBasis p
 fun i => f ⁻¹' s i
参数：f : β → α；Filter.comap f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
-/
theorem HasBasis.comap (f : β → α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
    exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h <| by rwa [mem_preimage, hx]⟩⟩
/-
**Filter.comap_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_hasBasis (f : α -> β) (l : Filter β) : HasBasis (comap f l) (fun s :
 Set β => s in l) fun s => f ⁻¹' s
参数：f : α -> β；l : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
-/
theorem comap_hasBasis (f : α → β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s ∈ l) fun s => f ⁻¹' s :=
  ⟨fun _ => mem_comap⟩
/-
**Filter.HasBasis.forall_mem_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → ∀ {x : α}, (∀ t ∈ l, x ∈ t) ↔ ∀ (i : ι), p i → x ∈ s i
参数：∀ t ∈ l, x ∈ t；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i := by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩
/-
**Filter.HasBasis.biInf_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l : Filter α} {p : ι → Pro
p} {s : ι → Set α} [inst : CompleteLattice β]   {f : Set α → β}, l.HasBasis p s 
→ Monotone f → ⨅ t ∈ l, f t = ⨅ i, ⨅ (_ : p i), f (s i)
参数：_ : p i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
-/
protected theorem HasBasis.biInf_mem [CompleteLattice β] {f : Set α → β} (h : HasBasis l p s)
    (hf : Monotone f) : ⨅ t ∈ l, f t = ⨅ (i) (_ : p i), f (s i) :=
  le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi)) <|
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)
/-
**Filter.HasBasis.biInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l : Filter α} {p : ι → Pro
p} {s : ι → Set α} {f : Set α → Set β},   l.HasBasis p s → Monotone f → ⋂ t ∈ l,
 f t = ⋂ i, ⋂ (_ : p i), f (s i)
参数：_ : p i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.biInf_mem`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4
} {l : Filter α} {p : ι → Prop} {s : ι → Set α} [inst : CompleteLattice β]   {f 
: Set α → β}, l…
-/
protected theorem HasBasis.biInter_mem {f : Set α → Set β} (h : HasBasis l p s) (hf : Monotone f) :
    ⋂ t ∈ l, f t = ⋂ (i) (_ : p i), f (s i) :=
  h.biInf_mem hf
/-
**Filter.HasBasis.ker** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → l.ker = ⋂ i, ⋂ (_ : p i), s i
参数：_ : p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Filter.HasBasis.biInter_mem`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {f : Set α → Set β},   l.HasBa
sis p s → Monoton…
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
protected theorem HasBasis.ker (h : HasBasis l p s) : l.ker = ⋂ (i) (_ : p i), s i :=
  sInter_eq_biInter.trans <| h.biInter_mem monotone_id

variable {ι'' : Type*} [Preorder ι''] (l) (s'' : ι'' → Set α)

/-- `IsAntitoneBasis s` means the image of `s` is a filter basis such that `s` is decreasing. -/
/-
**Filter.IsAntitoneBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {ι'' : Type u_6} → [Preorder ι''] → (ι'' → Set α) → Prop
参数：ι'' → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAntitoneBasis s` means the image of `s` is a filter basis such that `s` is de
creasing.
-/
structure IsAntitoneBasis : Prop extends IsBasis (fun _ => True) s'' where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s''

/-- We say that a filter `l` has an antitone basis `s : ι → Set α`, if `t ∈ l` if and only if `t`
includes `s i` for some `i`, and `s` is decreasing. -/
/-
**Filter.HasAntitoneBasis** 是 Mathlib 中的一个结构，位于命名空间 `Filter`。
形式化陈述：HasAntitoneBasis (l : Filter α) (s : ι'' -> Set α) : Prop extends HasBasis
 l (fun _ => True) s where /-- The sequence of sets is antitone. -/ protected an
titone : Antitone s  protected theorem HasAntitoneBasis.map {l : Filter α} {s : 
ι'' -> Set α} (hf : HasAntitoneBasis l s) (m : α -> β) : HasAntitoneBasis (map m
 l) (m '' s ·)
参数：l : Filter α；s : ι'' -> Set α。
继承自：HasBasis l (fun _ => True) s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a filter `l` has an antitone basis `s : ι → Set α`, if `t ∈ l` if an
d only if `t`
includes `s i` for some `i`, and `s` is decreasing.
-/
structure HasAntitoneBasis (l : Filter α) (s : ι'' → Set α) : Prop
    extends HasBasis l (fun _ => True) s where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s
/-
**Filter.HasAntitoneBasis.map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasAntitoneBasis
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι'' : Type u_6} [inst : Preorder ι''] {l 
: Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → ∀ (m : α → β), (Filter.m
ap m l).HasAntitoneBasis fun x => m '' s x
参数：m : α → β；Filter.map m l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
-/
protected theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : α → β) : HasAntitoneBasis (map m l) (m '' s ·) :=
  ⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_mono <| hf.2 h⟩
/-
**Filter.HasAntitoneBasis.comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasAntitoneBas
is`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι'' : Type u_6} [inst : Preorder ι''] {l 
: Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → ∀ (m : β → α), (Filter.c
omap m l).HasAntitoneBasis fun x => m ⁻¹' s x
参数：m : β → α；Filter.comap m l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
-/
protected theorem HasAntitoneBasis.comap {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : β → α) : HasAntitoneBasis (comap m l) (m ⁻¹' s ·) :=
  ⟨hf.1.comap _, fun _ _ h ↦ preimage_mono (hf.2 h)⟩
/-
**Filter.HasAntitoneBasis.iInf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasAn
titoneBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_7} [inst : Preorder ι] [Nonempty ι] [IsDirect
edOrder ι] {s : ι → Set α},   Antitone s → (⨅ i, Filter.principal (s i)).HasAnti
toneBasis s
参数：⨅ i, Filter.principal (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_iInf_principal`：hasBasis_iInf_principal {s : ι -> Set α}
 (h : Directed (· >= ·) s) [Nonempty ι] : (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True
) s
· 使用定理 `Antitone.directed_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [IsDirectedOrder α] [inst_2 : Preorder β] {f : α → β},   Antitone f → Directed
 (fun x1 x…
-/
lemma HasAntitoneBasis.iInf_principal {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {s : ι → Set α} (hs : Antitone s) : (⨅ i, 𝓟 (s i)).HasAntitoneBasis s :=
  ⟨hasBasis_iInf_principal hs.directed_ge, hs⟩

end SameType

section TwoTypes

variable {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β} {pb : ι' → Prop}
  {sb : ι' → Set β} {f : α → β}

/-
**Filter.HasBasis.tendsto_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {la : Filter α} {pa : ι → P
rop} {sa : ι → Set α} {lb : Filter β}   {f : α → β}, la.HasBasis pa sa → (Filter
.Tendsto f la lb ↔ ∀ t ∈ lb, ∃ i, pa i ∧ Set.MapsTo f (sa i) t)
参数：Filter.Tendsto f la lb ↔ ∀ t ∈ lb, ∃ i, pa i ∧ Set.MapsTo f (sa i) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.le_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l l' : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l ≤ l' ↔ ∀ t ∈ l', ∃ i, p 
i ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t := by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl
/-
**Filter.HasBasis.tendsto_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι' : Sort u_5} {la : Filter α} {lb : Filt
er β} {pb : ι' → Prop} {sb : ι' → Set β}   {f : α → β}, lb.HasBasis pb sb → (Fil
ter.Tendsto f la lb ↔ ∀ (i : ι'), pb i → ∀ᶠ (x : α) in la, f x ∈ sb i)
参数：Filter.Tendsto f la lb ↔ ∀ (i : ι'), pb i → ∀ᶠ (x : α) in la, f x ∈ sb i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i := by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]
/-
**Filter.HasBasis.tendsto_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {ι' : Sort u_5} {la : Filte
r α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Filter β} {pb : ι' → Prop} {sb : ι
' → Set β} {f : α → β},   la.HasBasis pa sa →     lb.HasBasis pb sb → (Filter.Te
ndsto f la lb ↔ ∀ (ib : ι'), pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x ∈ sb ib)
参数：Filter.Tendsto f la lb ↔ ∀ (ib : ι'), pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x 
∈ sb ib。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ ib, pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x ∈ sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]
/-
**Filter.Tendsto.basis_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {la : Filter α} {pa : ι → P
rop} {sa : ι → Set α} {lb : Filter β}   {f : α → β}, Filter.Tendsto f la lb → la
.HasBasis pa sa → ∀ t ∈ lb, ∃ i, pa i ∧ Set.MapsTo f (sa i) t
参数：sa i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
-/
theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t :=
  hla.tendsto_left_iff.1 H
/-
**Filter.Tendsto.basis_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι' : Sort u_5} {la : Filter α} {lb : Filt
er β} {pb : ι' → Prop} {sb : ι' → Set β}   {f : α → β}, Filter.Tendsto f la lb →
 lb.HasBasis pb sb → ∀ (i : ι'), pb i → ∀ᶠ (x : α) in la, f x ∈ sb i
参数：i : ι'；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
-/
theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i :=
  hlb.tendsto_right_iff.1 H
/-
**Filter.Tendsto.basis_both** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {ι' : Sort u_5} {la : Filte
r α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Filter β} {pb : ι' → Prop} {sb : ι
' → Set β} {f : α → β},   Filter.Tendsto f la lb →     la.HasBasis pa sa → lb.Ha
sBasis pb sb → ∀ (ib : ι'), pb ib → ∃ ia, pa ia ∧ Set.MapsTo f (sa ia) (sb ib)
参数：ib : ι'；sa ia；sb ib。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
-/
theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    ∀ ib, pb ib → ∃ ia, pa ia ∧ MapsTo f (sa ia) (sb ib) :=
  (hla.tendsto_iff hlb).1 H
/-
**Filter.HasBasis.prod_pprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {ι' : Sort u_5} {la : Filte
r α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Filter β} {pb : ι' → Prop} {sb : ι
' → Set β},   la.HasBasis pa sa →     lb.HasBasis pb sb → (la ×ˢ lb).HasBasis (f
un i => pa i.fst ∧ pb i.snd) fun i => sa i.fst ×ˢ sb i.snd
参数：la ×ˢ lb；fun i => pa i.fst ∧ pb i.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l
 l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set
 α},   l.H…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem HasBasis.prod_pprod (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)
/-
**Filter.HasBasis.prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {ι : Type 
u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} {pb : ι' → Prop} {sb : ι
' → Set β},   la.HasBasis pa sa → lb.HasBasis pb sb → (la ×ˢ lb).HasBasis (fun i
 => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2
参数：la ×ˢ lb；fun i => pa i.1 ∧ pb i.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf`：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {
ι' : Type u_7} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem HasBasis.prod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)
/-
**Filter.HasBasis.principal_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι' : Sort u_5} {lb : Filter β} {pb : ι' →
 Prop} {sb : ι' → Set β} (sa : Set α),   lb.HasBasis pb sb → (Filter.principal s
a ×ˢ lb).HasBasis pb fun x => sa ×ˢ sb x
参数：sa : Set α；Filter.principal sa ×ˢ lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.HasBasis.principal_inf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (Filter
.principal s' ⊓ l).…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
protected theorem HasBasis.principal_prod (sa : Set α) (h : lb.HasBasis pb sb) :
    (𝓟 sa ×ˢ lb).HasBasis pb (sa ×ˢ sb ·) := by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.snd).principal_inf _
/-
**Filter.HasBasis.prod_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {la : Filter α} {pa : ι → P
rop} {sa : ι → Set α},   la.HasBasis pa sa → ∀ (sb : Set β), (la ×ˢ Filter.princ
ipal sb).HasBasis pa fun x => sa x ×ˢ sb
参数：sb : Set β；la ×ˢ Filter.principal sb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
protected theorem HasBasis.prod_principal (h : la.HasBasis pa sa) (sb : Set β) :
    (la ×ˢ 𝓟 sb).HasBasis pa (sa · ×ˢ sb) := by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.fst).inf_principal _
/-
**Filter.HasBasis.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι' : Sort u_5} {lb : Filter β} {pb : ι' →
 Prop} {sb : ι' → Set β},   lb.HasBasis pb sb → (⊤ ×ˢ lb).HasBasis pb fun x => S
et.univ ×ˢ sb x
参数：⊤ ×ˢ lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Filter.HasBasis.principal_prod`：∀ {α : Type u_1} {β : Type u_2} {ι' : So
rt u_5} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β} (sa : Set α),   lb.Ha
sBasis pb sb → (Filt…
-/
protected theorem HasBasis.top_prod (h : lb.HasBasis pb sb) :
    (⊤ ×ˢ lb : Filter (α × β)).HasBasis pb (univ ×ˢ sb ·) := by
  simpa only [principal_univ] using h.principal_prod univ
/-
**Filter.HasBasis.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {la : Filter α} {pa : ι → P
rop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ ⊤).HasBasis pa fun x => sa x
 ×ˢ Set.univ
参数：la ×ˢ ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Filter.HasBasis.prod_principal`：∀ {α : Type u_1} {β : Type u_2} {ι : Sor
t u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → ∀
 (sb : Set β), (la ×…
-/
protected theorem HasBasis.prod_top (h : la.HasBasis pa sa) :
    (la ×ˢ ⊤ : Filter (α × β)).HasBasis pa (sa · ×ˢ univ) := by
  simpa only [principal_univ] using h.prod_principal univ
/-
**Filter.HasBasis.prod_same_index** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {la : Filter α} {sa : ι → S
et α} {lb : Filter β} {p : ι → Prop}   {sb : ι → Set β},   la.HasBasis p sa →   
  lb.HasBasis p sb →       (∀ {i j : ι}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb
 k ⊆ sb j) → (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i
参数：∀ {i j : ι}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j；la ×ˢ lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod_pprod`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_
4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Filt
er β} {pb : ι' →…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem HasBasis.prod_same_index {p : ι → Prop} {sb : ι → Set β} (hla : la.HasBasis p sa)
    (hlb : lb.HasBasis p sb) (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i := by
  simp only [hasBasis_iff, (hla.prod_pprod hlb).mem_iff]
  refine fun t => ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j ⊆ t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩
/-
**Filter.HasBasis.prod_same_index_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {ι : Type 
u_6} [inst : LinearOrder ι] {p : ι → Prop}   {sa : ι → Set α} {sb : ι → Set β}, 
  la.HasBasis p sa →     lb.HasBasis p sb → MonotoneOn sa {i | p i} → MonotoneOn
 sb {i | p i} → (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i
参数：la ×ˢ lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.prod_same_index`：∀ {α : Type u_1} {β : Type u_2} {ι : So
rt u_4} {la : Filter α} {sa : ι → Set α} {lb : Filter β} {p : ι → Prop}   {sb : 
ι → Set β},   la.HasB…
· 使用引理 `min_rec'`：min_rec' (p : α -> Prop) (ha : p a) (hb : p b) : p (min a b)
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem HasBasis.prod_same_index_mono {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
    ⟨min i j, this, hsa this hi <| min_le_left _ _, hsb this hj <| min_le_right _ _⟩
/-
**Filter.HasBasis.prod_same_index_anti** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {ι : Type 
u_6} [inst : LinearOrder ι] {p : ι → Prop}   {sa : ι → Set α} {sb : ι → Set β}, 
  la.HasBasis p sa →     lb.HasBasis p sb → AntitoneOn sa {i | p i} → AntitoneOn
 sb {i | p i} → (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i
参数：la ×ˢ lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.prod_same_index_mono`：∀ {α : Type u_1} {β : Type u_2} {l
a : Filter α} {lb : Filter β} {ι : Type u_6} [inst : LinearOrder ι] {p : ι → Pro
p}   {sa : ι → Set α} {sb …
· 使用定理 `AntitoneOn.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (f ∘ 
⇑OrderDual…
-/
theorem HasBasis.prod_same_index_anti {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left
/-
**Filter.HasBasis.prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → 
Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis pa fun i => sa i ×ˢ sa i
参数：la ×ˢ la。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.prod_same_index`：∀ {α : Type u_1} {β : Type u_2} {ι : So
rt u_4} {la : Filter α} {sa : ι → Set α} {lb : Filter β} {p : ι → Prop}   {sb : 
ι → Set β},   la.HasB…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ˢ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))
/-
**Filter.mem_prod_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_prod_self_iff {s} : s in la ×ˢ la ↔ exists t in la, t ×ˢ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem mem_prod_self_iff {s} : s ∈ la ×ˢ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s :=
  la.basis_sets.prod_self.mem_iff
/-
**Filter.eventually_prod_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventually_prod_self_iff {r : α -> α -> Prop} : (forallᶠ x in la ×ˢ la, r 
x.1 x.2) ↔ exists t in la, forall x in t, forall y in t, r x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.mem_prod_self_iff`：mem_prod_self_iff {s} : s in la ×ˢ la ↔ exists
 t in la, t ×ˢ t subseteq s
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
lemma eventually_prod_self_iff {r : α → α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x.1 x.2) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r x y :=
  mem_prod_self_iff.trans <| by simp only [prod_subset_iff, mem_ofPred_eq]

/-- A version of `eventually_prod_self_iff` that is more suitable for forward rewriting. -/
/-
**Filter.eventually_prod_self_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventually_prod_self_iff' {r : α × α -> Prop} : (forallᶠ x in la ×ˢ la, r 
x) ↔ exists t in la, forall x in t, forall y in t, r (x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Filter.eventually_prod_self_iff`：eventually_prod_self_iff {r : α -> α ->
 Prop} : (forallᶠ x in la ×ˢ la, r x.1 x.2) ↔ exists t in la, forall x in t, for
all y in t, r x y

--- 原说明 ---
A version of `eventually_prod_self_iff` that is more suitable for forward rewrit
ing.
-/
lemma eventually_prod_self_iff' {r : α × α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r (x, y) :=
  Iff.symm eventually_prod_self_iff.symm
/-
**Filter.HasAntitoneBasis.prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasAntitoneBasi
s`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_6} [inst : LinearOrder ι] {f :
 Filter α} {g : Filter β} {s : ι → Set α}   {t : ι → Set β}, f.HasAntitoneBasis 
s → g.HasAntitoneBasis t → (f ×ˢ g).HasAntitoneBasis fun n => s n ×ˢ t n
参数：f ×ˢ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.prod_same_index_anti`：∀ {α : Type u_1} {β : Type u_2} {l
a : Filter α} {lb : Filter β} {ι : Type u_6} [inst : LinearOrder ι] {p : ι → Pro
p}   {sa : ι → Set α} {sb …
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
· 使用定理 `Antitone.set_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: Preorder α] {f : α → Set β} {g : α → Set γ},   Antitone f → Antitone g → Antit
one fun…
-/
theorem HasAntitoneBasis.prod {ι : Type*} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι → Set α} {t : ι → Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ˢ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩
/-
**Filter.HasBasis.coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {ι : Type 
u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} {pb : ι' → Prop} {sb : ι
' → Set β},   la.HasBasis pa sa →     lb.HasBasis pb sb →       (la.coprod lb).H
asBasis (fun i => pa i.1 ∧ pb i.2) fun i => Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' s
b i.2
参数：la.coprod lb；fun i => pa i.1 ∧ pb i.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.sup`：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {
ι' : Type u_7} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem HasBasis.coprod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)

end TwoTypes

/-
**Filter.map_sigma_mk_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_sigma_mk_comap {π : α -> Type*} {π' : β -> Type*} {f : α -> β} (hf : F
unction.Injective f) (g : forall a, π a -> π' (f a)) (a : α) (l : Filter (π' (f 
a))) : map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (
f a)) l)
参数：hf : Function.Injective f；g : forall a, π a -> π' (f a)；a : α；l : Filter (π' 
(f a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_sigmaMk_preimage_sigmaMap`：image_sigmaMk_preimage_sigmaMap {β 
: ι' -> Type*} {f : ι -> ι'} (hf : Function.Injective f) (g : forall i, α i -> β
 (f i)) (i : ι) (s : Set …
-/
theorem map_sigma_mk_comap {π : α → Type*} {π' : β → Type*} {f : α → β}
    (hf : Function.Injective f) (g : ∀ a, π a → π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) := by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert! ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf

end Filter

