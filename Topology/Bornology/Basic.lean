/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.Filter.Cofinite

/-!
# Basic theory of bornology

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter.  This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `Bornology.ofBounded`,
`IsBounded.union`, `IsBounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `Bornology α`: a class consisting of `cobounded : Filter α` and a proof that this filter
  contains the `cofinite` filter.
- `Bornology.IsCobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : Set α`, one should prefer `Bornology.IsCobounded s` over `s ∈ cobounded α`.
- `bornology.IsBounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `Bornology.IsBounded s` over `sᶜ ∈ cobounded α`.
- `BoundedSpace α`: a class extending `Bornology α` with the condition
  `Bornology.IsBounded (Set.univ : Set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/

@[expose] public section


open Set Filter

variable {ι α β : Type*}

/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `Bornology.ofBounded`
and `Bornology.ext_iff_isBounded` -/
/-
**Bornology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **bornology** on a type `α` is a filter of cobounded sets which contains the c
ofinite filter.
Such spaces are equivalently specified by their bounded sets, see `Bornology.ofB
ounded`
and `Bornology.ext_iff_isBounded`
-/
class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. -/
  cobounded (α) : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. -/
  le_cofinite (α) : cobounded ≤ cofinite

@[ext]
/-
**Bornology.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bornology.ext (t t' : Bornology α) (h_cobounded : @Bornology.cobounded α t
 = @Bornology.cobounded α t') : t = t'
参数：t t' : Bornology α；h_cobounded : @Bornology.cobounded α t = @Bornology.coboun
ded α t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Bornology.ext (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  cases t'
  congr

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps, instance_reducible]
/-
**Bornology.ofBounded** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Bornology.ofBounded {α : Type*} (B : Set (Set α)) (empty_mem : ∅ in B) (su
bset_mem : forall s₁ in B, forall s₂ subseteq s₁, s₂ in B) (union_mem : forall s
₁ in B, forall s₂ in B, s₁ union s₂ in B) (singleton_mem : forall x, {x} in B) :
 Bornology α where cobounded
参数：B : Set (Set α)；empty_mem : ∅ in B；subset_mem : forall s₁ in B, forall s₂ sub
seteq s₁, s₂ in B；union_mem : forall s₁ in B, forall s₂ in B, s₁ union s₂ in B；s
ingleton_mem : forall x, {x} in B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions.
-/
def Bornology.ofBounded {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)
    (union_mem : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ ∪ s₂ ∈ B)
    (singleton_mem : ∀ x, {x} ∈ B) : Bornology α where
  cobounded := comk (· ∈ B) empty_mem subset_mem union_mem
  le_cofinite := by simpa [le_cofinite_iff_compl_singleton_mem]

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps! cobounded, instance_reducible]
/-
**Bornology.ofBounded'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Bornology.ofBounded' {α : Type*} (B : Set (Set α)) (empty_mem : ∅ in B) (s
ubset_mem : forall s₁ in B, forall s₂ subseteq s₁, s₂ in B) (union_mem : forall 
s₁ in B, forall s₂ in B, s₁ union s₂ in B) (sUnion_univ : ⋃₀ B = univ) : Bornolo
gy α
参数：B : Set (Set α)；empty_mem : ∅ in B；subset_mem : forall s₁ in B, forall s₂ sub
seteq s₁, s₂ in B；union_mem : forall s₁ in B, forall s₂ in B, s₁ union s₂ in B；s
Union_univ : ⋃₀ B = univ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions.
-/
def Bornology.ofBounded' {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)
    (union_mem : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ ∪ s₂ ∈ B)
    (sUnion_univ : ⋃₀ B = univ) :
    Bornology α :=
  Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
namespace Bornology

section

/-- `IsCobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
/-
**Bornology.IsCobounded** 是 Mathlib 中的一个定义，位于命名空间 `Bornology`。
形式化陈述：IsCobounded [Bornology α] (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsCobounded` is the predicate that `s` is in the filter of cobounded sets in th
e ambient
bornology on `α`
-/
def IsCobounded [Bornology α] (s : Set α) : Prop :=
  s ∈ cobounded α

/-- `IsBounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
/-
**Bornology.IsBounded** 是 Mathlib 中的一个定义，位于命名空间 `Bornology`。
形式化陈述：IsBounded [Bornology α] (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsBounded` is the predicate that `s` is bounded relative to the ambient bornolo
gy on `α`.
-/
def IsBounded [Bornology α] (s : Set α) : Prop :=
  IsCobounded sᶜ

variable {_ : Bornology α} {s t : Set α} {x : α}
/-
**Bornology.isCobounded_def** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_def {s : Set α} : IsCobounded s ↔ s in cobounded α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCobounded_def {s : Set α} : IsCobounded s ↔ s ∈ cobounded α :=
  Iff.rfl
/-
**Bornology.isBounded_def** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in cobounded α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_def {s : Set α} : IsBounded s ↔ sᶜ ∈ cobounded α :=
  Iff.rfl

@[simp]
/-
**Bornology.isBounded_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_compl_iff : IsBounded sᶜ ↔ IsCobounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `Bornology.isCobounded_def`：isCobounded_def {s : Set α} : IsCobounded s ↔
 s in cobounded α
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_compl_iff : IsBounded sᶜ ↔ IsCobounded s := by
  rw [isBounded_def, isCobounded_def, compl_compl]

@[simp]
/-
**Bornology.isCobounded_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_compl_iff : IsCobounded sᶜ ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCobounded_compl_iff : IsCobounded sᶜ ↔ IsBounded s :=
  Iff.rfl

alias ⟨IsBounded.of_compl, IsCobounded.compl⟩ := isBounded_compl_iff

alias ⟨IsCobounded.of_compl, IsBounded.compl⟩ := isCobounded_compl_iff

@[simp]
/-
**Bornology.isBounded_empty** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_empty : IsBounded (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem isBounded_empty : IsBounded (∅ : Set α) := by
  rw [isBounded_def, compl_empty]
  exact univ_mem
/-
**Bornology.nonempty_of_not_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：nonempty_of_not_isBounded (h : ¬IsBounded s) : s.Nonempty
参数：h : ¬IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Bornology.isBounded_empty`：isBounded_empty : IsBounded (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_not_isBounded (h : ¬IsBounded s) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h isBounded_empty

@[simp]
/-
**Bornology.isBounded_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_singleton : IsBounded ({x} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `Bornology.le_cofinite`：∀ (α : Type u_4) [self : Bornology α], Bornology.
cobounded α ≤ Filter.cofinite
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem isBounded_singleton : IsBounded ({x} : Set α) := by
  rw [isBounded_def]
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite
/-
**Bornology.isBounded_iff_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_iff_forall_mem : IsBounded s ↔ forall x in s, IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Bornology.isBounded_empty`：isBounded_empty : IsBounded (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isBounded_iff_forall_mem : IsBounded s ↔ ∀ x ∈ s, IsBounded s :=
  ⟨fun h _ _ ↦ h, fun h ↦ by
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    exacts [isBounded_empty, h x hx]⟩

@[simp]
/-
**Bornology.isCobounded_univ** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_univ : IsCobounded (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem isCobounded_univ : IsCobounded (univ : Set α) :=
  univ_mem

@[simp]
/-
**Bornology.isCobounded_inter** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_inter : IsCobounded (s inter t) ↔ IsCobounded s ∧ IsCobounded 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem_iff`：inter_mem_iff {s t : Set α} : s inter t in f ↔ s i
n f ∧ t in f
-/
theorem isCobounded_inter : IsCobounded (s ∩ t) ↔ IsCobounded s ∧ IsCobounded t :=
  inter_mem_iff
/-
**Bornology.IsCobounded.inter** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsCobounded`。
形式化陈述：∀ {α : Type u_2} {x : Bornology α} {s t : Set α},   Bornology.IsCobounded 
s → Bornology.IsCobounded t → Bornology.IsCobounded (s ∩ t)
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.isCobounded_inter`：isCobounded_inter : IsCobounded (s inter t)
 ↔ IsCobounded s ∧ IsCobounded t
-/
theorem IsCobounded.inter (hs : IsCobounded s) (ht : IsCobounded t) : IsCobounded (s ∩ t) :=
  isCobounded_inter.2 ⟨hs, ht⟩

@[simp]
/-
**Bornology.isBounded_union** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_union : IsBounded (s union t) ↔ IsBounded s ∧ IsBounded t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBounded_union : IsBounded (s ∪ t) ↔ IsBounded s ∧ IsBounded t := by
  simp only [← isCobounded_compl_iff, compl_union, isCobounded_inter]
/-
**Bornology.IsBounded.union** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_2} {x : Bornology α} {s t : Set α},   Bornology.IsBounded s 
→ Bornology.IsBounded t → Bornology.IsBounded (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.isBounded_union`：isBounded_union : IsBounded (s union t) ↔ IsB
ounded s ∧ IsBounded t
-/
theorem IsBounded.union (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ∪ t) :=
  isBounded_union.2 ⟨hs, ht⟩
/-
**Bornology.IsCobounded.superset** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsCobounde
d`。
形式化陈述：∀ {α : Type u_2} {x : Bornology α} {s t : Set α}, Bornology.IsCobounded s 
→ s ⊆ t → Bornology.IsCobounded t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem IsCobounded.superset (hs : IsCobounded s) (ht : s ⊆ t) : IsCobounded t :=
  mem_of_superset hs ht
/-
**Bornology.IsBounded.subset** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_2} {x : Bornology α} {s t : Set α}, Bornology.IsBounded t → 
s ⊆ t → Bornology.IsBounded s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsCobounded.superset`：∀ {α : Type u_2} {x : Bornology α} {s t 
: Set α}, Bornology.IsCobounded s → s ⊆ t → Bornology.IsCobounded t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
-/
theorem IsBounded.subset (ht : IsBounded t) (hs : s ⊆ t) : IsBounded s :=
  ht.superset (compl_subset_compl.mpr hs)

@[simp]
/-
**Bornology.sUnion_bounded_univ** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：sUnion_bounded_univ : ⋃₀ { s : Set α | IsBounded s } = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sUnion_eq_univ_iff`：sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = un
iv ↔ forall a, exists b in c, a in b
· 使用定理 `Bornology.isBounded_singleton`：isBounded_singleton : IsBounded ({x} : Se
t α)
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem sUnion_bounded_univ : ⋃₀ { s : Set α | IsBounded s } = univ :=
  sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩
/-
**Bornology.IsBounded.insert** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_2} {x : Bornology α} {s : Set α}, Bornology.IsBounded s → ∀ 
(x_1 : α), Bornology.IsBounded (insert x_1 s)
参数：x_1 : α；insert x_1 s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `Bornology.isBounded_singleton`：isBounded_singleton : IsBounded ({x} : Se
t α)
-/
theorem IsBounded.insert (h : IsBounded s) (x : α) : IsBounded (insert x s) :=
  isBounded_singleton.union h

@[simp]
/-
**Bornology.isBounded_insert** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_insert : IsBounded (insert x s) ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Bornology.IsBounded.insert`：∀ {α : Type u_2} {x : Bornology α} {s : Set 
α}, Bornology.IsBounded s → ∀ (x_1 : α), Bornology.IsBounded (insert x_1 s)
-/
theorem isBounded_insert : IsBounded (insert x s) ↔ IsBounded s :=
  ⟨fun h ↦ h.subset (subset_insert _ _), (.insert · x)⟩
/-
**Bornology.comap_cobounded_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：comap_cobounded_le_iff [Bornology β] {f : α -> β} : (cobounded β).comap f 
<= cobounded α ↔ forall ⦃s⦄, IsBounded s -> IsBounded (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.compl`：∀ {α : Type u_2} {x : Bornology α} {s : Set α
}, Bornology.IsBounded s → Bornology.IsCobounded sᶜ
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Bornology.IsCobounded.compl`：∀ {α : Type u_2} {x : Bornology α} {s : Set
 α}, Bornology.IsCobounded s → Bornology.IsBounded sᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem comap_cobounded_le_iff [Bornology β] {f : α → β} :
    (cobounded β).comap f ≤ cobounded α ↔ ∀ ⦃s⦄, IsBounded s → IsBounded (f '' s) := by
  refine
    ⟨fun h s hs => ?_, fun h t ht =>
      ⟨(f '' tᶜ)ᶜ, h <| IsCobounded.compl ht, compl_subset_comm.1 <| subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  rw [subset_compl_comm, ← preimage_compl] at hts
  exact (IsCobounded.compl ht).subset ((image_mono hts).trans <| image_preimage_subset _ _)

end

/-
**Bornology.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：ext_iff' {t t' : Bornology α} : t = t' ↔ forall s, s in @cobounded α t ↔ s
 in @cobounded α t'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Bornology.ext_iff`：∀ {α : Type u_2} {t t' : Bornology α}, t = t' ↔ Borno
logy.cobounded α = Bornology.cobounded α
· 使用定理 `Filter.ext_iff`：∀ {α : Type u_1} {f g : Filter α}, f = g ↔ ∀ (s : Set α)
, s ∈ f ↔ s ∈ g
-/
theorem ext_iff' {t t' : Bornology α} :
    t = t' ↔ ∀ s, s ∈ @cobounded α t ↔ s ∈ @cobounded α t' :=
  Bornology.ext_iff.trans Filter.ext_iff
/-
**Bornology.ext_iff_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：ext_iff_isBounded {t t' : Bornology α} : t = t' ↔ forall s, @IsBounded α t
 s ↔ @IsBounded α t' s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Bornology.ext_iff'`：ext_iff' {t t' : Bornology α} : t = t' ↔ forall s, s
 in @cobounded α t ↔ s in @cobounded α t'
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
-/
theorem ext_iff_isBounded {t t' : Bornology α} :
    t = t' ↔ ∀ s, @IsBounded α t s ↔ @IsBounded α t' s :=
  ext_iff'.trans compl_surjective.forall

variable {s : Set α}
/-
**Bornology.isCobounded_ofBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_me
m sUnion_univ} : @IsCobounded _ (ofBounded B empty_mem subset_mem union_mem sUni
on_univ) s ↔ sᶜ in B
参数：B : Set (Set α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCobounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsCobounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ sᶜ ∈ B :=
  Iff.rfl
/-
**Bornology.isBounded_ofBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem 
sUnion_univ} : @IsBounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_u
niv) s ↔ s in B
参数：B : Set (Set α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `Bornology.ofBounded_cobounded`：∀ {α : Type u_4} (B : Set (Set α)) (empty
_mem : ∅ ∈ B) (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)   (union_mem : ∀ s₁ ∈ B
, ∀ s₂ ∈ B, s₁ ∪ s₂…
· 使用引理 `Filter.compl_mem_comk`：compl_mem_comk {p : Set α -> Prop} {he hmono huni
on s} : sᶜ in comk p he hmono hunion ↔ p s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsBounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ s ∈ B := by
  rw [isBounded_def, ofBounded_cobounded, compl_mem_comk]

variable [Bornology α]
/-
**Bornology.isCobounded_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_biInter {s : Set ι} {f : ι -> Set α} (hs : s.Finite) : IsCobou
nded (⋂ i in s, f i) ↔ forall i in s, IsCobounded (f i)
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
-/
theorem isCobounded_biInter {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_mem hs

@[simp]
/-
**Bornology.isCobounded_biInter_finset** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_biInter_finset (s : Finset ι) {f : ι -> Set α} : IsCobounded (
⋂ i in s, f i) ↔ forall i in s, IsCobounded (f i)
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
-/
theorem isCobounded_biInter_finset (s : Finset ι) {f : ι → Set α} :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_finset_mem s

@[simp]
/-
**Bornology.isCobounded_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_iInter [Finite ι] {f : ι -> Set α} : IsCobounded (⋂ i, f i) ↔ 
forall i, IsCobounded (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
-/
theorem isCobounded_iInter [Finite ι] {f : ι → Set α} :
    IsCobounded (⋂ i, f i) ↔ ∀ i, IsCobounded (f i) :=
  iInter_mem
/-
**Bornology.isCobounded_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isCobounded_sInter {S : Set (Set α)} (hs : S.Finite) : IsCobounded (⋂₀ S) 
↔ forall s in S, IsCobounded s
参数：Set α；hs : S.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.sInter_mem`：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s
 in f ↔ forall U in s, U in f
-/
theorem isCobounded_sInter {S : Set (Set α)} (hs : S.Finite) :
    IsCobounded (⋂₀ S) ↔ ∀ s ∈ S, IsCobounded s :=
  sInter_mem hs
/-
**Bornology.isBounded_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_biUnion {s : Set ι} {f : ι -> Set α} (hs : s.Finite) : IsBounded
 (⋃ i in s, f i) ↔ forall i in s, IsBounded (f i)
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bornology.isCobounded_biInter`：isCobounded_biInter {s : Set ι} {f : ι ->
 Set α} (hs : s.Finite) : IsCobounded (⋂ i in s, f i) ↔ forall i in s, IsCobound
ed (f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBounded_biUnion {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) := by
  simp only [← isCobounded_compl_iff, compl_iUnion, isCobounded_biInter hs]
/-
**Bornology.isBounded_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_biUnion_finset (s : Finset ι) {f : ι -> Set α} : IsBounded (⋃ i 
in s, f i) ↔ forall i in s, IsBounded (f i)
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.isBounded_biUnion`：isBounded_biUnion {s : Set ι} {f : ι -> Set
 α} (hs : s.Finite) : IsBounded (⋃ i in s, f i) ↔ forall i in s, IsBounded (f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem isBounded_biUnion_finset (s : Finset ι) {f : ι → Set α} :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) :=
  isBounded_biUnion s.finite_toSet
/-
**Bornology.isBounded_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_sUnion {S : Set (Set α)} (hs : S.Finite) : IsBounded (⋃₀ S) ↔ fo
rall s in S, IsBounded s
参数：Set α；hs : S.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Bornology.isBounded_biUnion`：isBounded_biUnion {s : Set ι} {f : ι -> Set
 α} (hs : s.Finite) : IsBounded (⋃ i in s, f i) ↔ forall i in s, IsBounded (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_sUnion {S : Set (Set α)} (hs : S.Finite) :
    IsBounded (⋃₀ S) ↔ ∀ s ∈ S, IsBounded s := by rw [sUnion_eq_biUnion, isBounded_biUnion hs]

@[simp]
/-
**Bornology.isBounded_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_iUnion [Finite ι] {s : ι -> Set α} : IsBounded (⋃ i, s i) ↔ fora
ll i, IsBounded (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `Bornology.isBounded_sUnion`：isBounded_sUnion {S : Set (Set α)} (hs : S.F
inite) : IsBounded (⋃₀ S) ↔ forall s in S, IsBounded s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_iUnion [Finite ι] {s : ι → Set α} :
    IsBounded (⋃ i, s i) ↔ ∀ i, IsBounded (s i) := by
  rw [← sUnion_range, isBounded_sUnion (finite_range s), forall_mem_range]
/-
**Bornology.eventually_ne_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Bornology`。
形式化陈述：eventually_ne_cobounded (a : α) : forallᶠ x in cobounded α, x != a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_cofinite_iff_eventually_ne`：le_cofinite_iff_eventually_ne : l 
<= cofinite ↔ forall x, forallᶠ y in l, y != x
· 使用定理 `Bornology.le_cofinite`：∀ (α : Type u_4) [self : Bornology α], Bornology.
cobounded α ≤ Filter.cofinite
-/
lemma eventually_ne_cobounded (a : α) : ∀ᶠ x in cobounded α, x ≠ a :=
  le_cofinite_iff_eventually_ne.1 (le_cofinite _) a

end Bornology

open Bornology

/-
**Filter.HasBasis.disjoint_cobounded_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.disjoint_cobounded_iff [Bornology α] {ι : Sort*} {p : ι ->
 Prop} {s : ι -> Set α} {l : Filter α} (h : l.HasBasis p s) : Disjoint l (coboun
ded α) ↔ exists i, p i ∧ Bornology.IsBounded (s i)
参数：h : l.HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
-/
theorem Filter.HasBasis.disjoint_cobounded_iff [Bornology α] {ι : Sort*} {p : ι → Prop}
    {s : ι → Set α} {l : Filter α} (h : l.HasBasis p s) :
    Disjoint l (cobounded α) ↔ ∃ i, p i ∧ Bornology.IsBounded (s i) :=
  h.disjoint_iff_left
/-
**Filter.disjoint_cobounded_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.disjoint_cobounded_iff [Bornology α] {l : Filter α} : Disjoint l (c
obounded α) ↔ exists s in l, Bornology.IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.disjoint_cobounded_iff`：Filter.HasBasis.disjoint_cobound
ed_iff [Bornology α] {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α} {l : Filter α}
 (h : l.HasBasis p s) : Disj…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem Filter.disjoint_cobounded_iff [Bornology α] {l : Filter α} :
    Disjoint l (cobounded α) ↔ ∃ s ∈ l, Bornology.IsBounded s :=
  l.basis_sets.disjoint_cobounded_iff

alias ⟨Disjoint.exists_isBounded, _⟩ := Filter.disjoint_cobounded_iff
/-
**Bornology.IsBounded.disjoint_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.disjoint_cobounded [Bornology α] {l : Filter α} {s : S
et α} (hs : IsBounded s) (hl : s in l) : Disjoint l (cobounded α)
参数：hs : IsBounded s；hl : s in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.disjoint_cobounded_iff`：Filter.disjoint_cobounded_iff [Bornology 
α] {l : Filter α} : Disjoint l (cobounded α) ↔ exists s in l, Bornology.IsBounde
d s
-/
theorem Bornology.IsBounded.disjoint_cobounded [Bornology α]
    {l : Filter α} {s : Set α} (hs : IsBounded s) (hl : s ∈ l) :
    Disjoint l (cobounded α) :=
  l.disjoint_cobounded_iff.mpr ⟨s, hl, hs⟩
/-
**Set.Finite.isBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isBounded [Bornology α] {s : Set α} (hs : s.Finite) : IsBounded
 s
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.le_cofinite`：∀ (α : Type u_4) [self : Bornology α], Bornology.
cobounded α ≤ Filter.cofinite
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
-/
theorem Set.Finite.isBounded [Bornology α] {s : Set α} (hs : s.Finite) : IsBounded s :=
  Bornology.le_cofinite α hs.compl_mem_cofinite

nonrec lemma Filter.Tendsto.eventually_ne_cobounded [Bornology α] {f : β → α} {l : Filter β}
    (h : Tendsto f l (cobounded α)) (a : α) : ∀ᶠ x in l, f x ≠ a :=
  h.eventually <| eventually_ne_cobounded a
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bornology PUnit :=
  ⟨⊥, bot_le⟩

/-- The cofinite filter as a bornology -/
/-
**Bornology.cofinite** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Bornology.cofinite : Bornology α where cobounded
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofinite filter as a bornology
-/
abbrev Bornology.cofinite : Bornology α where
  cobounded := Filter.cofinite
  le_cofinite := le_rfl

/-- A space with a `Bornology` is a **bounded space** if `Set.univ : Set α` is bounded. -/
/-
**BoundedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_4) → [Bornology α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space with a `Bornology` is a **bounded space** if `Set.univ : Set α` is bound
ed.
-/
class BoundedSpace (α : Type*) [Bornology α] : Prop where
  /-- The `Set.univ` is bounded. -/
  bounded_univ : Bornology.IsBounded (univ : Set α)

/-- A finite space is bounded. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite space is bounded.
-/
instance (priority := 100) BoundedSpace.of_finite {α : Type*} [Bornology α] [Finite α] :
    BoundedSpace α where
  bounded_univ := (toFinite _).isBounded

namespace Bornology

variable [Bornology α]

/-
**Bornology.isBounded_univ** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_univ : IsBounded (univ : Set α) ↔ BoundedSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedSpace.bounded_univ`：∀ {α : Type u_4} {inst : Bornology α} [self :
 BoundedSpace α], Bornology.IsBounded Set.univ
-/
theorem isBounded_univ : IsBounded (univ : Set α) ↔ BoundedSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
/-
**Bornology.cobounded_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：cobounded_eq_bot_iff : cobounded α = ⊥ ↔ BoundedSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_univ`：isBounded_univ : IsBounded (univ : Set α) ↔ Bo
undedSpace α
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cobounded_eq_bot_iff : cobounded α = ⊥ ↔ BoundedSpace α := by
  rw [← isBounded_univ, isBounded_def, compl_univ, empty_mem_iff_bot]

variable [BoundedSpace α]
/-
**Bornology.IsBounded.all** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_2} [inst : Bornology α] [BoundedSpace α] (s : Set α), Bornol
ogy.IsBounded s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `BoundedSpace.bounded_univ`：∀ {α : Type u_4} {inst : Bornology α} [self :
 BoundedSpace α], Bornology.IsBounded Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem IsBounded.all (s : Set α) : IsBounded s :=
  BoundedSpace.bounded_univ.subset s.subset_univ
/-
**Bornology.IsCobounded.all** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsCobounded`。
形式化陈述：∀ {α : Type u_2} [inst : Bornology α] [BoundedSpace α] (s : Set α), Bornol
ogy.IsCobounded s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.all`：∀ {α : Type u_2} [inst : Bornology α] [BoundedS
pace α] (s : Set α), Bornology.IsBounded s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem IsCobounded.all (s : Set α) : IsCobounded s :=
  compl_compl s ▸ IsBounded.all sᶜ

variable (α)

@[simp]
/-
**Bornology.cobounded_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：cobounded_eq_bot : cobounded α = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.cobounded_eq_bot_iff`：cobounded_eq_bot_iff : cobounded α = ⊥ ↔
 BoundedSpace α
-/
theorem cobounded_eq_bot : cobounded α = ⊥ :=
  cobounded_eq_bot_iff.2 ‹_›

end Bornology

namespace OrderDual
variable [Bornology α]

/-
**OrderDual.instBornology** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instBornology : Bornology αᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBornology : Bornology αᵒᵈ := ‹Bornology α›
/-
**OrderDual.isCobounded_preimage_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_2} [inst : Bornology α] {s : Set α},   Bornology.IsCobounded
 (⇑OrderDual.ofDual ⁻¹' s) ↔ Bornology.IsCobounded s
参数：⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isCobounded_preimage_ofDual {s : Set α} :
    IsCobounded (ofDual ⁻¹' s) ↔ IsCobounded s := Iff.rfl
/-
**OrderDual.isCobounded_preimage_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_2} [inst : Bornology α] {s : Set αᵒᵈ},   Bornology.IsCobound
ed (⇑OrderDual.toDual ⁻¹' s) ↔ Bornology.IsCobounded s
参数：⇑OrderDual.toDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isCobounded_preimage_toDual {s : Set αᵒᵈ} :
    IsCobounded (toDual ⁻¹' s) ↔ IsCobounded s := Iff.rfl
/-
**OrderDual.isBounded_preimage_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_2} [inst : Bornology α] {s : Set α}, Bornology.IsBounded (⇑O
rderDual.ofDual ⁻¹' s) ↔ Bornology.IsBounded s
参数：⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isBounded_preimage_ofDual {s : Set α} :
    IsBounded (ofDual ⁻¹' s) ↔ IsBounded s := Iff.rfl
/-
**OrderDual.isBounded_preimage_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_2} [inst : Bornology α] {s : Set αᵒᵈ},   Bornology.IsBounded
 (⇑OrderDual.toDual ⁻¹' s) ↔ Bornology.IsBounded s
参数：⇑OrderDual.toDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isBounded_preimage_toDual {s : Set αᵒᵈ} :
    IsBounded (toDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

end OrderDual

