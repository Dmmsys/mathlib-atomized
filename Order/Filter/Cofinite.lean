/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Ker
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Heyting.Boundary

/-!
# The cofinite filter

In this file we define

`Filter.cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `Filter.atTop`.

## TODO

Define filters for other cardinalities of the complement.
-/

@[expose] public section

open Set Function

variable {ι α β : Type*} {l : Filter α}

namespace Filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
/-
**Filter.cofinite** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：cofinite : Filter α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite

--- 原说明 ---
The cofinite filter is the filter of subsets whose complements are finite.
-/
def cofinite : Filter α :=
  comk Set.Finite finite_empty (fun _t ht _s hsub ↦ ht.subset hsub) fun _ h _ ↦ h.union

@[simp]
/-
**Filter.mem_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_cofinite {s : Set α} : s in @cofinite α ↔ sᶜ.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ sᶜ.Finite :=
  Iff.rfl

@[simp]
/-
**Filter.eventually_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_cofinite {p : α -> Prop} : (forallᶠ x in cofinite, p x) ↔ { x |
 ¬p x }.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite :=
  Iff.rfl
/-
**Filter.hasBasis_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
-/
theorem hasBasis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ =>
      htf.subset <| compl_subset_comm.2 hts⟩⟩
/-
**Filter.cofinite_neBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cofinite_neBot [Infinite α] : NeBot (@cofinite α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `Filter.hasBasis_cofinite`：hasBasis_cofinite : HasBasis cofinite (fun s :
 Set α => s.Finite) compl
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `Set.Finite.infinite_compl`：∀ {α : Type u} [Infinite α] {s : Set α}, s.Fi
nite → sᶜ.Infinite
-/
instance cofinite_neBot [Infinite α] : NeBot (@cofinite α) :=
  hasBasis_cofinite.neBot_iff.2 fun hs => hs.infinite_compl.nonempty

@[simp]
/-
**Filter.cofinite_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cofinite_eq_bot_iff : @cofinite α = ⊥ ↔ Finite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cofinite_eq_bot_iff : @cofinite α = ⊥ ↔ Finite α := by
  simp [← empty_mem_iff_bot, finite_univ_iff]

@[simp]
/-
**Filter.cofinite_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cofinite_eq_bot [Finite α] : @cofinite α = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.cofinite_eq_bot_iff`：cofinite_eq_bot_iff : @cofinite α = ⊥ ↔ Fini
te α
-/
theorem cofinite_eq_bot [Finite α] : @cofinite α = ⊥ := cofinite_eq_bot_iff.2 ‹_›
/-
**Filter.frequently_cofinite_iff_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_cofinite_iff_infinite {p : α -> Prop} : (existsᶠ x in cofinite,
 p x) ↔ Set.Infinite { x | p x }
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
theorem frequently_cofinite_iff_infinite {p : α → Prop} :
    (∃ᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x } := by
  simp only [Filter.Frequently, eventually_cofinite, not_not, Set.Infinite]
/-
**Filter.frequently_cofinite_mem_iff_infinite** 是 Mathlib 中的一个引理，位于命名空间 `Filter`
。
形式化陈述：frequently_cofinite_mem_iff_infinite {s : Set α} : (existsᶠ x in cofinite,
 x in s) ↔ s.Infinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.frequently_cofinite_iff_infinite`：frequently_cofinite_iff_infinit
e {p : α -> Prop} : (existsᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x }
-/
lemma frequently_cofinite_mem_iff_infinite {s : Set α} : (∃ᶠ x in cofinite, x ∈ s) ↔ s.Infinite :=
  frequently_cofinite_iff_infinite

alias ⟨_, _root_.Set.Infinite.frequently_cofinite⟩ := frequently_cofinite_mem_iff_infinite

@[simp]
/-
**Filter.cofinite_inf_principal_neBot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：cofinite_inf_principal_neBot_iff {s : Set α} : (cofinite ⊓ 𝓟 s).NeBot ↔ s.
Infinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Filter.frequently_mem_iff_neBot`：frequently_mem_iff_neBot {l : Filter α}
 {s : Set α} : (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
· 使用引理 `Filter.frequently_cofinite_mem_iff_infinite`：frequently_cofinite_mem_iff
_infinite {s : Set α} : (existsᶠ x in cofinite, x in s) ↔ s.Infinite
-/
lemma cofinite_inf_principal_neBot_iff {s : Set α} : (cofinite ⊓ 𝓟 s).NeBot ↔ s.Infinite :=
  frequently_mem_iff_neBot.symm.trans frequently_cofinite_mem_iff_infinite

alias ⟨_, _root_.Set.Infinite.cofinite_inf_principal_neBot⟩ := cofinite_inf_principal_neBot_iff
/-
**Filter._root_.Set.Finite.compl_mem_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.Finite) : sᶜ ∈ @cofinite α :=
  mem_cofinite.2 <| (compl_compl s).symm ▸ hs
/-
**Filter._root_.Set.Finite.eventually_cofinite_notMem** 是 Mathlib 中的一个定理，位于命名空间 
`Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.eventually_cofinite_notMem {s : Set α} (hs : s.Finite) :
    ∀ᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite
/-
**Filter._root_.Finset.eventually_cofinite_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.eventually_cofinite_notMem (s : Finset α) : ∀ᶠ x in cofinite, x ∉ s :=
  s.finite_toSet.eventually_cofinite_notMem
/-
**Filter._root_.Set.infinite_iff_frequently_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `
Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.infinite_iff_frequently_cofinite {s : Set α} :
    Set.Infinite s ↔ ∃ᶠ x in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm
/-
**Filter.eventually_cofinite_ne** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_cofinite_ne (x : α) : forallᶠ a in cofinite, a != x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.eventually_cofinite_notMem`：∀ {α : Type u_2} {s : Set α}, s.F
inite → ∀ᶠ (x : α) in Filter.cofinite, x ∉ s
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_notMem
/-
**Filter.le_cofinite_iff_compl_singleton_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_cofinite_iff_compl_singleton_mem : l <= cofinite ↔ forall x, {x}ᶜ in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Set.compl_iUnion₂`：compl_iUnion₂ (s : forall i, κ i -> Set α) : (⋃ (i) (
j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
-/
theorem le_cofinite_iff_compl_singleton_mem : l ≤ cofinite ↔ ∀ x, {x}ᶜ ∈ l := by
  refine ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => ?_⟩
  rw [← compl_compl s, ← biUnion_of_singleton sᶜ, compl_iUnion₂, Filter.biInter_mem hs]
  exact fun x _ => h x
/-
**Filter.le_cofinite_iff_eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_cofinite_iff_eventually_ne : l <= cofinite ↔ forall x, forallᶠ y in l, 
y != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_cofinite_iff_compl_singleton_mem`：le_cofinite_iff_compl_single
ton_mem : l <= cofinite ↔ forall x, {x}ᶜ in l
-/
theorem le_cofinite_iff_eventually_ne : l ≤ cofinite ↔ ∀ x, ∀ᶠ y in l, y ≠ x :=
  le_cofinite_iff_compl_singleton_mem

/-- If `α` is a preorder with no top element, then `atTop ≤ cofinite`. -/
/-
**Filter.atTop_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_le_cofinite [Preorder α] [NoTopOrder α] : (atTop : Filter α) <= cofi
nite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_cofinite_iff_eventually_ne`：le_cofinite_iff_eventually_ne : l 
<= cofinite ↔ forall x, forallᶠ y in l, y != x
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a

--- 原说明 ---
If `α` is a preorder with no top element, then `atTop ≤ cofinite`.
-/
theorem atTop_le_cofinite [Preorder α] [NoTopOrder α] : (atTop : Filter α) ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop

/-- If `α` is a preorder with no bottom element, then `atBot ≤ cofinite`. -/
/-
**Filter.atBot_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atBot_le_cofinite [Preorder α] [NoBotOrder α] : (atBot : Filter α) <= cofi
nite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_cofinite_iff_eventually_ne`：le_cofinite_iff_eventually_ne : l 
<= cofinite ↔ forall x, forallᶠ y in l, y != x
· 使用定理 `Filter.eventually_ne_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotO
rder α] (a : α), ∀ᶠ (x : α) in Filter.atBot, x ≠ a

--- 原说明 ---
If `α` is a preorder with no bottom element, then `atBot ≤ cofinite`.
-/
theorem atBot_le_cofinite [Preorder α] [NoBotOrder α] : (atBot : Filter α) ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atBot
/-
**Filter.comap_cofinite_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_cofinite_le (f : α -> β) : comap f cofinite <= cofinite
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_cofinite_iff_eventually_ne`：le_cofinite_iff_eventually_ne : l 
<= cofinite ↔ forall x, forallᶠ y in l, y != x
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem comap_cofinite_le (f : α → β) : comap f cofinite ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun _ => ne_of_apply_ne f⟩

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
/-
**Filter.coprod_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_cofinite : (cofinite : Filter α).coprod (cofinite : Filter β) = cof
inite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.coext`：∀ {α : Type u} {f g : Filter α}, (∀ (s : Set α), sᶜ ∈ f ↔ 
sᶜ ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The coproduct of the cofinite filters on two types is the cofinite filter on the
ir product.
-/
theorem coprod_cofinite : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_cofinite {α : ι → Type*} [Finite ι] :
    (Filter.coprodᵢ fun i => (cofinite : Filter (α i))) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cofinite, compl_compl, forall_finite_image_eval_iff]
/-
**Filter.disjoint_cofinite_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_cofinite_left : Disjoint cofinite l ↔ exists s in l, Set.Finite s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.disjoint_iff_right`：∀ {α : Type u_1} {ι : Sort u_4} {l l
' : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l' l 
↔ ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_cofinite_left : Disjoint cofinite l ↔ ∃ s ∈ l, Set.Finite s := by
  simp [l.basis_sets.disjoint_iff_right]
/-
**Filter.disjoint_cofinite_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_cofinite_right : Disjoint l cofinite ↔ exists s in l, Set.Finite 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Filter.disjoint_cofinite_left`：disjoint_cofinite_left : Disjoint cofinit
e l ↔ exists s in l, Set.Finite s
-/
theorem disjoint_cofinite_right : Disjoint l cofinite ↔ ∃ s ∈ l, Set.Finite s :=
  disjoint_comm.trans disjoint_cofinite_left

/-- If `l ≥ Filter.cofinite` is a countably generated filter, then `l.ker` is cocountable. -/
/-
**Filter.countable_compl_ker** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：countable_compl_ker [l.IsCountablyGenerated] (h : cofinite <= l) : Set.Cou
ntable l.kerᶜ
参数：h : cofinite <= l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_antitone_basis`：exists_antitone_basis (f : Filter α) [f.Is
CountablyGenerated] : exists x : Nat -> Set α, f.HasAntitoneBasis x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.ker`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p :
 ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.ker = ⋂ i, ⋂ (_ : p i), s i
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Filter.HasAntitoneBasis.mem`：∀ {α : Type u_1} {ι : Type u_4} [inst : Pre
order ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ (i : ι), s i
 ∈ l

--- 原说明 ---
If `l ≥ Filter.cofinite` is a countably generated filter, then `l.ker` is cocoun
table.
-/
theorem countable_compl_ker [l.IsCountablyGenerated] (h : cofinite ≤ l) : Set.Countable l.kerᶜ := by
  rcases exists_antitone_basis l with ⟨s, hs⟩
  simp only [hs.ker, iInter_true, compl_iInter]
  exact countable_iUnion fun n ↦ Set.Finite.countable <| h <| hs.mem _

/-- If `f` tends to a countably generated filter `l` along `Filter.cofinite`,
then for all but countably many elements, `f x ∈ l.ker`. -/
/-
**Filter.Tendsto.countable_compl_preimage_ker** 是 Mathlib 中的一个定理，位于命名空间 `Filter.
Tendsto`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {f : α → β} {l : Filter β} [l.IsCountablyG
enerated],   Filter.Tendsto f Filter.cofinite l → (f ⁻¹' l.ker)ᶜ.Countable
参数：f ⁻¹' l.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.ker_comap`：∀ {α : Type u_2} {β : Type u_3} (m : α → β) (f : Filte
r β), (Filter.comap m f).ker = m ⁻¹' f.ker
· 使用定理 `Filter.countable_compl_ker`：countable_compl_ker [l.IsCountablyGenerated]
 (h : cofinite <= l) : Set.Countable l.kerᶜ
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂

--- 原说明 ---
If `f` tends to a countably generated filter `l` along `Filter.cofinite`,
then for all but countably many elements, `f x ∈ l.ker`.
-/
theorem Tendsto.countable_compl_preimage_ker {f : α → β}
    {l : Filter β} [l.IsCountablyGenerated] (h : Tendsto f cofinite l) :
    Set.Countable (f ⁻¹' l.ker)ᶜ := by rw [← ker_comap]; exact countable_compl_ker h.le_comap

/-- Given a collection of filters `l i : Filter (α i)` and sets `s i ∈ l i`,
if all but finitely many of `s i` are the whole space,
then their indexed product `Set.pi Set.univ s` belongs to the filter `Filter.pi l`. -/
/-
**Filter.univ_pi_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：univ_pi_mem_pi {α : ι -> Type*} {s : forall i, Set (α i)} {l : forall i, F
ilter (α i)} (h : forall i, s i in l i) (hfin : forallᶠ i in cofinite, s i = uni
v) : univ.pi s in pi l
参数：α i；α i；h : forall i, s i in l i；hfin : forallᶠ i in cofinite, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.pi_mem_pi`：pi_mem_pi {I : Set ι} (hI : I.Finite) (h : forall i in
 I, s i in f i) : I.pi s in pi f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Given a collection of filters `l i : Filter (α i)` and sets `s i ∈ l i`,
if all but finitely many of `s i` are the whole space,
then their indexed product `Set.pi Set.univ s` belongs to the filter `Filter.pi 
l`.
-/
theorem univ_pi_mem_pi {α : ι → Type*} {s : ∀ i, Set (α i)} {l : ∀ i, Filter (α i)}
    (h : ∀ i, s i ∈ l i) (hfin : ∀ᶠ i in cofinite, s i = univ) : univ.pi s ∈ pi l := by
  filter_upwards [pi_mem_pi hfin fun i _ ↦ h i] with a ha i _
  if hi : s i = univ then
    simp [hi]
  else
    exact ha i hi

/-- Given a family of maps `f i : α i → β i` and a family of filters `l i : Filter (α i)`,
if all but finitely many of `f i` are surjective,
then the indexed product of `f i`s maps the indexed product of the filters `l i`
to the indexed products of their pushforwards under individual `f i`s.

See also `map_piMap_pi_finite` for the case of a finite index type.
-/
/-
**Filter.map_piMap_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_piMap_pi {α β : ι -> Type*} {f : forall i, α i -> β i} (hf : forallᶠ i
 in cofinite, Surjective (f i)) (l : forall i, Filter (α i)) : map (Pi.map f) (p
i l) = pi fun i => map (f i) (l i)
参数：hf : forallᶠ i in cofinite, Surjective (f i)；l : forall i, Filter (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.tendsto_piMap_pi`：tendsto_piMap_pi {β : ι -> Type*} {f : forall i
, α i -> β i} {l : forall i, Filter (α i)} {l' : forall i, Filter (β i)} (h : fo
rall i, Tends…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.hasBasis_pi`：hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i ->
 Set (α i)} {p : forall i, ι' i -> Prop} (h : forall i, (f i).HasBasis (p i) (s 
i)) : (p…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_piecewise_univ`：univ_pi_piecewise_univ {ι : Type*} {α : ι ->
 Type*} (s : Set ι) (t : forall i, Set (α i)) [forall x, Decidable (x in s)] : p
i univ (s.piecew…
· 使用定理 `Set.piMap_image_univ_pi`：piMap_image_univ_pi (f : forall i, α i -> β i) 
(t : forall i, Set (α i)) : Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i
· 使用定理 `Filter.univ_pi_mem_pi`：univ_pi_mem_pi {α : ι -> Type*} {s : forall i, Se
t (α i)} {l : forall i, Filter (α i)} (h : forall i, s i in l i) (hfin : forallᶠ
 i in cofin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a family of maps `f i : α i → β i` and a family of filters `l i : Filter (
α i)`,
if all but finitely many of `f i` are surjective,
then the indexed product of `f i`s maps the indexed product of the filters `l i`
to the indexed products of their pushforwards under individual `f i`s.

See also `map_piMap_pi_finite` for the case of a finite index type.
-/
theorem map_piMap_pi {α β : ι → Type*} {f : ∀ i, α i → β i}
    (hf : ∀ᶠ i in cofinite, Surjective (f i)) (l : ∀ i, Filter (α i)) :
    map (Pi.map f) (pi l) = pi fun i ↦ map (f i) (l i) := by
  refine le_antisymm (tendsto_piMap_pi fun _ ↦ tendsto_map) ?_
  refine ((hasBasis_pi fun i ↦ (l i).basis_sets).map _).ge_iff.2 ?_
  rintro ⟨I, s⟩ ⟨hI : I.Finite, hs : ∀ i ∈ I, s i ∈ l i⟩
  classical
  rw [← univ_pi_piecewise_univ, piMap_image_univ_pi]
  refine univ_pi_mem_pi (fun i ↦ ?_) ?_
  · by_cases hi : i ∈ I
    · simpa [hi] using image_mem_map (hs i hi)
    · simp [hi]
  · filter_upwards [hf, hI.compl_mem_cofinite] with i hsurj (hiI : i ∉ I)
    simp [hiI, hsurj.range_eq]

/-- Given finite families of maps `f i : α i → β i` and of filters `l i : Filter (α i)`,
the indexed product of `f i`s maps the indexed product of the filters `l i`
to the indexed products of their pushforwards under individual `f i`s.

See also `map_piMap_pi` for a more general case.
-/
/-
**Filter.map_piMap_pi_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_piMap_pi_finite {α β : ι -> Type*} [Finite ι] (f : forall i, α i -> β 
i) (l : forall i, Filter (α i)) : map (Pi.map f) (pi l) = pi fun i => map (f i) 
(l i)
参数：f : forall i, α i -> β i；l : forall i, Filter (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_piMap_pi`：map_piMap_pi {α β : ι -> Type*} {f : forall i, α i 
-> β i} (hf : forallᶠ i in cofinite, Surjective (f i)) (l : forall i, Filter (α 
i)) : map…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.cofinite_eq_bot`：cofinite_eq_bot [Finite α] : @cofinite α = ⊥

--- 原说明 ---
Given finite families of maps `f i : α i → β i` and of filters `l i : Filter (α 
i)`,
the indexed product of `f i`s maps the indexed product of the filters `l i`
to the indexed products of their pushforwards under individual `f i`s.

See also `map_piMap_pi` for a more general case.
-/
theorem map_piMap_pi_finite {α β : ι → Type*} [Finite ι]
    (f : ∀ i, α i → β i) (l : ∀ i, Filter (α i)) :
    map (Pi.map f) (pi l) = pi fun i ↦ map (f i) (l i) :=
  map_piMap_pi (by simp) l

end Filter

open Filter

/-
**Set.Finite.cofinite_inf_principal_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.cofinite_inf_principal_compl {s : Set α} (hs : s.Finite) : cofi
nite ⊓ 𝓟 sᶜ = cofinite
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
-/
lemma Set.Finite.cofinite_inf_principal_compl {s : Set α} (hs : s.Finite) :
    cofinite ⊓ 𝓟 sᶜ = cofinite := by
  simpa using hs.compl_mem_cofinite
/-
**Set.Finite.cofinite_inf_principal_sdiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.cofinite_inf_principal_sdiff {s t : Set α} (ht : t.Finite) : co
finite ⊓ 𝓟 (s \ t) = cofinite ⊓ 𝓟 s
参数：ht : t.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
· 使用引理 `Set.Finite.cofinite_inf_principal_compl`：Set.Finite.cofinite_inf_princip
al_compl {s : Set α} (hs : s.Finite) : cofinite ⊓ 𝓟 sᶜ = cofinite
-/
lemma Set.Finite.cofinite_inf_principal_sdiff {s t : Set α} (ht : t.Finite) :
    cofinite ⊓ 𝓟 (s \ t) = cofinite ⊓ 𝓟 s := by
  rw [sdiff_eq, ← inf_principal, ← inf_assoc, inf_right_comm, ht.cofinite_inf_principal_compl]

@[deprecated (since := "2026-06-03")]
alias Set.Finite.cofinite_inf_principal_diff := Set.Finite.cofinite_inf_principal_sdiff

/-- For natural numbers the filters `Filter.cofinite` and `Filter.atTop` coincide. -/
/-
**Nat.cofinite_eq_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_Ici`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ici
 a)ᶜ = Set.Iio a
· 使用定理 `Set.finite_lt_nat`：finite_lt_nat (n : Nat) : Set.Finite { i | i < n }
· 使用定理 `Filter.atTop_le_cofinite`：atTop_le_cofinite [Preorder α] [NoTopOrder α] 
: (atTop : Filter α) <= cofinite
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α

--- 原说明 ---
For natural numbers the filters `Filter.cofinite` and `Filter.atTop` coincide.
-/
theorem Nat.cofinite_eq_atTop : @cofinite ℕ = atTop := by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun N _ => ?_
  simpa only [mem_cofinite, compl_Ici] using! finite_lt_nat N
/-
**Nat.frequently_atTop_iff_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.frequently_atTop_iff_infinite {p : Nat -> Prop} : (existsᶠ n in atTop,
 p n) ↔ Set.Infinite { n | p n }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Filter.frequently_cofinite_iff_infinite`：frequently_cofinite_iff_infinit
e {p : α -> Prop} : (existsᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x }
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nat.frequently_atTop_iff_infinite {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ Set.Infinite { n | p n } := by
  rw [← Nat.cofinite_eq_atTop, frequently_cofinite_iff_infinite]
/-
**Nat.eventually_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.eventually_pos : forallᶠ (k : Nat) in Filter.atTop, 0 < k
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma Nat.eventually_pos : ∀ᶠ (k : ℕ) in Filter.atTop, 0 < k :=
  Filter.eventually_of_mem (Filter.mem_atTop_sets.mpr ⟨1, fun _ hx ↦ hx⟩) (fun _ hx ↦ hx)
/-
**Filter.Tendsto.exists_within_forall_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.exists_within_forall_le {α β : Type*} [LinearOrder β] {s : 
Set α} (hs : s.Nonempty) {f : α -> β} (hf : Filter.Tendsto f Filter.cofinite Fil
ter.atTop) : exists a₀ in s, forall a in s, f a₀ <= f a
参数：hs : s.Nonempty；hf : Filter.Tendsto f Filter.cofinite Filter.atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_cofinite`：eventually_cofinite {p : α -> Prop} : (foral
lᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Set.exists_min_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Filter.Tendsto.exists_within_forall_le {α β : Type*} [LinearOrder β] {s : Set α}
    (hs : s.Nonempty) {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a₀ ≤ f a := by
  by_cases! all_top : ∃ y ∈ s, ∃ x, f y < x
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    rcases all_top with ⟨y, hys, x, hx⟩
    have : { y | ¬x ≤ f y }.Finite := Filter.eventually_cofinite.mp (tendsto_atTop.1 hf x)
    simp only [not_le] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine ⟨a₀, ha₀s, fun a has => (lt_or_ge (f a) x).elim ?_ (le_trans ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
  · -- in this case, f is constant because all values are at top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => all_top a ha (f a₀)⟩
/-
**Filter.Tendsto.exists_forall_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.exists_forall_le [Nonempty α] [LinearOrder β] {f : α -> β} 
(hf : Tendsto f cofinite atTop) : exists a₀, forall a, f a₀ <= f a
参数：hf : Tendsto f cofinite atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.exists_within_forall_le`：Filter.Tendsto.exists_within_for
all_le {α β : Type*} [LinearOrder β] {s : Set α} (hs : s.Nonempty) {f : α -> β} 
(hf : Filter.Tendsto f Filte…
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem Filter.Tendsto.exists_forall_le [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atTop) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩
/-
**Filter.Tendsto.exists_within_forall_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.exists_within_forall_ge [LinearOrder β] {s : Set α} (hs : s
.Nonempty) {f : α -> β} (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) : e
xists a₀ in s, forall a in s, f a <= f a₀
参数：hs : s.Nonempty；hf : Filter.Tendsto f Filter.cofinite Filter.atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.exists_within_forall_le`：Filter.Tendsto.exists_within_for
all_le {α β : Type*} [LinearOrder β] {s : Set α} (hs : s.Nonempty) {f : α -> β} 
(hf : Filter.Tendsto f Filte…
-/
theorem Filter.Tendsto.exists_within_forall_ge [LinearOrder β] {s : Set α} (hs : s.Nonempty)
    {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf
/-
**Filter.Tendsto.exists_forall_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.exists_forall_ge [Nonempty α] [LinearOrder β] {f : α -> β} 
(hf : Tendsto f cofinite atBot) : exists a₀, forall a, f a <= f a₀
参数：hf : Tendsto f cofinite atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.exists_forall_le`：Filter.Tendsto.exists_forall_le [Nonemp
ty α] [LinearOrder β] {f : α -> β} (hf : Tendsto f cofinite atTop) : exists a₀, 
forall a, f a₀ <= f a
-/
theorem Filter.Tendsto.exists_forall_ge [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atBot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf
/-
**Function.Surjective.le_map_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.le_map_cofinite {f : α -> β} (hf : Surjective f) : cof
inite <= map f cofinite
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set
 β}, (f ⁻¹' s).Finite → Function.Surjective f → s.Finite
-/
theorem Function.Surjective.le_map_cofinite {f : α → β} (hf : Surjective f) :
    cofinite ≤ map f cofinite := fun _ h => .of_preimage h hf

/-- For an injective function `f`, inverse images of finite sets are finite. See also
`Filter.comap_cofinite_le` and `Function.Injective.comap_cofinite_eq`. -/
/-
**Function.Injective.tendsto_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.tendsto_cofinite {f : α -> β} (hf : Injective f) : Tend
sto f cofinite cofinite
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
For an injective function `f`, inverse images of finite sets are finite. See als
o
`Filter.comap_cofinite_le` and `Function.Injective.comap_cofinite_eq`.
-/
theorem Function.Injective.tendsto_cofinite {f : α → β} (hf : Injective f) :
    Tendsto f cofinite cofinite := fun _ h => h.preimage hf.injOn

/-- For a function with finite fibres, inverse images of finite sets are finite. -/
/-
**Filter.Tendsto.cofinite_of_finite_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Filter.Tendsto.cofinite_of_finite_preimage_singleton {f : α -> β} (hf : fo
rall b, Finite (f ⁻¹' {b})) : Tendsto f cofinite cofinite
参数：hf : forall b, Finite (f ⁻¹' {b})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage'`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β
}, s.Finite → (∀ b ∈ s, (f ⁻¹' {b}).Finite) → (f ⁻¹' s).Finite

--- 原说明 ---
For a function with finite fibres, inverse images of finite sets are finite.
-/
theorem Filter.Tendsto.cofinite_of_finite_preimage_singleton {f : α → β}
    (hf : ∀ b, Finite (f ⁻¹' {b})) : Tendsto f cofinite cofinite :=
  fun _ h => h.preimage' fun b _ ↦ hf b

/-- The pullback of the `Filter.cofinite` under an injective function is equal to `Filter.cofinite`.
See also `Filter.comap_cofinite_le` and `Function.Injective.tendsto_cofinite`. -/
/-
**Function.Injective.comap_cofinite_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.comap_cofinite_eq {f : α -> β} (hf : Injective f) : com
ap f cofinite = cofinite
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.comap_cofinite_le`：comap_cofinite_le (f : α -> β) : comap f cofin
ite <= cofinite
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite

--- 原说明 ---
The pullback of the `Filter.cofinite` under an injective function is equal to `F
ilter.cofinite`.
See also `Filter.comap_cofinite_le` and `Function.Injective.tendsto_cofinite`.
-/
theorem Function.Injective.comap_cofinite_eq {f : α → β} (hf : Injective f) :
    comap f cofinite = cofinite :=
  (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

/-- An injective sequence `f : ℕ → ℕ` tends to infinity at infinity. -/
/-
**Function.Injective.nat_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.nat_tendsto_atTop {f : Nat -> Nat} (hf : Injective f) :
 Tendsto f atTop atTop
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
An injective sequence `f : ℕ → ℕ` tends to infinity at infinity.
-/
theorem Function.Injective.nat_tendsto_atTop {f : ℕ → ℕ} (hf : Injective f) :
    Tendsto f atTop atTop :=
  Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite
/-
**Function.update_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.update_eventuallyEq [DecidableEq α] (f : α -> β) (a : α) (b : β) 
: Function.update f a b =ᶠ[𝓟 {a}ᶜ] f
参数：f : α -> β；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
lemma Function.update_eventuallyEq [DecidableEq α] (f : α → β) (a : α) (b : β) :
    Function.update f a b =ᶠ[𝓟 {a}ᶜ] f := by
  filter_upwards [mem_principal_self _] with u hu using Function.update_of_ne hu _ _
/-
**Function.update_eventuallyEq_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.update_eventuallyEq_cofinite [DecidableEq α] (f : α -> β) (a : α)
 (b : β) : Function.update f a b =ᶠ[cofinite] f
参数：f : α -> β；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用引理 `Function.update_eventuallyEq`：Function.update_eventuallyEq [DecidableEq 
α] (f : α -> β) (a : α) (b : β) : Function.update f a b =ᶠ[𝓟 {a}ᶜ] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma Function.update_eventuallyEq_cofinite [DecidableEq α] (f : α → β) (a : α) (b : β) :
    Function.update f a b =ᶠ[cofinite] f :=
  (Function.update_eventuallyEq f a b).filter_mono (by simp)

/-- A function tendsto 0 along the cofinite filter iff it has finite support. -/
/-
**tendsto_cofinite_pure_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_cofinite_pure_iff {f : α -> β} [Zero β] : Tendsto f cofinite (pure
 0) ↔ f.HasFiniteSupport
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function tendsto 0 along the cofinite filter iff it has finite support.
-/
lemma tendsto_cofinite_pure_iff {f : α → β} [Zero β] :
    Tendsto f cofinite (pure 0) ↔ f.HasFiniteSupport := by
  simp [Function.HasFiniteSupport, Function.support]

variable {f : Filter α}

/-- A filter is free iff it is smaller than the cofinite filter. -/
/-
**le_cofinite_iff_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_cofinite_iff_ker : f <= cofinite ↔ f.ker = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_cofinite_iff_compl_singleton_mem`：le_cofinite_iff_compl_single
ton_mem : l <= cofinite ↔ forall x, {x}ᶜ in l
· 使用引理 `Filter.ker_def`：ker_def (f : Filter α) : f.ker = ⋂ s in f, s
· 使用定理 `Set.iInter₂_eq_empty_iff`：iInter₂_eq_empty_iff {s : forall i, κ i -> Set
 α} : ⋂ (i) (j), s i j = ∅ ↔ forall a, exists i j, a ∉ s i j
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
A filter is free iff it is smaller than the cofinite filter.
-/
theorem le_cofinite_iff_ker : f ≤ cofinite ↔ f.ker = ∅ := by
  rw [le_cofinite_iff_compl_singleton_mem, ker_def, iInter₂_eq_empty_iff]
  exact forall_congr' fun x => ⟨fun h => ⟨{x}ᶜ, h, by simp⟩,
    fun ⟨s, hs, hx⟩ => mem_of_superset hs (by simpa using hx)⟩
/-
**le_cofinite_iff_boundary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_cofinite_iff_boundary : f <= cofinite ↔ Coheyting.boundary f = f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coheyting.inf_hnot_self`：inf_hnot_self (a : α) : a ⊓ ￢a = ∂ a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `le_cofinite_iff_ker`：le_cofinite_iff_ker : f <= cofinite ↔ f.ker = ∅
· 使用定理 `Filter.hnot_def`：∀ {α : Type u_1} {f : Filter α}, ￢f = Filter.principal 
f.kerᶜ
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
-/
theorem le_cofinite_iff_boundary : f ≤ cofinite ↔ Coheyting.boundary f = f := by
  rw [← Coheyting.inf_hnot_self, inf_eq_left, le_cofinite_iff_ker,
    Filter.hnot_def, le_principal_iff]
  constructor
  · intro h
    simp [h]
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    exact hx f.kerᶜ h hx

variable (f)
/-
**boundary_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boundary_le_cofinite : Coheyting.boundary f <= cofinite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_cofinite_iff_boundary`：le_cofinite_iff_boundary : f <= cofinite ↔ Coh
eyting.boundary f = f
· 使用定理 `Coheyting.boundary_boundary`：boundary_boundary (a : α) : ∂ ∂ a = ∂ a
-/
theorem boundary_le_cofinite : Coheyting.boundary f ≤ cofinite :=
  le_cofinite_iff_boundary.2 (Coheyting.boundary_boundary f)

@[simp]
/-
**boundary_principal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boundary_principal (s : Set α) : Coheyting.boundary (𝓟 s) = ⊥
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.hnot_principal`：hnot_principal {s : Set α} : ￢𝓟 s = 𝓟 sᶜ
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem boundary_principal (s : Set α) : Coheyting.boundary (𝓟 s) = ⊥ := by
  simp [← Coheyting.inf_hnot_self]

/-- Every filter is the disjoint supremum of
a principal filter and a free filter in a unique way. -/
/-
**existsUnique_eq_principal_sup_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_eq_principal_sup_free : exists! p : Set α × Filter α, p.2 <= 
cofinite ∧ Disjoint (𝓟 p.1) p.2 ∧ f = 𝓟 p.1 ⊔ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `boundary_le_cofinite`：boundary_le_cofinite : Coheyting.boundary f <= cof
inite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.disjoint_principal_left`：disjoint_principal_left {f : Filter α} {
s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ in f
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.hnot_principal`：hnot_principal {s : Set α} : ￢𝓟 s = 𝓟 sᶜ
· 使用定理 `Filter.hnot_def`：∀ {α : Type u_1} {f : Filter α}, ￢f = Filter.principal 
f.kerᶜ
· 使用定理 `Coheyting.hnot_hnot_sup_boundary`：hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔
 ∂ a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_cofinite_iff_ker`：le_cofinite_iff_ker : f <= cofinite ↔ f.ker = ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.ker_principal`：∀ {α : Type u_2} (s : Set α), (Filter.principal s)
.ker = s
· 使用定理 `Filter.ker_sup`：ker_sup (f g : Filter α) : ker (f ⊔ g) = ker f union ker
 g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Coheyting.boundary_sup_le`：boundary_sup_le : ∂ (a ⊔ b) <= ∂ a ⊔ ∂ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `boundary_principal`：boundary_principal (s : Set α) : Coheyting.boundary 
(𝓟 s) = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Coheyting.boundary_le`：boundary_le : ∂ a <= a

--- 原说明 ---
Every filter is the disjoint supremum of
a principal filter and a free filter in a unique way.
-/
theorem existsUnique_eq_principal_sup_free :
    ∃! p : Set α × Filter α, p.2 ≤ cofinite ∧ Disjoint (𝓟 p.1) p.2 ∧ f = 𝓟 p.1 ⊔ p.2 := by
  refine ⟨(f.ker, Coheyting.boundary f), ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
  · exact boundary_le_cofinite f
  · rw [disjoint_principal_left]
    exact mem_inf_of_right (mem_principal_self f.kerᶜ)
  · rw [← compl_compl f.ker, ← hnot_principal, ← Filter.hnot_def,
      Coheyting.hnot_hnot_sup_boundary]
  · have hqk := congrArg Filter.ker hq.2.2
    rw [ker_sup, ker_principal, le_cofinite_iff_ker.mp hq.1, union_empty] at hqk
    refine congrArg₂ Prod.mk hqk.symm (le_antisymm (le_inf ?_ ?_) ?_)
    · rw [hq.2.2]
      exact le_sup_right
    · rw [Filter.hnot_def, le_principal_iff, ← disjoint_principal_left, hqk]
      exact hq.2.1
    · grw [hq.2.2, Coheyting.boundary_sup_le, boundary_principal, bot_sup_eq]
      exact Coheyting.boundary_le

/-- Every filter is the disjoint supremum of a principal filter and a free filter. -/
/-
**exists_eq_principal_sup_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_principal_sup_free : exists s g, g <= cofinite ∧ Disjoint (𝓟 s) 
g ∧ f = 𝓟 s ⊔ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `existsUnique_eq_principal_sup_free`：existsUnique_eq_principal_sup_free :
 exists! p : Set α × Filter α, p.2 <= cofinite ∧ Disjoint (𝓟 p.1) p.2 ∧ f = 𝓟 p.
1 ⊔ p.2

--- 原说明 ---
Every filter is the disjoint supremum of a principal filter and a free filter.
-/
theorem exists_eq_principal_sup_free :
    ∃ s g, g ≤ cofinite ∧ Disjoint (𝓟 s) g ∧ f = 𝓟 s ⊔ g :=
  Prod.exists.mp (existsUnique_eq_principal_sup_free f).exists
