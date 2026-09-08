/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.LiminfLimsup


/-!
# Summation filters

We define a `SummationFilter` on `β` to be a filter on the finite subsets of `β`. These are used
in defining summability: if `L` is a summation filter, we define the `L`-sum of `f` to be the
limit along `L` of the sums over finsets (if this limit exists). This file only develops the basic
machinery of summation filters - the key definitions `HasSum`, `tsum` and `summable` (and their
product variants) are in the file `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`.
-/

@[expose] public section

open Set Filter Function

variable {α β γ : Type*}

/-- A filter on the set of finite subsets of a type `β`. (Used for defining infinite topological
sums and products, as limits along the given filter of partial sums / products over finsets.) -/
/-
**SummationFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter on the set of finite subsets of a type `β`. (Used for defining infinite
 topological
sums and products, as limits along the given filter of partial sums / products o
ver finsets.)
-/
structure SummationFilter (β) where
  /-- The filter -/
  filter : Filter (Finset β)

namespace SummationFilter

/-- Typeclass asserting that a summation filter `L` is consistent with unconditional summation,
so that any unconditionally-summable function is `L`-summable with the same sum. -/
/-
**SummationFilter.LeAtTop** 是 Mathlib 中的一个归纳类型，位于命名空间 `SummationFilter`。
形式化陈述：{β : Type u_2} → SummationFilter β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass asserting that a summation filter `L` is consistent with unconditional
 summation,
so that any unconditionally-summable function is `L`-summable with the same sum.
-/
class LeAtTop (L : SummationFilter β) : Prop where
  le_atTop : L.filter ≤ atTop

export LeAtTop (le_atTop)

/-- Typeclass asserting that a summation filter is non-vacuous (if this is not satisfied, then
every function is summable with every possible sum simultaneously). -/
/-
**SummationFilter.NeBot** 是 Mathlib 中的一个归纳类型，位于命名空间 `SummationFilter`。
形式化陈述：{β : Type u_2} → SummationFilter β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass asserting that a summation filter is non-vacuous (if this is not satis
fied, then
every function is summable with every possible sum simultaneously).
-/
class NeBot (L : SummationFilter β) : Prop where
  ne_bot : L.filter.NeBot

/-- Makes the `NeBot` instance visible to the typeclass machinery. -/
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes the `NeBot` instance visible to the typeclass machinery.
-/
instance (L : SummationFilter β) [L.NeBot] : L.filter.NeBot := NeBot.ne_bot
/-
**SummationFilter.neBot_or_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `SummationFilter`。
形式化陈述：neBot_or_eq_bot (L : SummationFilter β) : L.NeBot ∨ L.filter = ⊥
参数：L : SummationFilter β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neBot_or_eq_bot (L : SummationFilter β) : L.NeBot ∨ L.filter = ⊥ := by
  by_cases h : L.filter = ⊥
  · exact .inr h
  · exact .inl ⟨⟨h⟩⟩

section support

/-- The support of a summation filter (its `lim inf`, considered as a filter of sets). -/
/-
**SummationFilter.support** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：support (L : SummationFilter β) : Set β
参数：L : SummationFilter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a summation filter (its `lim inf`, considered as a filter of sets
).
-/
def support (L : SummationFilter β) : Set β := {b | ∀ᶠ s in L.filter, b ∈ s}
/-
**SummationFilter.support_eq_limsInf** 是 Mathlib 中的一个引理，位于命名空间 `SummationFilter`
。
形式化陈述：support_eq_limsInf (L : SummationFilter β) : support L = limsInf (L.filter
.map (↑))
参数：L : SummationFilter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma support_eq_limsInf (L : SummationFilter β) :
    support L = limsInf (L.filter.map (↑)) := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simpa [support, limsInf, ofPred_subset] using
    ⟨fun hL b hb x hx ↦ hL x <| hb.mp <| .of_forall fun c hc ↦ hc hx,
      fun hL x hx ↦ singleton_subset_iff.mp <| hL _ <| by simpa using hx⟩
/-
**SummationFilter.support_eq_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 `SummationFilter
`。
形式化陈述：support_eq_univ_iff {L : SummationFilter β} : L.support = univ ↔ L.filter 
<= atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma support_eq_univ_iff {L : SummationFilter β} :
    L.support = univ ↔ L.filter ≤ atTop := by
  simp only [support, Set.eq_univ_iff_forall, Set.mem_ofPred]
  refine ⟨fun h s hs ↦ ?_, fun h b ↦ .filter_mono h ?_⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    have := (Filter.biInter_finset_mem t).mpr fun b hb ↦ h b
    exact Filter.mem_of_superset this fun r hr ↦ ht r (by simpa using! hr)
  · filter_upwards [eventually_ge_atTop {b}] using by simp
/-
**SummationFilter.support_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `SummationFilter`。
形式化陈述：∀ {β : Type u_2} (L : SummationFilter β) [L.LeAtTop], L.support = Set.univ
参数：L : SummationFilter β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SummationFilter.support_eq_univ_iff`：support_eq_univ_iff {L : SummationF
ilter β} : L.support = univ ↔ L.filter <= atTop
· 使用定理 `SummationFilter.LeAtTop.le_atTop`：∀ {β : Type u_2} {L : SummationFilter 
β} [self : L.LeAtTop], L.filter ≤ Filter.atTop
-/
@[simp] lemma support_eq_univ (L : SummationFilter β) [L.LeAtTop] : L.support = univ :=
  support_eq_univ_iff.mpr L.le_atTop
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty β] (L : SummationFilter β) : L.LeAtTop :=
  ⟨support_eq_univ_iff.mp <| Subsingleton.elim ..⟩
/-
**SummationFilter.leAtTop_of_not_NeBot** 是 Mathlib 中的一个引理，位于命名空间 `SummationFilte
r`。
形式化陈述：leAtTop_of_not_NeBot (L : SummationFilter β) (hL : ¬L.NeBot) : L.LeAtTop
参数：L : SummationFilter β；hL : ¬L.NeBot。
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
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `SummationFilter.neBot_or_eq_bot`：neBot_or_eq_bot (L : SummationFilter β)
 : L.NeBot ∨ L.filter = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SummationFilter.support_eq_univ_iff`：support_eq_univ_iff {L : SummationF
ilter β} : L.support = univ ↔ L.filter <= atTop
-/
lemma leAtTop_of_not_NeBot (L : SummationFilter β) (hL : ¬L.NeBot) : L.LeAtTop := by
  have hLs : L.support = Set.univ := by
    simp [SummationFilter.support, L.neBot_or_eq_bot.resolve_left hL]
  exact ⟨L.support_eq_univ_iff.mp hLs⟩

/-- Decidability instance: useful when working with `Finset` sums / products. -/
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decidability instance: useful when working with `Finset` sums / products.
-/
instance (L : SummationFilter β) [L.LeAtTop] : DecidablePred (· ∈ L.support) :=
  fun b ↦ isTrue (by simp)

end support

section has_support

/-- Typeclass asserting that the sets in `L.filter` are eventually contained in `L.support`. This
is a sufficient condition for `L`-summation to behave well on finitely-supported functions: every
finitely-supported `f` is `L`-summable with the sum `∑ᶠ x ∈ L.support, f x` (and similarly for
products). -/
/-
**SummationFilter.HasSupport** 是 Mathlib 中的一个归纳类型，位于命名空间 `SummationFilter`。
形式化陈述：{β : Type u_2} → SummationFilter β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass asserting that the sets in `L.filter` are eventually contained in `L.s
upport`. This
is a sufficient condition for `L`-summation to behave well on finitely-supported
 functions: every
finitely-supported `f` is `L`-summable with the sum `∑ᶠ x ∈ L.support, f x` (and
 similarly for
products).
-/
class HasSupport (L : SummationFilter β) : Prop where
  eventually_le_support : ∀ᶠ s in L.filter, ↑s ⊆ L.support

export HasSupport (eventually_le_support)
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : SummationFilter β) [L.LeAtTop] : HasSupport L := ⟨by simp⟩
/-
**SummationFilter.eventually_mem_or_not_mem** 是 Mathlib 中的一个引理，位于命名空间 `Summation
Filter`。
形式化陈述：eventually_mem_or_not_mem (L : SummationFilter β) [HasSupport L] (b : β) :
 (forallᶠ s in L.filter, b in s) ∨ (forallᶠ s in L.filter, b ∉ s)
参数：L : SummationFilter β；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `SummationFilter.HasSupport.eventually_le_support`：∀ {β : Type u_2} {L : 
SummationFilter β} [self : L.HasSupport], ∀ᶠ (s : Finset β) in L.filter, ↑s ⊆ L.
support
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
-/
lemma eventually_mem_or_not_mem (L : SummationFilter β) [HasSupport L] (b : β) :
    (∀ᶠ s in L.filter, b ∈ s) ∨ (∀ᶠ s in L.filter, b ∉ s) := by
  rw [or_iff_not_imp_left]
  intro hb
  filter_upwards [L.eventually_le_support] with a ha using notMem_subset ha hb

end has_support

section map_comap

/-- Pushforward of a summation filter along an embedding.

(We define this only for embeddings, rather than arbitrary maps, since this is the only case needed
for the intended applications, and this avoids requiring a `DecidableEq` instance on `γ`.) -/
/-
**SummationFilter.map** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：{β : Type u_2} → {γ : Type u_3} → SummationFilter β → (β ↪ γ) → SummationF
ilter γ
参数：β ↪ γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward of a summation filter along an embedding.

(We define this only for embeddings, rather than arbitrary maps, since this is t
he only case needed
for the intended applications, and this avoids requiring a `DecidableEq` instanc
e on `γ`.)
-/
@[simps] def map (L : SummationFilter β) (f : β ↪ γ) : SummationFilter γ where
  filter := L.filter.map (Finset.map f)
/-
**SummationFilter.support_map** 是 Mathlib 中的一个定理，位于命名空间 `SummationFilter`。
形式化陈述：∀ {β : Type u_2} {γ : Type u_3} (L : SummationFilter β) [L.NeBot] (f : β ↪
 γ), (L.map f).support = ⇑f '' L.support
参数：L : SummationFilter β；f : β ↪ γ；L.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
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
· 使用定理 `SummationFilter.map_filter`：∀ {β : Type u_2} {γ : Type u_3} (L : Summati
onFilter β) (f : β ↪ γ),   (L.map f).filter = Filter.map (Finset.map f) L.filter
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
-/
@[simp] lemma support_map (L : SummationFilter β) [L.NeBot] (f : β ↪ γ) :
    (L.map f).support = f '' L.support := by
  ext c
  rcases em (c ∈ range f) with ⟨b, rfl⟩ | hc
  · simp [support]
  · exact ⟨fun hc' ↦ have := hc'.exists; by grind, by grind⟩

/-- If `L` has well-defined support, then so does its map along an embedding. -/
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` has well-defined support, then so does its map along an embedding.
-/
instance (L : SummationFilter β) [HasSupport L] (f : β ↪ γ) : HasSupport (L.map f) := by
  constructor
  obtain (h | h) := L.neBot_or_eq_bot
  · simp only [map_filter, eventually_map, Finset.coe_map, image_subset_iff, support_map]
    filter_upwards [L.eventually_le_support] with a using by grind
  · simp [h]

/-- Pullback of a summation filter along an embedding. -/
/-
**SummationFilter.comap** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：{β : Type u_2} → {γ : Type u_3} → SummationFilter β → (γ ↪ β) → SummationF
ilter γ
参数：γ ↪ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of a summation filter along an embedding.
-/
@[simps] noncomputable def comap (L : SummationFilter β) (f : γ ↪ β) : SummationFilter γ where
  filter := L.filter.map (fun s ↦ s.preimage f f.injective.injOn)
/-
**SummationFilter.support_comap** 是 Mathlib 中的一个定理，位于命名空间 `SummationFilter`。
形式化陈述：∀ {β : Type u_2} {γ : Type u_3} (L : SummationFilter β) (f : γ ↪ β), (L.co
map f).support = ⇑f ⁻¹' L.support
参数：L : SummationFilter β；f : γ ↪ β；L.comap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SummationFilter.comap_filter`：∀ {β : Type u_2} {γ : Type u_3} (L : Summa
tionFilter β) (f : γ ↪ β),   (L.comap f).filter = Filter.map (fun s => s.preimag
e ⇑f ⋯) L.filter
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma support_comap (L : SummationFilter β) (f : γ ↪ β) :
    (L.comap f).support = f ⁻¹' L.support := by
  simp [support]

/-- If `L` has well-defined support, then so does its comap along an embedding. -/
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` has well-defined support, then so does its comap along an embedding.
-/
instance (L : SummationFilter β) [HasSupport L] (f : γ ↪ β) : HasSupport (L.comap f) := by
  constructor
  simp only [support_comap, comap_filter, eventually_map, Finset.coe_preimage]
  filter_upwards [L.eventually_le_support] with a using Set.preimage_mono
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : SummationFilter β) [LeAtTop L] (f : γ ↪ β) : LeAtTop (L.comap f) :=
  ⟨by rw [← support_eq_univ_iff]; simp⟩

end map_comap

section examples
/-!
## Examples of summation filters
-/
variable (β)

/-- **Unconditional summation**: a function on `β` is said to be *unconditionally summable* if its
partial sums over finite subsets converge with respect to the `atTop` filter. -/
/-
**SummationFilter.unconditional** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：(β : Type u_2) → SummationFilter β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Unconditional summation**: a function on `β` is said to be *unconditionally su
mmable* if its
partial sums over finite subsets converge with respect to the `atTop` filter.
-/
@[simps] def unconditional : SummationFilter β where
  filter := atTop
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (unconditional β).LeAtTop := ⟨le_rfl⟩
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (unconditional β).NeBot := ⟨atTop_neBot⟩

/-- This instance is useful for some measure-theoretic statements. -/
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is useful for some measure-theoretic statements.
-/
instance [Countable β] : IsCountablyGenerated (unconditional β).filter :=
  atTop.isCountablyGenerated

/-- The unconditional filter is preserved by comaps. -/
/-
**SummationFilter.comap_unconditional** 是 Mathlib 中的一个定理，位于命名空间 `SummationFilter
`。
形式化陈述：∀ {γ : Type u_3} {β : Type u_4} (f : γ ↪ β), (SummationFilter.unconditiona
l β).comap f = SummationFilter.unconditional γ
参数：f : γ ↪ β；SummationFilter.unconditional β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Finset.preimage_union`：preimage_union [DecidableEq α] [DecidableEq β] {f
 : α -> β} {s t : Finset β} (hst) : preimage (s union t) f hst = (preimage s f f
un _ hx₁ _ …
· 使用引理 `Finset.preimage_map`：preimage_map (f : α ↪ β) (s : Finset α) : (s.map f)
.preimage f f.injective.injOn = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.union_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, s ∪ t = t ↔ s ⊆ t
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Finset.map_subset_iff_subset_preimage`：map_subset_iff_subset_preimage {f
 : α ↪ β} {s : Finset α} {t : Finset β} : s.map f subseteq t ↔ s subseteq t.prei
mage f f.injective.injOn

--- 原说明 ---
The unconditional filter is preserved by comaps.
-/
@[simp] lemma comap_unconditional {β} (f : γ ↪ β) :
    (unconditional β).comap f = unconditional γ := by
  classical
  simp only [unconditional, comap]
  congr 1 with s
  simp only [mem_map, mem_atTop_sets, mem_preimage]
  constructor <;> rintro ⟨t, ht⟩
  · refine ⟨t.preimage f (by simp), fun x hx ↦ ?_⟩
    simpa [Finset.union_eq_right.mpr hx] using ht (t ∪ x.map f) t.subset_union_left
  · exact ⟨_, fun b hb ↦ ht _ (Finset.map_subset_iff_subset_preimage.mp hb)⟩

/-- If `β` is finite, then `unconditional β` is the only summation filter `L` on `β` satisfying
`L.LeAtTop` and `L.NeBot`. -/
/-
**SummationFilter.eq_unconditional_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Summatio
nFilter`。
形式化陈述：eq_unconditional_of_finite {β} [Finite β] (L : SummationFilter β) [L.LeAtT
op] [L.NeBot] : L = unconditional β
参数：L : SummationFilter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTop.atTop_eq`：∀ {α : Type u_3} [inst : Preorder α] {a : α}, IsTop a → 
Filter.atTop = Filter.principal (Set.Ici a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isTop_iff_eq_top`：isTop_iff_eq_top : IsTop a ↔ a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.top_eq_univ`：top_eq_univ : (⊤ : Finset α) = univ
· 使用定理 `Set.Ici_top`：Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤}
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `SummationFilter.LeAtTop.le_atTop`：∀ {β : Type u_2} {L : SummationFilter 
β} [self : L.LeAtTop], L.filter ≤ Filter.atTop
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.NeBot.ne'`：∀ {α : Type u_1} {f : Filter α} [self : f.NeBot], f ≠ 
⊥
· 使用定理 `SummationFilter.NeBot.ne_bot`：∀ {β : Type u_2} {L : SummationFilter β} [
self : L.NeBot], L.filter.NeBot
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.pure_le_iff`：pure_le_iff {a : α} {l : Filter α} : pure a <= l ↔ f
orall s in l, a in s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_singleton_eq_empty`：inter_singleton_eq_empty : s inter {a} = ∅
 ↔ a ∉ s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f

--- 原说明 ---
If `β` is finite, then `unconditional β` is the only summation filter `L` on `β`
 satisfying
`L.LeAtTop` and `L.NeBot`.
-/
lemma eq_unconditional_of_finite {β} [Finite β]
    (L : SummationFilter β) [L.LeAtTop] [L.NeBot] : L = unconditional β := by
  have := Fintype.ofFinite β
  have hAtTop : (atTop : Filter (Finset β)) = pure Finset.univ := by
    rw [(isTop_iff_eq_top.mpr rfl).atTop_eq (a := Finset.univ), ← Finset.top_eq_univ,
      Ici_top, principal_singleton]
  have hL := L.le_atTop
  have hL' : ∅ ∉ L.filter := empty_mem_iff_bot.not.mpr <| NeBot.ne_bot.ne'
  cases L with | mk F =>
  simp only [unconditional, hAtTop] at *
  congr 1
  refine eq_of_le_of_ge hL (pure_le_iff.mpr ?_)
  contrapose! hL'
  obtain ⟨s, hs, hs'⟩ := hL'
  simpa [inter_singleton_eq_empty.mpr hs'] using inter_mem hs (le_pure_iff.mp hL)

section conditionalTop

variable [Preorder β] [LocallyFiniteOrder β]

/-- **Conditional summation**, for ordered types `β` such that closed intervals `[x, y]` are
finite: this corresponds to limits of finite sums over larger and larger intervals. -/
/-
**SummationFilter.conditional** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：(β : Type u_2) → [inst : Preorder β] → [LocallyFiniteOrder β] → SummationF
ilter β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Conditional summation**, for ordered types `β` such that closed intervals `[x,
 y]` are
finite: this corresponds to limits of finite sums over larger and larger interva
ls.
-/
@[simps] def conditional : SummationFilter β where
  filter := (atBot ×ˢ atTop).map (fun p ↦ Finset.Icc p.1 p.2)
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (conditional β).LeAtTop := ⟨support_eq_univ_iff.mp <| by
  simpa [eq_univ_iff_forall, support, -eventually_and]
    using! fun x ↦ prod_mem_prod (eventually_le_atBot x) (eventually_ge_atTop x)⟩
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty β] [IsDirectedOrder β] [IsCodirectedOrder β] : (conditional β).NeBot :=
  ⟨by rw [conditional_filter]; infer_instance⟩
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCountablyGenerated (atTop : Filter β)] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (conditional β).filter :=
  map.isCountablyGenerated ..

/-- When `β` has a bottom element, `conditional β` is given by limits over finite intervals
`{y | y ≤ x}` as `x → atTop`. -/
@[simp high] -- want this to be prioritized over `conditional_filter` when they both apply
/-
**SummationFilter.conditional_filter_eq_map_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Summa
tionFilter`。
形式化陈述：conditional_filter_eq_map_Iic {γ} [PartialOrder γ] [LocallyFiniteOrder γ] 
[OrderBot γ] : (conditional γ).filter = atTop.map Finset.Iic
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SummationFilter.conditional_filter`：∀ (β : Type u_2) [inst : Preorder β]
 [inst_1 : LocallyFiniteOrder β],   (SummationFilter.conditional β).filter = Fil
ter.map (fun p => Finset…
· 使用定理 `IsBot.atBot_eq`：∀ {α : Type u_3} [inst : Preorder α] {a : α}, IsBot a → 
Filter.atBot = Filter.principal (Set.Iic a)
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
· 使用定理 `Set.Iic_bot`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderBot
 α], Set.Iic ⊥ = {⊥}
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.pure_prod`：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (
Prod.mk a) f
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `β` has a bottom element, `conditional β` is given by limits over finite in
tervals
`{y | y ≤ x}` as `x → atTop`.
-/
lemma conditional_filter_eq_map_Iic {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderBot γ] :
    (conditional γ).filter = atTop.map Finset.Iic := by
  simp [isBot_bot.atBot_eq, comp_def, Finset.Icc_bot]

/-- When `β` has a top element, `conditional β` is given by limits over finite intervals
`{y | x ≤ y}` as `x → atBot`. -/
@[simp high] -- want this to be prioritized over `conditional_filter` when they both apply
/-
**SummationFilter.conditional_filter_eq_map_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Summa
tionFilter`。
形式化陈述：conditional_filter_eq_map_Ici {γ} [PartialOrder γ] [LocallyFiniteOrder γ] 
[OrderTop γ] : (conditional γ).filter = atBot.map Finset.Ici
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SummationFilter.conditional_filter`：∀ (β : Type u_2) [inst : Preorder β]
 [inst_1 : LocallyFiniteOrder β],   (SummationFilter.conditional β).filter = Fil
ter.map (fun p => Finset…
· 使用定理 `IsTop.atTop_eq`：∀ {α : Type u_3} [inst : Preorder α] {a : α}, IsTop a → 
Filter.atTop = Filter.principal (Set.Ici a)
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
· 使用定理 `Set.Ici_top`：Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤}
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `β` has a top element, `conditional β` is given by limits over finite inter
vals
`{y | x ≤ y}` as `x → atBot`.
-/
lemma conditional_filter_eq_map_Ici {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderTop γ] :
    (conditional γ).filter = atBot.map Finset.Ici := by
  simp [isTop_top.atTop_eq, comp_def, Finset.Icc_top]

/-- Conditional summation over `ℕ` is given by limits of sums over `Finset.range n` as `n → ∞`. -/
@[simp high + 1] -- want this to be prioritized over `conditional_filter_eq_map_Ici`
/-
**SummationFilter.conditional_filter_eq_map_range** 是 Mathlib 中的一个引理，位于命名空间 `Sum
mationFilter`。
形式化陈述：conditional_filter_eq_map_range : (conditional Nat).filter = atTop.map Fin
set.range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SummationFilter.conditional_filter_eq_map_Iic`：conditional_filter_eq_map
_Iic {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderBot γ] : (conditional γ).
filter = atTop.map Finset.Iic
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Conditional summation over `ℕ` is given by limits of sums over `Finset.range n` 
as `n → ∞`.
-/
lemma conditional_filter_eq_map_range : (conditional ℕ).filter = atTop.map Finset.range := by
  have (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by ext x; simp [Nat.lt_succ_iff]
  simp only [conditional_filter_eq_map_Iic, funext this]
  apply le_antisymm <;>
      rw [← Tendsto] <;>
      simp only [tendsto_atTop', mem_map, mem_atTop_sets, mem_preimage] <;>
      rintro s ⟨a, ha⟩
  · exact ⟨a + 1, fun b hb ↦ ha (b + 1) (by lia)⟩
  · exact ⟨a + 1, fun b hb ↦ by convert! ha (b - 1) (by lia); lia⟩

end conditionalTop

end examples

end SummationFilter

