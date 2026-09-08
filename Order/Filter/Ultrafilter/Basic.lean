/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.ZornAtoms

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `hyperfilter`: the ultrafilter extending the cofinite filter.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

open Set Filter

namespace Ultrafilter

variable {f : Ultrafilter α} {s : Set α}

/-
**Ultrafilter.finite_sUnion_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：finite_sUnion_mem_iff {s : Set (Set α)} (hs : s.Finite) : ⋃₀ s in f ↔ exis
ts t in s, t in f
参数：Set α；hs : s.Finite。
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
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem finite_sUnion_mem_iff {s : Set (Set α)} (hs : s.Finite) : ⋃₀ s ∈ f ↔ ∃ t ∈ s, t ∈ f := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ his => simp [union_mem_iff, his, or_and_right, exists_or]
/-
**Ultrafilter.finite_biUnion_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：finite_biUnion_mem_iff {is : Set β} {s : β -> Set α} (his : is.Finite) : (
⋃ i in is, s i) in f ↔ exists i in is, s i in f
参数：his : is.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ultrafilter.finite_sUnion_mem_iff`：finite_sUnion_mem_iff {s : Set (Set α
)} (hs : s.Finite) : ⋃₀ s in f ↔ exists t in s, t in f
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finite_biUnion_mem_iff {is : Set β} {s : β → Set α} (his : is.Finite) :
    (⋃ i ∈ is, s i) ∈ f ↔ ∃ i ∈ is, s i ∈ f := by
  simp only [← sUnion_image, finite_sUnion_mem_iff (his.image s), exists_mem_image]

set_option backward.isDefEq.respectTransparency false in
/-
**Ultrafilter.eventually_exists_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ultrafilter`。
形式化陈述：eventually_exists_mem_iff {is : Set β} {P : β -> α -> Prop} (his : is.Fini
te) : (forallᶠ i in f, exists a in is, P a i) ↔ exists a in is, forallᶠ i in f, 
P a i
参数：his : is.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Ultrafilter.finite_biUnion_mem_iff`：finite_biUnion_mem_iff {is : Set β} 
{s : β -> Set α} (his : is.Finite) : (⋃ i in is, s i) in f ↔ exists i in is, s i
 in f
-/
lemma eventually_exists_mem_iff {is : Set β} {P : β → α → Prop} (his : is.Finite) :
    (∀ᶠ i in f, ∃ a ∈ is, P a i) ↔ ∃ a ∈ is, ∀ᶠ i in f, P a i := by
  simp only [Filter.Eventually, Ultrafilter.mem_coe]
  convert! f.finite_biUnion_mem_iff his (s := P) with i
  aesop
/-
**Ultrafilter.eventually_exists_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ultrafilter`。
形式化陈述：eventually_exists_iff [Finite β] {P : β -> α -> Prop} : (forallᶠ i in f, e
xists a, P a i) ↔ exists a, forallᶠ i in f, P a i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Ultrafilter.eventually_exists_mem_iff`：eventually_exists_mem_iff {is : S
et β} {P : β -> α -> Prop} (his : is.Finite) : (forallᶠ i in f, exists a in is, 
P a i) ↔ exists a in is, fo…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma eventually_exists_iff [Finite β] {P : β → α → Prop} :
    (∀ᶠ i in f, ∃ a, P a i) ↔ ∃ a, ∀ᶠ i in f, P a i := by
  simpa using eventually_exists_mem_iff (f := f) (P := P) Set.finite_univ
/-
**Ultrafilter.eq_pure_of_finite_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eq_pure_of_finite_mem (h : s.Finite) (h' : s in f) : exists x in s, f = pu
re x
参数：h : s.Finite；h' : s in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ultrafilter.finite_biUnion_mem_iff`：finite_biUnion_mem_iff {is : Set β} 
{s : β -> Set α} (his : is.Finite) : (⋃ i in is, s i) in f ↔ exists i in is, s i
 in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Ultrafilter.eq_of_le`：eq_of_le {f g : Ultrafilter α} (h : (f : Filter α)
 <= g) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f
-/
theorem eq_pure_of_finite_mem (h : s.Finite) (h' : s ∈ f) : ∃ x ∈ s, f = pure x := by
  rw [← biUnion_of_singleton s] at h'
  rcases (Ultrafilter.finite_biUnion_mem_iff h).mp h' with ⟨a, has, haf⟩
  exact ⟨a, has, eq_of_le (Filter.le_pure_iff.2 haf)⟩
/-
**Ultrafilter.eq_pure_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eq_pure_of_finite [Finite α] (f : Ultrafilter α) : exists a, f = pure a
参数：f : Ultrafilter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Ultrafilter.eq_pure_of_finite_mem`：eq_pure_of_finite_mem (h : s.Finite) 
(h' : s in f) : exists x in s, f = pure x
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem eq_pure_of_finite [Finite α] (f : Ultrafilter α) : ∃ a, f = pure a :=
  (eq_pure_of_finite_mem finite_univ univ_mem).imp fun _ ⟨_, ha⟩ => ha
/-
**Ultrafilter.le_cofinite_or_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：le_cofinite_or_eq_pure (f : Ultrafilter α) : (f : Filter α) <= cofinite ∨ 
exists a, f = pure a
参数：f : Ultrafilter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.disjoint_cofinite_right`：disjoint_cofinite_right : Disjoint l cof
inite ↔ exists s in l, Set.Finite s
· 使用定理 `Ultrafilter.disjoint_iff_not_le`：disjoint_iff_not_le {f : Ultrafilter α}
 {g : Filter α} : Disjoint (↑f) g ↔ ¬↑f <= g
· 使用定理 `Ultrafilter.eq_pure_of_finite_mem`：eq_pure_of_finite_mem (h : s.Finite) 
(h' : s in f) : exists x in s, f = pure x
-/
theorem le_cofinite_or_eq_pure (f : Ultrafilter α) : (f : Filter α) ≤ cofinite ∨ ∃ a, f = pure a :=
  or_iff_not_imp_left.2 fun h =>
    let ⟨_, hs, hfin⟩ := Filter.disjoint_cofinite_right.1 (disjoint_iff_not_le.2 h)
    let ⟨a, _, hf⟩ := eq_pure_of_finite_mem hfin hs
    ⟨a, hf⟩
/-
**Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty** 是 Mathlib 中的一个定理，位于命
名空间 `Ultrafilter`。
形式化陈述：exists_ultrafilter_of_finite_inter_nonempty (S : Set (Set α)) (cond : fora
ll T : Finset (Set α), (↑T : Set (Set α)) subseteq S -> (⋂₀ (↑T : Set (Set α))).
Nonempty) : exists F : Ultrafilter α, S subseteq F.sets
参数：S : Set (Set α)；cond : forall T : Finset (Set α), (↑T : Set (Set α)) subseteq
 S -> (⋂₀ (↑T : Set (Set α))).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.generate_neBot_iff`：generate_neBot_iff {s : Set (Set α)} : NeBot 
(generate s) ↔ forall t, t subseteq s -> t.Finite -> (⋂₀ t).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
-/
theorem exists_ultrafilter_of_finite_inter_nonempty (S : Set (Set α))
    (cond : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ S → (⋂₀ (↑T : Set (Set α))).Nonempty) :
    ∃ F : Ultrafilter α, S ⊆ F.sets :=
  haveI : NeBot (generate S) :=
    generate_neBot_iff.2 fun _ hts ht =>
      ht.coe_toFinset ▸ cond ht.toFinset (ht.coe_toFinset.symm ▸ hts)
  ⟨of (generate S), fun _ ht => (of_le <| generate S) <| GenerateSets.basic ht⟩

end Ultrafilter

namespace Filter

open Ultrafilter

@[to_dual]
/-
**Filter.atTop_eq_pure_of_isTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：atTop_eq_pure_of_isTop [PartialOrder α] {x : α} (hx : IsTop x) : (atTop : 
Filter α) = pure x
参数：hx : IsTop x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.OrderTop.atTop_eq`：∀ (α : Type u_6) [inst : PartialOrder α] [inst
_1 : OrderTop α], Filter.atTop = pure ⊤
-/
lemma atTop_eq_pure_of_isTop [PartialOrder α] {x : α} (hx : IsTop x) :
    (atTop : Filter α) = pure x :=
  { top := x, le_top := hx : OrderTop α }.atTop_eq

/-- The `tendsto` relation can be checked on ultrafilters. -/
/-
**Filter.tendsto_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_ultrafilter (f : α -> β) (l₁ : Filter α) (l₂ : Filter β) : Ten
dsto f l₁ l₂ ↔ forall g : Ultrafilter α, ↑g <= l₁ -> Tendsto f g l₂
参数：f : α -> β；l₁ : Filter α；l₂ : Filter β。
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
· 使用定理 `Filter.le_iff_ultrafilter`：le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ <=
 f₂ ↔ forall g : Ultrafilter α, ↑g <= f₁ -> ↑g <= f₂

--- 原说明 ---
The `tendsto` relation can be checked on ultrafilters.
-/
theorem tendsto_iff_ultrafilter (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ l₁ → Tendsto f g l₂ := by
  simpa only [tendsto_iff_comap] using le_iff_ultrafilter

section Hyperfilter

variable (α) [Infinite α]

/-- The ultrafilter extending the cofinite filter. -/
/-
**Filter.hyperfilter** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：hyperfilter : Ultrafilter α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ultrafilter extending the cofinite filter.
-/
noncomputable def hyperfilter : Ultrafilter α :=
  Ultrafilter.of cofinite

variable {α}
/-
**Filter.hyperfilter_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hyperfilter_le_cofinite : ↑(hyperfilter α) <= @cofinite α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
-/
theorem hyperfilter_le_cofinite : ↑(hyperfilter α) ≤ @cofinite α :=
  Ultrafilter.of_le cofinite
/-
**Filter._root_.Nat.hyperfilter_le_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.hyperfilter_le_atTop : (hyperfilter ℕ).toFilter ≤ atTop :=
  hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop

@[simp]
/-
**Filter.bot_ne_hyperfilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bot_ne_hyperfilter : (⊥ : Filter α) != hyperfilter α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
-/
theorem bot_ne_hyperfilter : (⊥ : Filter α) ≠ hyperfilter α :=
  (NeBot.ne inferInstance).symm
/-
**Filter.notMem_hyperfilter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：notMem_hyperfilter_of_finite {s : Set α} (hf : s.Finite) : s ∉ hyperfilter
 α
参数：hf : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.compl_notMem`：compl_notMem {f : Filter α} {s : Set α} [NeBot f] (
h : s in f) : sᶜ ∉ f
· 使用定理 `Filter.hyperfilter_le_cofinite`：hyperfilter_le_cofinite : ↑(hyperfilter 
α) <= @cofinite α
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
-/
theorem notMem_hyperfilter_of_finite {s : Set α} (hf : s.Finite) : s ∉ hyperfilter α := fun hy =>
  compl_notMem hy <| hyperfilter_le_cofinite hf.compl_mem_cofinite

alias _root_.Set.Finite.notMem_hyperfilter := notMem_hyperfilter_of_finite
/-
**Filter.compl_mem_hyperfilter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_hyperfilter_of_finite {s : Set α} (hf : Set.Finite s) : sᶜ in hy
perfilter α
参数：hf : Set.Finite s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
· 使用定理 `Set.Finite.notMem_hyperfilter`：∀ {α : Type u} [inst : Infinite α] {s : S
et α}, s.Finite → s ∉ Filter.hyperfilter α
-/
theorem compl_mem_hyperfilter_of_finite {s : Set α} (hf : Set.Finite s) : sᶜ ∈ hyperfilter α :=
  compl_mem_iff_notMem.2 hf.notMem_hyperfilter

alias _root_.Set.Finite.compl_mem_hyperfilter := compl_mem_hyperfilter_of_finite
/-
**Filter.mem_hyperfilter_of_finite_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_hyperfilter_of_finite_compl {s : Set α} (hf : Set.Finite sᶜ) : s in hy
perfilter α
参数：hf : Set.Finite sᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.compl_mem_hyperfilter`：∀ {α : Type u} [inst : Infinite α] {s 
: Set α}, s.Finite → sᶜ ∈ Filter.hyperfilter α
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem mem_hyperfilter_of_finite_compl {s : Set α} (hf : Set.Finite sᶜ) : s ∈ hyperfilter α :=
  compl_compl s ▸ hf.compl_mem_hyperfilter

end Hyperfilter

end Filter

