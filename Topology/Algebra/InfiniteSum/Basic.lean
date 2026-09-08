/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Lee
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Order.Filter.AtTopBot.BigOperators

import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Lemmas on infinite sums and products in topological monoids

This file contains many simple lemmas on `tsum`, `HasSum` etc, which are placed here in order to
keep the basic file of definitions as short as possible.

Results requiring a group (rather than monoid) structure on the target should go in `Group.lean`.

-/

public section

noncomputable section

open Filter Finset Function Topology SummationFilter

variable {α β γ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]
variable {f g : β → α} {a b : α} {L : SummationFilter β}

/-- Constant one function has product `1` -/
@[to_additive (attr := simp) /-- Constant zero function has sum `0` -/]
/-
**hasProd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
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
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1

--- 原说明 ---
Constant one function has product `1`
-/
theorem hasProd_one : HasProd (fun _ ↦ 1 : β → α) 1 L := by simp [HasProd, tendsto_const_nhds]

@[to_additive (attr := simp)]
/-
**hasProd_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_empty [IsEmpty β] : HasProd f 1 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
-/
theorem hasProd_empty [IsEmpty β] : HasProd f 1 L := by
  convert! hasProd_one

@[to_additive (attr := nontriviality)]
/-
**HasProd.of_subsingleton_cod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.of_subsingleton_cod [Subsingleton α] : HasProd f 1 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
-/
theorem HasProd.of_subsingleton_cod [Subsingleton α] : HasProd f 1 L := by
  convert! hasProd_one

@[to_additive (attr := simp)]
/-
**multipliable_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_one : Multipliable (fun _ => 1 : β -> α) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
-/
theorem multipliable_one : Multipliable (fun _ ↦ 1 : β → α) L :=
  hasProd_one.multipliable

@[to_additive (attr := simp)]
/-
**multipliable_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_empty [IsEmpty β] : Multipliable f L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `hasProd_empty`：hasProd_empty [IsEmpty β] : HasProd f 1 L
-/
theorem multipliable_empty [IsEmpty β] : Multipliable f L :=
  hasProd_empty.multipliable

@[to_additive (attr := nontriviality)]
/-
**Multipliable.of_subsingleton_cod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.of_subsingleton_cod [Subsingleton α] : Multipliable f L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.of_subsingleton_cod`：HasProd.of_subsingleton_cod [Subsingleton α
] : HasProd f 1 L
-/
theorem Multipliable.of_subsingleton_cod [Subsingleton α] : Multipliable f L :=
  HasProd.of_subsingleton_cod.multipliable

/-- See `multipliable_congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/
@[to_additive /-- See `summable_congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/]
/-
**multipliable_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_congr (hfg : forall b, f b = g b) : Multipliable f L ↔ Multip
liable g L
参数：hfg : forall b, f b = g b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem multipliable_congr (hfg : ∀ b, f b = g b) : Multipliable f L ↔ Multipliable g L :=
  iff_of_eq (congr_arg (Multipliable · L) <| funext hfg)

/-- See `Multipliable.congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/
@[to_additive /-- See `Summable.congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/]
/-
**Multipliable.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.congr (hf : Multipliable f L) (hfg : forall b, f b = g b) : M
ultipliable g L
参数：hf : Multipliable f L；hfg : forall b, f b = g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `multipliable_congr`：multipliable_congr (hfg : forall b, f b = g b) : Mul
tipliable f L ↔ Multipliable g L
-/
theorem Multipliable.congr (hf : Multipliable f L) (hfg : ∀ b, f b = g b) : Multipliable g L :=
  (multipliable_congr hfg).mp hf

@[to_additive]
/-
**HasProd.congr_fun** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.congr_fun (hf : HasProd f a L) (h : forall x : β, g x = f x) : Has
Prod g a L
参数：hf : HasProd f a L；h : forall x : β, g x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma HasProd.congr_fun (hf : HasProd f a L) (h : ∀ x : β, g x = f x) : HasProd g a L :=
  (funext h : g = f) ▸ hf

@[to_additive]
/-
**HasProd.hasProd_of_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.hasProd_of_prod_eq {g : γ -> α} (h_eq : forall u : Finset γ, exist
s v : Finset β, forall v', v subseteq v' -> exists u', u subseteq u' ∧ ∏ x in u'
, g x = ∏ b in v', f b) (hf : HasProd g a) : HasProd f a
参数：h_eq : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' -> 
exists u', u subseteq u' ∧ ∏ x in u', g x = ∏ b in v', f b；hf : HasProd g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_atTop_finsetProd_le_of_prod_eq`：Filter.map_atTop_finsetProd_l
e_of_prod_eq {f : α -> M} {g : β -> M} (h_eq : forall u : Finset β, exists v : F
inset α, forall v', v subseteq …
-/
theorem HasProd.hasProd_of_prod_eq {g : γ → α}
    (h_eq : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' →
      ∃ u', u ⊆ u' ∧ ∏ x ∈ u', g x = ∏ b ∈ v', f b)
    (hf : HasProd g a) : HasProd f a :=
  le_trans (map_atTop_finsetProd_le_of_prod_eq h_eq) hf

@[to_additive]
/-
**hasProd_iff_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_iff_hasProd {g : γ -> α} (h₁ : forall u : Finset γ, exists v : Fin
set β, forall v', v subseteq v' -> exists u', u subseteq u' ∧ ∏ x in u', g x = ∏
 b in v', f b) (h₂ : forall v : Finset β, exists u : Finset γ, forall u', u subs
eteq u' -> exists v', v subseteq v' ∧ ∏ b in v', f b = ∏ x in u', g x) : HasProd
 f a ↔ HasProd g a
参数：h₁ : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' -> ex
ists u', u subseteq u' ∧ ∏ x in u', g x = ∏ b in v', f b；h₂ : forall v : Finset 
β, exists u : Finset γ, forall u', u subseteq u' -> exists v', v subseteq v' ∧ ∏
 b in v', f b = ∏ x in u', g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.hasProd_of_prod_eq`：HasProd.hasProd_of_prod_eq {g : γ -> α} (h_e
q : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' -> exists
 u', u subseteq …
-/
theorem hasProd_iff_hasProd {g : γ → α}
    (h₁ : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' →
      ∃ u', u ⊆ u' ∧ ∏ x ∈ u', g x = ∏ b ∈ v', f b)
    (h₂ : ∀ v : Finset β, ∃ u : Finset γ, ∀ u', u ⊆ u' →
      ∃ v', v ⊆ v' ∧ ∏ b ∈ v', f b = ∏ x ∈ u', g x) :
    HasProd f a ↔ HasProd g a :=
  ⟨HasProd.hasProd_of_prod_eq h₂, HasProd.hasProd_of_prod_eq h₁⟩

@[to_additive]
/-
**Function.Injective.multipliable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.multipliable_iff {g : γ -> β} (hg : Injective g) (hf : 
forall x ∉ Set.range g, f x = 1) : Multipliable (f ∘ g) ↔ Multipliable f
参数：hg : Injective g；hf : forall x ∉ Set.range g, f x = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Function.Injective.hasProd_iff`：Function.Injective.hasProd_iff {g : γ ->
 β} (hg : Injective g) (hf : forall x, x ∉ Set.range g -> f x = 1) : HasProd (f 
∘ g) a ↔ HasProd f a
-/
theorem Function.Injective.multipliable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x ∉ Set.range g, f x = 1) : Multipliable (f ∘ g) ↔ Multipliable f :=
  exists_congr fun _ ↦ hg.hasProd_iff hf
/-
**hasProd_extend_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] {f : β → α} {a : α}   {g : β → γ}, Function.Injective g
 → (HasProd (Function.extend g f 1) a ↔ HasProd f a)
参数：HasProd (Function.extend g f 1) a ↔ HasProd f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.hasProd_iff`：Function.Injective.hasProd_iff {g : γ ->
 β} (hg : Injective g) (hf : forall x, x ∉ Set.range g -> f x = 1) : HasProd (f 
∘ g) a ↔ HasProd f a
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `Function.extend_comp`：extend_comp (hf : Injective f) (g : α -> γ) (e' : 
β -> γ) : extend f g e' ∘ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] theorem hasProd_extend_one {g : β → γ} (hg : Injective g) :
    HasProd (extend g f 1) a ↔ HasProd f a := by
  rw [← hg.hasProd_iff, extend_comp hg]
  exact extend_apply' _ _
/-
**multipliable_extend_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] {f : β → α}   {g : β → γ}, Function.Injective g → (Mult
ipliable (Function.extend g f 1) ↔ Multipliable f)
参数：Multipliable (Function.extend g f 1) ↔ Multipliable f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasProd_extend_one`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {g : β → γ}
, Functi…
-/
@[to_additive (attr := simp)] theorem multipliable_extend_one {g : β → γ} (hg : Injective g) :
    Multipliable (extend g f 1) ↔ Multipliable f :=
  exists_congr fun _ ↦ hasProd_extend_one hg

@[to_additive]
/-
**hasProd_subtype_iff_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_subtype_iff_mulIndicator {s : Set β} : HasProd (f ∘ (↑) : s -> α) 
a ↔ HasProd (s.mulIndicator f) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulIndicator_range_comp`：mulIndicator_range_comp {ι : Sort*} (f : ι 
-> α) (g : α -> M) : mulIndicator (range f) g ∘ f = g ∘ f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `hasProd_subtype_iff_of_mulSupport_subset`：hasProd_subtype_iff_of_mulSupp
ort_subset {s : Set β} (hf : mulSupport f subseteq s) : HasProd (f ∘ (↑) : s -> 
α) a ↔ HasProd f a
· 使用引理 `Set.mulSupport_mulIndicator_subset`：mulSupport_mulIndicator_subset : mul
Support (s.mulIndicator f) subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasProd_subtype_iff_mulIndicator {s : Set β} :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd (s.mulIndicator f) a := by
  rw [← Set.mulIndicator_range_comp, Subtype.range_coe,
    hasProd_subtype_iff_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]

@[to_additive]
/-
**multipliable_subtype_iff_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_subtype_iff_mulIndicator {s : Set β} : Multipliable (f ∘ (↑) 
: s -> α) ↔ Multipliable (s.mulIndicator f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a
-/
theorem multipliable_subtype_iff_mulIndicator {s : Set β} :
    Multipliable (f ∘ (↑) : s → α) ↔ Multipliable (s.mulIndicator f) :=
  exists_congr fun _ ↦ hasProd_subtype_iff_mulIndicator

@[to_additive (attr := simp)]
/-
**hasProd_subtype_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_subtype_mulSupport : HasProd (f ∘ (↑) : mulSupport f -> α) a ↔ Has
Prod f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_subtype_iff_of_mulSupport_subset`：hasProd_subtype_iff_of_mulSupp
ort_subset {s : Set β} (hf : mulSupport f subseteq s) : HasProd (f ∘ (↑) : s -> 
α) a ↔ HasProd f a
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem hasProd_subtype_mulSupport : HasProd (f ∘ (↑) : mulSupport f → α) a ↔ HasProd f a :=
  hasProd_subtype_iff_of_mulSupport_subset <| Set.Subset.refl _

@[to_additive]
/-
**Finset.multipliable** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] (s : Finset β) (f : β → α),   Multipliable (f ∘ Subtype.val)
参数：s : Finset β；f : β → α；f ∘ Subtype.val。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `Finset.hasProd`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [i
nst_1 : TopologicalSpace α] (s : Finset β) (f : β → α)   (L : optParam (Summatio
nFil…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
protected theorem Finset.multipliable (s : Finset β) (f : β → α) :
    Multipliable (f ∘ (↑) : (↑s : Set β) → α) :=
  (s.hasProd f).multipliable

@[to_additive]
/-
**Set.Finite.multipliable** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] {s : Set β},   s.Finite → ∀ (f : β → α), Multipliable (f ∘ Subtype.val
)
参数：f : β → α；f ∘ Subtype.val。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.multipliable`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid 
α] [inst_1 : TopologicalSpace α] (s : Finset β) (f : β → α),   Multipliable (f ∘
 Subtype.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
protected theorem Set.Finite.multipliable {s : Set β} (hs : s.Finite) (f : β → α) :
    Multipliable (f ∘ (↑) : s → α) := by
  have := hs.toFinset.multipliable f
  rwa [hs.coe_toFinset] at this

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**multipliable_of_hasFiniteMulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_of_hasFiniteMulSupport [L.HasSupport] (h : HasFiniteMulSuppor
t f) : Multipliable f L
参数：h : HasFiniteMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multipliable_of_ne_finset_one`：multipliable_of_ne_finset_one (hf : foral
l b ∉ s, f b = 1) [L.HasSupport] : Multipliable f L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem multipliable_of_hasFiniteMulSupport [L.HasSupport] (h : HasFiniteMulSupport f) :
    Multipliable f L := by
  apply multipliable_of_ne_finset_one (s := h.toFinset); simp

@[deprecated (since := "2026-03-03")] alias
  multipliable_of_finite_mulSupport := multipliable_of_hasFiniteMulSupport

@[deprecated (since := "2026-03-03")] alias
  summable_of_finite_support := summable_of_hasFiniteSupport

@[to_additive]
/-
**Multipliable.of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.of_finite [Finite β] [L.HasSupport] {f : β -> α} : Multipliab
le f L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multipliable_of_hasFiniteMulSupport`：multipliable_of_hasFiniteMulSupport
 [L.HasSupport] (h : HasFiniteMulSupport f) : Multipliable f L
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma Multipliable.of_finite [Finite β] [L.HasSupport] {f : β → α} : Multipliable f L :=
  multipliable_of_hasFiniteMulSupport <| Set.finite_univ.subset (Set.subset_univ _)

@[to_additive]
/-
**hasProd_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_single {f : β -> α} (b : β) (hf : forall (b') (_ : b' != b), f b' 
= 1) (L
参数：b : β；hf : forall (b') (_ : b' != b), f b' = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_prod_of_ne_finset_one`：hasProd_prod_of_ne_finset_one (hf : foral
l b ∉ s, f b = 1) [L.LeAtTop] : HasProd f (∏ b in s, f b) L
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem hasProd_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 1)
    (L := unconditional β) [L.LeAtTop] : HasProd f (f b) L :=
  suffices HasProd f (∏ b' ∈ {b}, f b') L by simpa using this
  hasProd_prod_of_ne_finset_one <| by simpa [hf]

@[to_additive (attr := simp)]
/-
**hasProd_unique** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProd_unique [Unique β] (f : β -> α) (L
参数：f : β -> α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_single`：hasProd_single {f : β -> α} (b : β) (hf : forall (b') (_
 : b' != b), f b' = 1) (L
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
lemma hasProd_unique [Unique β] (f : β → α) (L := unconditional β) [L.LeAtTop] :
    HasProd f (f default) L :=
  hasProd_single default (fun _ hb ↦ False.elim <| hb <| Unique.uniq ..) L

@[to_additive (attr := simp)]
/-
**hasProd_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProd_singleton (m : β) (f : β -> α) : HasProd (({m} : Set β).domRestric
t f) (f m)
参数：m : β；f : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProd_unique`：hasProd_unique [Unique β] (f : β -> α) (L
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
lemma hasProd_singleton (m : β) (f : β → α) : HasProd (({m} : Set β).domRestrict f) (f m) :=
  hasProd_unique (Set.domRestrict {m} f)

@[to_additive]
/-
**hasProd_ite_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (L
参数：b : β；· = b；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_single`：hasProd_single {f : β -> α} (b : β) (hf : forall (b') (_
 : b' != b), f b' = 1) (L
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' ↦ if b' = b then a else 1) a L :=
  suffices HasProd (fun b' ↦ if b' = b then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' ↦ if_neg hb') (L := L)

@[to_additive]
/-
**hasProd_ite_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_ite_eq' (b : β) [DecidablePred (b = ·)] (a : α) (L
参数：b : β；b = ·；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_single`：hasProd_single {f : β -> α} (b : β) (hf : forall (b') (_
 : b' != b), f b' = 1) (L
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasProd_ite_eq' (b : β) [DecidablePred (b = ·)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' ↦ if b = b' then a else 1) a L :=
  suffices HasProd (fun b' ↦ if b = b' then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' ↦ if_neg hb'.symm) (L := L)

@[to_additive]
/-
**Equiv.hasProd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ HasProd f a
参数：e : γ ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.hasProd_iff`：Function.Injective.hasProd_iff {g : γ ->
 β} (hg : Injective g) (hf : forall x, x ∉ Set.range g -> f x = 1) : HasProd (f 
∘ g) a ↔ HasProd f a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ HasProd f a :=
  e.injective.hasProd_iff <| by simp

@[to_additive]
/-
**Function.Injective.hasProd_range_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.hasProd_range_iff {g : γ -> β} (hg : Injective g) : Has
Prod (fun x : Set.range g => f x) a ↔ HasProd (f ∘ g) a
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
-/
theorem Function.Injective.hasProd_range_iff {g : γ → β} (hg : Injective g) :
    HasProd (fun x : Set.range g ↦ f x) a ↔ HasProd (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasProd_iff.symm

@[to_additive]
/-
**Equiv.multipliable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.multipliable_iff (e : γ ≃ β) : Multipliable (f ∘ e) ↔ Multipliable f
参数：e : γ ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
-/
theorem Equiv.multipliable_iff (e : γ ≃ β) : Multipliable (f ∘ e) ↔ Multipliable f :=
  exists_congr fun _ ↦ e.hasProd_iff

@[to_additive]
/-
**Equiv.hasProd_iff_of_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.hasProd_iff_of_mulSupport {g : γ -> α} (e : mulSupport f ≃ mulSuppor
t g) (he : forall x : mulSupport f, g (e x) = f x) : HasProd f a ↔ HasProd g a
参数：e : mulSupport f ≃ mulSupport g；he : forall x : mulSupport f, g (e x) = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasProd_subtype_mulSupport`：hasProd_subtype_mulSupport : HasProd (f ∘ (↑
) : mulSupport f -> α) a ↔ HasProd f a
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Equiv.hasProd_iff_of_mulSupport {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x : mulSupport f, g (e x) = f x) : HasProd f a ↔ HasProd g a := by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasProd_subtype_mulSupport, ← this, e.hasProd_iff, hasProd_subtype_mulSupport]

@[to_additive]
/-
**hasProd_iff_hasProd_of_ne_one_bij** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_iff_hasProd_of_ne_one_bij {g : γ -> α} (i : mulSupport g -> β) (hi
 : Injective i) (hf : mulSupport f subseteq Set.range i) (hfg : forall x, f (i x
) = g x) : HasProd f a ↔ HasProd g a
参数：i : mulSupport g -> β；hi : Injective i；hf : mulSupport f subseteq Set.range i
；hfg : forall x, f (i x) = g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.hasProd_iff_of_mulSupport`：Equiv.hasProd_iff_of_mulSupport {g : γ 
-> α} (e : mulSupport f ≃ mulSupport g) (he : forall x : mulSupport f, g (e x) =
 f x) : HasProd f a ↔…
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem hasProd_iff_hasProd_of_ne_one_bij {g : γ → α} (i : mulSupport g → β)
    (hi : Injective i) (hf : mulSupport f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasProd f a ↔ HasProd g a :=
  Iff.symm <|
    Equiv.hasProd_iff_of_mulSupport
      (Equiv.ofBijective (fun x ↦ ⟨i x, fun hx ↦ x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun _ _ h ↦ hi <| Subtype.ext_iff.1 h, fun y ↦
          (hf y.coe_prop).imp fun _ hx ↦ Subtype.ext hx⟩)
      hfg

@[to_additive]
/-
**Equiv.multipliable_iff_of_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.multipliable_iff_of_mulSupport {g : γ -> α} (e : mulSupport f ≃ mulS
upport g) (he : forall x : mulSupport f, g (e x) = f x) : Multipliable f ↔ Multi
pliable g
参数：e : mulSupport f ≃ mulSupport g；he : forall x : mulSupport f, g (e x) = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Equiv.hasProd_iff_of_mulSupport`：Equiv.hasProd_iff_of_mulSupport {g : γ 
-> α} (e : mulSupport f ≃ mulSupport g) (he : forall x : mulSupport f, g (e x) =
 f x) : HasProd f a ↔…
-/
theorem Equiv.multipliable_iff_of_mulSupport {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x : mulSupport f, g (e x) = f x) : Multipliable f ↔ Multipliable g :=
  exists_congr fun _ ↦ e.hasProd_iff_of_mulSupport he

@[to_additive]
/-
**HasProd.map** 是 Mathlib 中的一个定理，位于命名空间 `HasProd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] {f : β → α} {a : α}   {L : SummationFilter β} [inst_2 :
 CommMonoid γ] [inst_3 : TopologicalSpace γ],   HasProd f a L →     ∀ {G : Type 
u_4} [inst_4 : FunLike G α γ] [MonoidHomClass G α γ] (g : G), Continuous ⇑g → Ha
sProd (⇑g ∘ f) (g a) L
参数：g : G；⇑g ∘ f；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
protected theorem HasProd.map [CommMonoid γ] [TopologicalSpace γ] (hf : HasProd f a L) {G}
    [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    HasProd (g ∘ f) (g a) L := by
  have : (g ∘ fun s : Finset β ↦ ∏ b ∈ s, f b) = fun s : Finset β ↦ ∏ b ∈ s, (g ∘ f) b :=
    funext <| map_prod g _
  unfold HasProd
  rw [← this]
  exact (hg.tendsto a).comp hf

@[to_additive]
/-
**Topology.IsInducing.hasProd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α]   {L : SummationFilter β} [inst_2 : CommMonoid γ] [inst
_3 : TopologicalSpace γ] {G : Type u_4} [inst_4 : FunLike G α γ]   [MonoidHomCla
ss G α γ] {g : G},   Topology.IsInducing ⇑g → ∀ (f : β → α) (a : α), HasProd (⇑g
 ∘ f) (g a) L ↔ HasProd f a L
参数：f : β → α；a : α；⇑g ∘ f；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
-/
protected theorem Topology.IsInducing.hasProd_iff [CommMonoid γ] [TopologicalSpace γ] {G}
    [FunLike G α γ] [MonoidHomClass G α γ] {g : G} (hg : IsInducing g) (f : β → α) (a : α) :
    HasProd (g ∘ f) (g a) L ↔ HasProd f a L := by
  simp_rw [HasProd, comp_apply, ← _root_.map_prod]
  exact hg.tendsto_nhds_iff.symm

@[to_additive]
/-
**Multipliable.map** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [inst_2 : CommMon
oid γ] [inst_3 : TopologicalSpace γ],   Multipliable f L →     ∀ {G : Type u_4} 
[inst_4 : FunLike G α γ] [MonoidHomClass G α γ] (g : G), Continuous ⇑g → Multipl
iable (⇑g ∘ f) L
参数：g : G；⇑g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comm
Monoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {L : SummationFilt
e…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.map [CommMonoid γ] [TopologicalSpace γ]
    (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    Multipliable (g ∘ f) L :=
  (hf.hasProd.map g hg).multipliable

@[to_additive]
/-
**Multipliable.map_iff_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [inst_2 : CommMon
oid γ] [inst_3 : TopologicalSpace γ] {G : Type u_4} {G' : Type u_5}   [inst_4 : 
FunLike G α γ] [MonoidHomClass G α γ] [inst_6 : FunLike G' γ α] [MonoidHomClass 
G' γ α] (g : G) (g' : G'),   Continuous ⇑g → Continuous ⇑g' → Function.LeftInver
se ⇑g' ⇑g → (Multipliable (⇑g ∘ f) L ↔ Multipliable f L)
参数：g : G；g' : G'；Multipliable (⇑g ∘ f) L ↔ Multipliable f L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.LeftInverse.id`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f 
: α → β}, Function.LeftInverse g f → g ∘ f = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
-/
protected theorem Multipliable.map_iff_of_leftInverse [CommMonoid γ]
    [TopologicalSpace γ] {G G'}
    [FunLike G α γ] [MonoidHomClass G α γ] [FunLike G' γ α] [MonoidHomClass G' γ α]
    (g : G) (g' : G') (hg : Continuous g) (hg' : Continuous g') (hinv : Function.LeftInverse g' g) :
    Multipliable (g ∘ f) L ↔ Multipliable f L :=
  ⟨fun h ↦ by
    have := h.map _ hg'
    rwa [← Function.comp_assoc, hinv.id] at this, fun h ↦ h.map _ hg⟩

@[to_additive]
/-
**Multipliable.map_tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.map_tprod [L.NeBot] [CommMonoid γ] [TopologicalSpace γ] [T2Sp
ace γ] (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G
) (hg : Continuous g) : g (∏'[L] i, f i) = ∏'[L] i, g (f i)
参数：hf : Multipliable f L；g : G；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `HasProd.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comm
Monoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {L : SummationFilt
e…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.map_tprod [L.NeBot] [CommMonoid γ] [TopologicalSpace γ] [T2Space γ]
    (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    g (∏'[L] i, f i) = ∏'[L] i, g (f i) :=
  (HasProd.tprod_eq (HasProd.map hf.hasProd g hg)).symm

@[to_additive]
/-
**Topology.IsClosedEmbedding.map_tprod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.map_tprod {ι α α' G : Type*} [CommMonoid α] [Co
mmMonoid α'] [TopologicalSpace α] [TopologicalSpace α'] [T2Space α'] (f : ι -> α
) {L : SummationFilter ι} {g : G} [FunLike G α α'] [MonoidHomClass G α α'] (hge 
: Topology.IsClosedEmbedding g) : g (∏'[L] i, f i) = ∏'[L] i, g (f i)
参数：f : ι -> α；hge : Topology.IsClosedEmbedding g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.map_tprod`：Multipliable.map_tprod [L.NeBot] [CommMonoid γ] 
[TopologicalSpace γ] [T2Space γ] (hf : Multipliable f L) {G} [FunLike G α γ] [Mo
noidHomClass…
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Topology.IsClosedEmbedding.tendsto_nhds_iff`：∀ {X : Type u_1} {Y : Type 
u_2} {ι : Type u_4} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y]   {g : ι → X} {l : Filt…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `tprod_bot`：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b,
 f b
· 使用定理 `MonoidHom.map_finprod_of_injective`：MonoidHom.map_finprod_of_injective (
g : M ->* N) (hg : Injective g) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
-/
lemma Topology.IsClosedEmbedding.map_tprod {ι α α' G : Type*}
    [CommMonoid α] [CommMonoid α'] [TopologicalSpace α] [TopologicalSpace α'] [T2Space α']
    (f : ι → α) {L : SummationFilter ι} {g : G} [FunLike G α α'] [MonoidHomClass G α α']
    (hge : Topology.IsClosedEmbedding g) :
    g (∏'[L] i, f i) = ∏'[L] i, g (f i) := by
  by_cases hL : L.NeBot
  · by_cases h : Multipliable f L
    · exact h.map_tprod g hge.continuous
    · rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable, map_one]
      contrapose h
      -- need to show `g ∘ f` multipliable implies `g` multipliable
      simp only [Multipliable, HasProd] at h ⊢
      obtain ⟨b, hb⟩ := h
      obtain ⟨a, ha⟩ : b ∈ Set.range g :=
        hge.isClosed_range.mem_of_tendsto hb (.of_forall <| by simp [← _root_.map_prod])
      use a
      simp [hge.tendsto_nhds_iff, Function.comp_def, ha, hb]
  · simpa [tprod_bot hL] using
      (MonoidHomClass.toMonoidHom g).map_finprod_of_injective hge.injective _

/-- Special case of `Topology.IsClosedEmbedding.map_tprod`, logically weaker but possibly easier
to apply in practice. -/
@[to_additive /-- Special case of `Topology.IsClosedEmbedding.map_tsum`, logically weaker but
possibly easier to apply in practice. -/]
/-
**Function.LeftInverse.map_tprod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.map_tprod {G : Type*} (f : β -> α) [CommMonoid γ] [To
pologicalSpace γ] [T2Space γ] {g : G} [FunLike G α γ] [MonoidHomClass G α γ] (hg
 : Continuous g) {g' : γ -> α} (hg' : Continuous g') (hgg' : LeftInverse g' g) :
 g (∏'[L] b, f b) = ∏'[L] b, g (f b)
参数：f : β -> α；hg : Continuous g；hg' : Continuous g'；hgg' : LeftInverse g' g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsClosedEmbedding.map_tprod`：Topology.IsClosedEmbedding.map_tpr
od {ι α α' G : Type*} [CommMonoid α] [CommMonoid α'] [TopologicalSpace α] [Topol
ogicalSpace α'] [T2Space α…
· 使用定理 `Function.LeftInverse.isClosedEmbedding`：Function.LeftInverse.isClosedEmb
edding [T2Space X] {f : X -> Y} {g : Y -> X} (h : Function.LeftInverse f g) (hf 
: Continuous f) (hg : Contin…
-/
lemma Function.LeftInverse.map_tprod {G : Type*} (f : β → α) [CommMonoid γ] [TopologicalSpace γ]
    [T2Space γ] {g : G} [FunLike G α γ] [MonoidHomClass G α γ] (hg : Continuous g)
    {g' : γ → α} (hg' : Continuous g') (hgg' : LeftInverse g' g) :
    g (∏'[L] b, f b) = ∏'[L] b, g (f b) :=
  (hgg'.isClosedEmbedding hg' hg).map_tprod _

@[to_additive]
/-
**Topology.IsInducing.multipliable_iff_tprod_comp_mem_range** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：Topology.IsInducing.multipliable_iff_tprod_comp_mem_range [CommMonoid γ] [
TopologicalSpace γ] [T2Space γ] {G} [FunLike G α γ] [MonoidHomClass G α γ] {g : 
G} (hg : IsInducing g) (f : β -> α) : Multipliable f L ↔ Multipliable (g ∘ f) L 
∧ ∏'[L] i, g (f i) in Set.range g
参数：hg : IsInducing g；f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [in…
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Multipliable.map_tprod`：Multipliable.map_tprod [L.NeBot] [CommMonoid γ] 
[TopologicalSpace γ] [T2Space γ] (hf : Multipliable f L) {G} [FunLike G α γ] [Mo
noidHomClass…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `tprod_bot`：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b,
 f b
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.hasProd_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : CommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilt
er β} [inst_2 : CommM…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Topology.IsInducing.multipliable_iff_tprod_comp_mem_range [CommMonoid γ] [TopologicalSpace γ]
    [T2Space γ] {G} [FunLike G α γ] [MonoidHomClass G α γ] {g : G} (hg : IsInducing g) (f : β → α) :
    Multipliable f L ↔ Multipliable (g ∘ f) L ∧ ∏'[L] i, g (f i) ∈ Set.range g := by
  constructor
  · intro hf
    constructor
    · exact hf.map g hg.continuous
    · by_cases hL : L.NeBot
      · exact ⟨_, hf.map_tprod g hg.continuous⟩
      · by_cases hfs : (mulSupport fun x ↦ g (f x)).Finite
        · simp [tprod_bot hL, finprod_eq_prod _ hfs, ← _root_.map_prod]
        · exact ⟨1, by simp [tprod_bot hL, finprod_of_infinite_mulSupport hfs]⟩
  · rintro ⟨hgf, a, ha⟩
    use a
    have := hgf.hasProd
    simp_rw [comp_apply, ← ha] at this
    exact (hg.hasProd_iff f a).mp this

/-- "A special case of `Multipliable.map_iff_of_leftInverse` for convenience" -/
@[to_additive /-- A special case of `Summable.map_iff_of_leftInverse` for convenience -/]
/-
**Multipliable.map_iff_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [inst_2 : CommMon
oid γ] [inst_3 : TopologicalSpace γ] {G : Type u_4}   [inst_4 : EquivLike G α γ]
 [MulEquivClass G α γ] (g : G),   Continuous ⇑g → Continuous (EquivLike.inv g) →
 (Multipliable (⇑g ∘ f) L ↔ Multipliable f L)
参数：g : G；EquivLike.inv g；Multipliable (⇑g ∘ f) L ↔ Multipliable f L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.map_iff_of_leftInverse`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L
 : SummationFilter β} [in…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…

--- 原说明 ---
"A special case of `Multipliable.map_iff_of_leftInverse` for convenience"
-/
protected theorem Multipliable.map_iff_of_equiv [CommMonoid γ] [TopologicalSpace γ] {G}
    [EquivLike G α γ] [MulEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (EquivLike.inv g : γ → α)) :
    Multipliable (g ∘ f) L ↔ Multipliable f L :=
  Multipliable.map_iff_of_leftInverse g (g : α ≃* γ).symm hg hg' (EquivLike.left_inv g)

@[to_additive]
/-
**Function.Surjective.multipliable_iff_of_hasProd_iff** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Function.Surjective.multipliable_iff_of_hasProd_iff {α' : Type*} [CommMono
id α'] [TopologicalSpace α'] {e : α' -> α} (hes : Function.Surjective e) {f : β 
-> α} {g : γ -> α'} (he : forall {a}, HasProd f (e a) ↔ HasProd g a) : Multiplia
ble f ↔ Multipliable g
参数：hes : Function.Surjective e；he : forall {a}, HasProd f (e a) ↔ HasProd g a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
-/
theorem Function.Surjective.multipliable_iff_of_hasProd_iff {α' : Type*} [CommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasProd f (e a) ↔ HasProd g a) : Multipliable f ↔ Multipliable g :=
  hes.exists.trans <| exists_congr <| @he

variable [ContinuousMul α]

@[to_additive]
/-
**HasProd.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : HasProd (fun b => 
f b * g b) (a * b) L
参数：hf : HasProd f a L；hg : HasProd g b L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
-/
theorem HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) :
    HasProd (fun b ↦ f b * g b) (a * b) L := by
  dsimp only [HasProd] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg

@[to_additive]
/-
**Multipliable.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.mul (hf : Multipliable f L) (hg : Multipliable g L) : Multipl
iable (fun b => f b * g b) L
参数：hf : Multipliable f L；hg : Multipliable g L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.mul (hf : Multipliable f L) (hg : Multipliable g L) :
    Multipliable (fun b ↦ f b * g b) L :=
  (hf.hasProd.mul hg.hasProd).multipliable

@[to_additive]
/-
**HasProd.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.pow (hf : HasProd f a L) (n : Nat) : HasProd (f · ^ n) (a ^ n) L
参数：hf : HasProd f a L；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
-/
lemma HasProd.pow (hf : HasProd f a L) (n : ℕ) : HasProd (f · ^ n) (a ^ n) L := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

@[to_additive]
/-
**Multipliable.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.pow (hf : Multipliable f L) (n : Nat) : Multipliable (f · ^ n
) L
参数：hf : Multipliable f L；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用引理 `HasProd.pow`：HasProd.pow (hf : HasProd f a L) (n : Nat) : HasProd (f · ^
 n) (a ^ n) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma Multipliable.pow (hf : Multipliable f L) (n : ℕ) : Multipliable (f · ^ n) L :=
  (hf.hasProd.pow n).multipliable

@[to_additive]
/-
**hasProd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_prod {f : γ -> β -> α} {a : γ -> α} {s : Finset γ} : (forall i in 
s, HasProd (f i) (a i) L) -> HasProd (fun b => ∏ i in s, f i b) (∏ i in s, a i) 
L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
-/
theorem hasProd_prod {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasProd (f i) (a i) L) → HasProd (fun b ↦ ∏ i ∈ s, f i b) (∏ i ∈ s, a i) L := by
  classical
  exact Finset.induction_on s (by simp) <| by
    simp +contextual only [mem_insert, forall_eq_or_imp, not_false_iff,
      prod_insert, and_imp]
    exact fun x s _ IH hx h ↦ hx.mul (IH h)

@[to_additive]
/-
**multipliable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_prod {f : γ -> β -> α} {s : Finset γ} (hf : forall i in s, Mu
ltipliable (f i) L) : Multipliable (fun b => ∏ i in s, f i b) L
参数：hf : forall i in s, Multipliable (f i) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `hasProd_prod`：hasProd_prod {f : γ -> β -> α} {a : γ -> α} {s : Finset γ}
 : (forall i in s, HasProd (f i) (a i) L) -> HasProd (fun b => ∏ i in s, f i b) 
(∏…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem multipliable_prod {f : γ → β → α} {s : Finset γ}
    (hf : ∀ i ∈ s, Multipliable (f i) L) : Multipliable (fun b ↦ ∏ i ∈ s, f i b) L :=
  (hasProd_prod fun i hi ↦ (hf i hi).hasProd).multipliable

@[to_additive]
/-
**HasProd.mul_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.mul_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasProd (f ∘ 
(↑) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : HasProd (f ∘ (↑) : (s uni
on t : Set β) -> α) (a * b)
参数：hs : Disjoint s t；ha : HasProd (f ∘ (↑) : s -> α) a；hb : HasProd (f ∘ (↑) : t
 -> α) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a
· 使用定理 `Set.mulIndicator_union_of_disjoint`：mulIndicator_union_of_disjoint (h : 
Disjoint s t) (f : α -> M) : mulIndicator (s union t) f = fun a => mulIndicator 
s f a * mulIndicator t f…
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
-/
theorem HasProd.mul_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : t → α) b) : HasProd (f ∘ (↑) : (s ∪ t : Set β) → α) (a * b) := by
  rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_union_of_disjoint hs]
  exact ha.mul hb

@[to_additive]
/-
**hasProd_prod_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_prod_disjoint {ι} (s : Finset ι) {t : ι -> Set β} {a : ι -> α} (hs
 : (s : Set ι).Pairwise (Disjoint on t)) (hf : forall i in s, HasProd (f ∘ (↑) :
 t i -> α) (a i)) : HasProd (f ∘ (↑) : (⋃ i in s, t i) -> α) (∏ i in s, a i)
参数：s : Finset ι；hs : (s : Set ι).Pairwise (Disjoint on t)；hf : forall i in s, Ha
sProd (f ∘ (↑) : t i -> α) (a i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mulIndicator_biUnion`：mulIndicator_biUnion (s : Finset ι) (t : ι 
-> Set κ) {f : κ -> β} (hs : (s : Set ι).PairwiseDisjoint t) : mulIndicator (⋃ i
 in s, t i) f = f…
· 使用定理 `hasProd_prod`：hasProd_prod {f : γ -> β -> α} {a : γ -> α} {s : Finset γ}
 : (forall i in s, HasProd (f i) (a i) L) -> HasProd (fun b => ∏ i in s, f i b) 
(∏…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem hasProd_prod_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasProd (f ∘ (↑) : t i → α) (a i)) :
    HasProd (f ∘ (↑) : (⋃ i ∈ s, t i) → α) (∏ i ∈ s, a i) := by
  simp_rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Finset.mulIndicator_biUnion _ _ hs]
  exact hasProd_prod hf

@[to_additive]
/-
**HasProd.mul_isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasProd (f ∘ (↑
) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : HasProd f (a * b)
参数：hs : IsCompl s t；ha : HasProd (f ∘ (↑) : s -> α) a；hb : HasProd (f ∘ (↑) : t 
-> α) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `Set.mulIndicator_self_mul_compl_apply`：mulIndicator_self_mul_compl_apply
 (s : Set α) (f : α -> M) (a : α) : mulIndicator s f a * mulIndicator sᶜ f a = f
 a
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a
-/
theorem HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : t → α) b) : HasProd f (a * b) := by
  simpa [← hs.compl_eq] using
    (hasProd_subtype_iff_mulIndicator.1 ha).mul (hasProd_subtype_iff_mulIndicator.1 hb)

@[to_additive]
/-
**HasProd.mul_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) : s -> α) a) (hb : Ha
sProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
参数：ha : HasProd (f ∘ (↑) : s -> α) a；hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.mul_isCompl`：HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t
) (ha : HasProd (f ∘ (↑) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : HasP
rod f (a …
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
theorem HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) → α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl hb

@[to_additive]
/-
**Multipliable.mul_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.mul_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s -> α)) 
(hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) -> α)) : Multipliable f
参数：hs : Multipliable (f ∘ (↑) : s -> α)；hsc : Multipliable (f ∘ (↑) : (sᶜ : Set 
β) -> α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.mul_compl`：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) 
: s -> α) a) (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.mul_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s → α))
    (hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α)) : Multipliable f :=
  (hs.hasProd.mul_compl hsc.hasProd).multipliable

@[to_additive]
/-
**HasProd.compl_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.compl_mul {s : Set β} (ha : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) 
a) (hb : HasProd (f ∘ (↑) : s -> α) b) : HasProd f (a * b)
参数：ha : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) a；hb : HasProd (f ∘ (↑) : s -> α) 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.mul_isCompl`：HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t
) (ha : HasProd (f ∘ (↑) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : HasP
rod f (a …
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
theorem HasProd.compl_mul {s : Set β} (ha : HasProd (f ∘ (↑) : (sᶜ : Set β) → α) a)
    (hb : HasProd (f ∘ (↑) : s → α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl.symm hb

@[to_additive]
/-
**Multipliable.compl_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.compl_add {s : Set β} (hs : Multipliable (f ∘ (↑) : (sᶜ : Set
 β) -> α)) (hsc : Multipliable (f ∘ (↑) : s -> α)) : Multipliable f
参数：hs : Multipliable (f ∘ (↑) : (sᶜ : Set β) -> α)；hsc : Multipliable (f ∘ (↑) :
 s -> α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.compl_mul`：HasProd.compl_mul {s : Set β} (ha : HasProd (f ∘ (↑) 
: (sᶜ : Set β) -> α) a) (hb : HasProd (f ∘ (↑) : s -> α) b) : HasProd f (a * b)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.compl_add {s : Set β} (hs : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α))
    (hsc : Multipliable (f ∘ (↑) : s → α)) : Multipliable f :=
  (hs.hasProd.compl_mul hsc.hasProd).multipliable

/-- Version of `HasProd.update` for `CommMonoid` rather than `CommGroup`.
Rather than showing that `f.update` has a specific product in terms of `HasProd`,
it gives a relationship between the products of `f` and `f.update` given that both exist. -/
@[to_additive /-- Version of `HasSum.update` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that `f.update` has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/]
/-
**HasProd.update'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.update' [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [Co
mmMonoid α] [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β -> α} {a a' : α
} (hf : HasProd f a L) (b : β) (x : α) (hf' : HasProd (update f b x) a' L) : a *
 x = a' * f b
参数：hf : HasProd f a L；b : β；x : α；hf' : HasProd (update f b x) a' L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `hasProd_ite_eq`：hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (
L
· 使用定理 `HasProd.unique`：HasProd.unique {a₁ a₂ : α} : HasProd f a₁ L -> HasProd f
 a₂ L -> a₁ = a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem HasProd.update' [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
    [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β → α} {a a' : α} (hf : HasProd f a L)
    (b : β) (x : α) (hf' : HasProd (update f b x) a' L) :
    a * x = a' * f b := by
  have : ∀ b', f b' * ite (b' = b) x 1 = update f b x b' * ite (b' = b) (f b) 1 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using! mul_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.mul (hasProd_ite_eq b x L)
  simp_rw [this] at h
  exact HasProd.unique h (hf'.mul (hasProd_ite_eq b (f b) L))

/-- Version of `hasProd_ite_div_hasProd` for `CommMonoid` rather than `CommGroup`.
Rather than showing that the `ite` expression has a specific product in terms of `HasProd`, it gives
a relationship between the products of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
@[to_additive /-- Version of `hasSum_ite_sub_hasSum` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that the `ite` expression has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/]
/-
**eq_mul_of_hasProd_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_hasProd_ite [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace 
α] [CommMonoid α] [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β -> α} {a 
: α} (hf : HasProd f a L) (b : β) (a' : α) (hf' : HasProd (fun n => ite (n = b) 
1 (f n)) a' L) : a = a' * f b
参数：hf : HasProd f a L；b : β；a' : α；hf' : HasProd (fun n => ite (n = b) 1 (f n)) 
a' L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasProd.update'`：HasProd.update' [L.LeAtTop] [L.NeBot] {α : Type*} [Topo
logicalSpace α] [CommMonoid α] [T2Space α] [ContinuousMul α] [DecidableEq β] {f 
: β -…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
-/
theorem eq_mul_of_hasProd_ite [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
    [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β → α} {a : α} (hf : HasProd f a L) (b : β)
    (a' : α) (hf' : HasProd (fun n ↦ ite (n = b) 1 (f n)) a' L) : a = a' * f b := by
  refine (mul_one a).symm.trans (hf.update' b 1 ?_)
  convert! hf'
  apply update_apply

end HasProd

section tprod

variable [CommMonoid α] [TopologicalSpace α] {f g : β → α} {L : SummationFilter β}

@[to_additive]
/-
**tprod_congr_set_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_congr_set_coe (f : β -> α) {s t : Set β} (h : s = t) : ∏' x : s, f x
 = ∏' x : t, f x
参数：f : β -> α；h : s = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem tprod_congr_set_coe (f : β → α) {s t : Set β} (h : s = t) :
    ∏' x : s, f x = ∏' x : t, f x := by rw [h]

@[to_additive]
/-
**tprod_congr_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_congr_subtype (f : β -> α) {P Q : β -> Prop} (h : forall x, P x ↔ Q 
x) : ∏' x : {x // P x}, f x = ∏' x : {x // Q x}, f x
参数：f : β -> α；h : forall x, P x ↔ Q x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_congr_set_coe`：tprod_congr_set_coe (f : β -> α) {s t : Set β} (h :
 s = t) : ∏' x : s, f x = ∏' x : t, f x
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem tprod_congr_subtype (f : β → α) {P Q : β → Prop} (h : ∀ x, P x ↔ Q x) :
    ∏' x : {x // P x}, f x = ∏' x : {x // Q x}, f x :=
  tprod_congr_set_coe f <| Set.ext h

@[to_additive]
/-
**tprod_eq_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_finprod [L.LeAtTop] (hf : HasFiniteMulSupport f) : ∏'[L] b, f b =
 ∏ᶠ b, f b
参数：hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `multipliable_of_hasFiniteMulSupport`：multipliable_of_hasFiniteMulSupport
 [L.HasSupport] (h : HasFiniteMulSupport f) : Multipliable f L
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SummationFilter.support_eq_univ`：∀ {β : Type u_2} (L : SummationFilter β
) [L.LeAtTop], L.support = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Set.mulIndicator_univ`：mulIndicator_univ (f : α -> M) : mulIndicator (un
iv : Set α) f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprod_eq_finprod [L.LeAtTop] (hf : HasFiniteMulSupport f) :
    ∏'[L] b, f b = ∏ᶠ b, f b := by
  simp [tprod_def, multipliable_of_hasFiniteMulSupport hf, show Set.Finite _ from hf,
    show L.HasSupport by infer_instance]

@[to_additive]
/-
**tprod_eq_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSupport f subseteq s) :
 ∏'[L] b, f b = ∏ b in s, f b
参数：hf : mulSupport f subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_finprod`：tprod_eq_finprod [L.LeAtTop] (hf : HasFiniteMulSupport
 f) : ∏'[L] b, f b = ∏ᶠ b, f b
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
-/
theorem tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSupport f ⊆ s) :
    ∏'[L] b, f b = ∏ b ∈ s, f b := by
  rw [tprod_eq_finprod (s.finite_toSet.subset hf), finprod_eq_prod_of_mulSupport_subset _ hf]

@[to_additive]
/-
**tprod_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : forall b ∉ s, f b = 1) : ∏'
[L] b, f b = ∏ b in s, f b
参数：hf : forall b ∉ s, f b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_eq_prod'`：tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSuppo
rt f subseteq s) : ∏'[L] b, f b = ∏ b in s, f b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
-/
theorem tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : ∀ b ∉ s, f b = 1) :
    ∏'[L] b, f b = ∏ b ∈ s, f b :=
  tprod_eq_prod' <| mulSupport_subset_iff'.2 hf

@[to_additive (attr := simp)]
/-
**tprod_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_one : ∏'[L] _, (1 : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `multipliable_one`：multipliable_one : Multipliable (fun _ => 1 : β -> α) 
L
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Function.mulSupport_fun_one`：mulSupport_fun_one : mulSupport (fun _ => 1
 : ι -> M) = ∅
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用引理 `Set.mulIndicator_one`：mulIndicator_one (s : Set α) : (mulIndicator s fun
 _ => (1 : M)) = fun _ => (1 : M)
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用引理 `eq_true_intro`：eq_true_intro {a : Prop} (h : a) : a = True
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem tprod_one : ∏'[L] _, (1 : α) = 1 := by
  rw [tprod_def, dif_pos multipliable_one, mulSupport_fun_one, Set.empty_inter,
    Set.mulIndicator_one, finprod_one, eq_true_intro hasProd_one, if_true, ite_self]

@[to_additive (attr := simp)]
/-
**tprod_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
-/
theorem tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1 := by
  convert! tprod_one (L := L)

@[to_additive]
/-
**tprod_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'[L] b, f b = ∏'
[L] b, g b
参数：hfg : forall b, f b = g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem tprod_congr {f g : β → α}
    (hfg : ∀ b, f b = g b) : ∏'[L] b, f b = ∏'[L] b, g b :=
  congr_arg (tprod · L) (funext hfg)

@[to_additive]
/-
**tprod_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'[L] b, f b = ∏'
[L] b, g b
参数：hfg : forall b, f b = g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem tprod_congr₂ {f g : β → γ → α} {M : SummationFilter γ}
    (hfg : ∀ b c, f b c = g b c) : ∏'[L] b, ∏'[M] c, f b c = ∏'[L] b, ∏'[M] c, g b c :=
  tprod_congr fun b ↦ tprod_congr fun c ↦ hfg b c

@[to_additive (attr := simp)]
/-
**tprod_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L] b, f b = ∏ b, f
 b
参数：f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_eq_prod`：tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : forall b ∉
 s, f b = 1) : ∏'[L] b, f b = ∏ b in s, f b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tprod_fintype [L.LeAtTop] [Fintype β] (f : β → α) : ∏'[L] b, f b = ∏ b, f b := by
  apply tprod_eq_prod; simp

@[to_additive]
/-
**prod_eq_tprod_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_eq_tprod_mulIndicator (f : β -> α) (s : Finset β) (L
参数：f : β -> α；s : Finset β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_prod'`：tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSuppo
rt f subseteq s) : ∏'[L] b, f b = ∏ b in s, f b
· 使用引理 `Set.mulSupport_mulIndicator_subset`：mulSupport_mulIndicator_subset : mul
Support (s.mulIndicator f) subseteq s
· 使用引理 `Finset.prod_mulIndicator_subset`：prod_mulIndicator_subset (f : ι -> β) {
s t : Finset ι} (h : s subseteq t) : ∏ i in t, mulIndicator (↑s) f i = ∏ i in s,
 f i
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem prod_eq_tprod_mulIndicator (f : β → α) (s : Finset β) (L := unconditional β) [L.LeAtTop] :
    ∏ x ∈ s, f x = ∏'[L] x, Set.mulIndicator (↑s) f x := by
  rw [tprod_eq_prod' (Set.mulSupport_mulIndicator_subset),
      Finset.prod_mulIndicator_subset _ Finset.Subset.rfl]

@[to_additive]
/-
**tprod_bool** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_bool (f : Bool -> α) : ∏' i : Bool, f i = f false * f true
参数：f : Bool -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Fintype.prod_bool`：prod_bool [CommMonoid α] (f : Bool -> α) : ∏ b, f b =
 f true * f false
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem tprod_bool (f : Bool → α) : ∏' i : Bool, f i = f false * f true := by
  rw [tprod_fintype, Fintype.prod_bool, mul_comm]

@[to_additive]
/-
**tprod_eq_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) (hf : forall b' != b, 
f b' = 1) : ∏'[L] b, f b = f b
参数：b : β；hf : forall b' != b, f b' = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_prod`：tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : forall b ∉
 s, f b = 1) : ∏'[L] b, f b = ∏ b in s, f b
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem tprod_eq_mulSingle [L.LeAtTop] {f : β → α} (b : β) (hf : ∀ b' ≠ b, f b' = 1) :
    ∏'[L] b, f b = f b := by
  rw [tprod_eq_prod (s := {b}), prod_singleton]
  exact fun b' hb' ↦ hf b' (by simpa using hb')

@[to_additive]
/-
**tprod_tprod_eq_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_tprod_eq_mulSingle (f : β -> γ -> α) (b : β) (c : γ) (hfb : forall b
' != b, f b' c = 1) (hfc : forall b', forall c' != c, f b' c' = 1) : ∏' (b') (c'
), f b' c' = f b c
参数：f : β -> γ -> α；b : β；c : γ；hfb : forall b' != b, f b' c = 1；hfc : forall b',
 forall c' != c, f b' c' = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_congr`：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'
[L] b, f b = ∏'[L] b, g b
· 使用定理 `tprod_eq_mulSingle`：tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) 
(hf : forall b' != b, f b' = 1) : ∏'[L] b, f b = f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem tprod_tprod_eq_mulSingle
    (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ b' ≠ b, f b' c = 1)
    (hfc : ∀ b', ∀ c' ≠ c, f b' c' = 1) : ∏' (b') (c'), f b' c' = f b c :=
  calc
    ∏' (b') (c'), f b' c' = ∏' b', f b' c := tprod_congr fun b' ↦ tprod_eq_mulSingle _ (hfc b')
    _ = f b c := tprod_eq_mulSingle _ hfb

@[to_additive (attr := simp)]
/-
**tprod_ite_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_ite_eq (b : β) [DecidablePred (· = b)] (a : β -> α) (L
参数：b : β；· = b；a : β -> α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_mulSingle`：tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) 
(hf : forall b' != b, f b' = 1) : ∏'[L] b, f b = f b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem tprod_ite_eq (b : β) [DecidablePred (· = b)] (a : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b' = b then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]
/-
**tprod_ite_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_ite_eq' (b : β) [DecidablePred (b = ·)] (a : β -> α) (L
参数：b : β；b = ·；a : β -> α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_mulSingle`：tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) 
(hf : forall b' != b, f b' = 1) : ∏'[L] b, f b = f b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem tprod_ite_eq' (b : β) [DecidablePred (b = ·)] (a : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b = b' then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive]
/-
**Finset.tprod_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.tprod_subtype (s : Finset β) (f : β -> α) : ∏' x : { x // x in s },
 f x = ∏ x in s, f x
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem Finset.tprod_subtype (s : Finset β) (f : β → α) :
    ∏' x : { x // x ∈ s }, f x = ∏ x ∈ s, f x := by
  rw [← prod_attach]; exact tprod_fintype _

@[to_additive]
/-
**Finset.tprod_subtype'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.tprod_subtype' (s : Finset β) (f : β -> α) : ∏' x : (s : Set β), f 
x = ∏ x in s, f x
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.tprod_subtype' (s : Finset β) (f : β → α) :
    ∏' x : (s : Set β), f x = ∏ x ∈ s, f x := by
  simp [prod_attach]

@[to_additive]
/-
**tprod_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_singleton (b : β) (f : β -> α) : ∏' x : ({b} : Set β), f x = f b
参数：b : β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprod_singleton (b : β) (f : β → α) : ∏' x : ({b} : Set β), f x = f b := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Function.Injective.tprod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.tprod_eq {g : γ -> β} (hg : Injective g) {f : β -> α} (
hf : mulSupport f subseteq Set.range g) : ∏' c, f (g c) = ∏' b, f b
参数：hg : Injective g；hf : mulSupport f subseteq Set.range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Function.instCanLiftForallEmbeddingCoeInjective`：∀ {α : Sort u_1} {β : S
ort u_2}, CanLift (α → β) (α ↪ β) DFunLike.coe Function.Injective
· 使用定理 `tprod_eq_prod'`：tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSuppo
rt f subseteq s) : ∏'[L] b, f b = ∏ b in s, f b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SummationFilter.support_eq_univ`：∀ {β : Type u_2} (L : SummationFilter β
) [L.LeAtTop], L.support = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
（共 39 条，此处仅展示前 30 条）
-/
theorem Function.Injective.tprod_eq {g : γ → β} (hg : Injective g) {f : β → α}
    (hf : mulSupport f ⊆ Set.range g) : ∏' c, f (g c) = ∏' b, f b := by
  classical
  have : mulSupport f = g '' mulSupport (f ∘ g) := by
    rw [mulSupport_comp_eq_preimage, Set.image_preimage_eq_iff.2 hf]
  rw [← Function.comp_def]
  by_cases hf_fin : (mulSupport f).Finite
  · have hfg_fin : (mulSupport (f ∘ g)).Finite := hf_fin.preimage hg.injOn
    lift g to γ ↪ β using hg
    simp_rw [tprod_eq_prod' hf_fin.coe_toFinset.ge, tprod_eq_prod' hfg_fin.coe_toFinset.ge,
      comp_apply, ← Finset.prod_map]
    refine Finset.prod_congr (Finset.coe_injective ?_) fun _ _ ↦ rfl
    simp [this]
  · have hf_fin' : ¬ Set.Finite (mulSupport (f ∘ g)) := by
      rwa [this, Set.finite_image_iff hg.injOn] at hf_fin
    simp_rw [tprod_def, SummationFilter.support_eq_univ, Set.inter_univ,
      show (unconditional β).HasSupport by infer_instance,
      show (unconditional γ).HasSupport by infer_instance, true_and,
      if_neg hf_fin, if_neg hf_fin', Multipliable]
    simp [hg.hasProd_iff (mulSupport_subset_iff'.1 hf)]

@[to_additive]
/-
**Equiv.tprod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) = ∏' b, f b
参数：e : γ ≃ β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tprod_eq`：Function.Injective.tprod_eq {g : γ -> β} (h
g : Injective g) {f : β -> α} (hf : mulSupport f subseteq Set.range g) : ∏' c, f
 (g c) = ∏' b, f …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
-/
theorem Equiv.tprod_eq (e : γ ≃ β) (f : β → α) : ∏' c, f (e c) = ∏' b, f b :=
  e.injective.tprod_eq <| by simp

@[to_additive (attr := simp)]
/-
**tprod_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_comp_neg {β : Type*} [InvolutiveNeg β] (f : β -> α) : ∏' d, f (-d) =
 ∏' d, f d
参数：f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.tprod_eq`：Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) 
= ∏' b, f b
-/
theorem tprod_comp_neg {β : Type*} [InvolutiveNeg β] (f : β → α) :
    ∏' d, f (-d) = ∏' d, f d :=
  (Equiv.neg β).tprod_eq f

@[to_additive]
/-
**tprod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_mem {ι S : Type*} {s : S} [SetLike S α] [SubmonoidClass S α] (h_clos
ed : IsClosed (s : Set α)) {f : ι -> α} (h : forall i, f i in s) : ∏' i, f i in 
s
参数：h_closed : IsClosed (s : Set α)；h : forall i, f i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
-/
theorem tprod_mem {ι S : Type*} {s : S} [SetLike S α] [SubmonoidClass S α]
    (h_closed : IsClosed (s : Set α)) {f : ι → α} (h : ∀ i, f i ∈ s) :
    ∏' i, f i ∈ s := by
  by_cases hf : Multipliable f
  · exact h_closed.mem_of_tendsto hf.hasProd <| .of_forall fun _ => prod_mem fun i _ => h i
  · simp [tprod_eq_one_of_not_multipliable hf, one_mem]

/-! ### `tprod` on subsets - part 1 -/

@[to_additive]
/-
**tprod_subtype_eq_of_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_subtype_eq_of_mulSupport_subset {f : β -> α} {s : Set β} (hs : mulSu
pport f subseteq s) : ∏' x : s, f x = ∏' x, f x
参数：hs : mulSupport f subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tprod_eq`：Function.Injective.tprod_eq {g : γ -> β} (h
g : Injective g) {f : β -> α} (hf : mulSupport f subseteq Set.range g) : ∏' c, f
 (g c) = ∏' b, f …
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }

--- 原说明 ---
### `tprod` on subsets - part 1
-/
theorem tprod_subtype_eq_of_mulSupport_subset {f : β → α} {s : Set β} (hs : mulSupport f ⊆ s) :
    ∏' x : s, f x = ∏' x, f x :=
  Subtype.val_injective.tprod_eq <| by simpa

@[to_additive]
/-
**tprod_subtype_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_subtype_mulSupport (f : β -> α) : ∏' x : mulSupport f, f x = ∏' x, f
 x
参数：f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_subtype_eq_of_mulSupport_subset`：tprod_subtype_eq_of_mulSupport_su
bset {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s) : ∏' x : s, f x = ∏
' x, f x
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem tprod_subtype_mulSupport (f : β → α) : ∏' x : mulSupport f, f x = ∏' x, f x :=
  tprod_subtype_eq_of_mulSupport_subset Set.Subset.rfl

@[to_additive]
/-
**tprod_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_subtype (s : Set β) (f : β -> α) : ∏' x : s, f x = ∏' x, s.mulIndica
tor f x
参数：s : Set β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_subtype_eq_of_mulSupport_subset`：tprod_subtype_eq_of_mulSupport_su
bset {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s) : ∏' x : s, f x = ∏
' x, f x
· 使用引理 `Set.mulSupport_mulIndicator_subset`：mulSupport_mulIndicator_subset : mul
Support (s.mulIndicator f) subseteq s
· 使用定理 `tprod_congr`：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'
[L] b, f b = ∏'[L] b, g b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tprod_subtype (s : Set β) (f : β → α) : ∏' x : s, f x = ∏' x, s.mulIndicator f x := by
  rw [← tprod_subtype_eq_of_mulSupport_subset Set.mulSupport_mulIndicator_subset, tprod_congr]
  simp

@[to_additive (attr := simp)]
/-
**tprod_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_univ (f : β -> α) : ∏' x : (Set.univ : Set β), f x = ∏' x, f x
参数：f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_subtype_eq_of_mulSupport_subset`：tprod_subtype_eq_of_mulSupport_su
bset {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s) : ∏' x : s, f x = ∏
' x, f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem tprod_univ (f : β → α) : ∏' x : (Set.univ : Set β), f x = ∏' x, f x :=
  tprod_subtype_eq_of_mulSupport_subset <| Set.subset_univ _

@[to_additive]
/-
**tprod_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_image {g : γ -> β} (f : β -> α) {s : Set γ} (hg : Set.InjOn g s) : ∏
' x : g '' s, f x = ∏' x : s, f (g x)
参数：f : β -> α；hg : Set.InjOn g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tprod_eq`：Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) 
= ∏' b, f b
-/
theorem tprod_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    ∏' x : g '' s, f x = ∏' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tprod_eq fun x ↦ f x).symm

@[to_additive]
/-
**tprod_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_range {g : γ -> β} (f : β -> α) (hg : Injective g) : ∏' x : Set.rang
e g, f x = ∏' x, f (g x)
参数：f : β -> α；hg : Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `tprod_image`：tprod_image {g : γ -> β} (f : β -> α) {s : Set γ} (hg : Set
.InjOn g s) : ∏' x : g '' s, f x = ∏' x : s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tprod_univ`：tprod_univ (f : β -> α) : ∏' x : (Set.univ : Set β), f x = ∏
' x, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprod_range {g : γ → β} (f : β → α) (hg : Injective g) :
    ∏' x : Set.range g, f x = ∏' x, f (g x) := by
  rw [← Set.image_univ, tprod_image f hg.injOn]
  simp_rw [← comp_apply (g := g), tprod_univ (f ∘ g)]

/-- If `f b = 1` for all `b ∈ t`, then the product of `f a` with `a ∈ s` is the same as the
product of `f a` with `a ∈ s ∖ t`. -/
@[to_additive /-- If `f b = 0` for all `b ∈ t`, then the sum of `f a` with `a ∈ s` is the same as
the sum of `f a` with `a ∈ s ∖ t`. -/]
/-
**tprod_setElem_eq_tprod_setElem_sdiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_setElem_eq_tprod_setElem_sdiff {f : β -> α} (s t : Set β) (hf₀ : for
all b in t, f b = 1) : ∏' a : s, f a = ∏' a : (s \ t : Set β), f a
参数：s t : Set β；hf₀ : forall b in t, f b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.tprod_eq`：Function.Injective.tprod_eq {g : γ -> β} (h
g : Injective g) {f : β -> α} (hf : mulSupport f subseteq Set.range g) : ∏' c, f
 (g c) = ∏' b, f …
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma tprod_setElem_eq_tprod_setElem_sdiff {f : β → α} (s t : Set β)
    (hf₀ : ∀ b ∈ t, f b = 1) :
    ∏' a : s, f a = ∏' a : (s \ t : Set β), f a :=
  .symm <| (Set.inclusion_injective (t := s) Set.sdiff_subset).tprod_eq (f := f ∘ (↑)) <|
    mulSupport_subset_iff'.2 fun b hb ↦ hf₀ b <| by simpa using hb

@[deprecated (since := "2026-06-03")]
alias tprod_setElem_eq_tprod_setElem_diff := tprod_setElem_eq_tprod_setElem_sdiff

/-- If `f b = 1`, then the product of `f a` with `a ∈ s` is the same as the product of `f a` for
`a ∈ s ∖ {b}`. -/
@[to_additive /-- If `f b = 0`, then the sum of `f a` with `a ∈ s` is the same as the sum of `f a`
for `a ∈ s ∖ {b}`. -/]
/-
**tprod_eq_tprod_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_eq_tprod_sdiff_singleton {f : β -> α} (s : Set β) {b : β} (hf₀ : f b
 = 1) : ∏' a : s, f a = ∏' a : (s \ {b} : Set β), f a
参数：s : Set β；hf₀ : f b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tprod_setElem_eq_tprod_setElem_sdiff`：tprod_setElem_eq_tprod_setElem_sdi
ff {f : β -> α} (s t : Set β) (hf₀ : forall b in t, f b = 1) : ∏' a : s, f a = ∏
' a : (s \ t : Set β), f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma tprod_eq_tprod_sdiff_singleton {f : β → α} (s : Set β) {b : β} (hf₀ : f b = 1) :
    ∏' a : s, f a = ∏' a : (s \ {b} : Set β), f a :=
  tprod_setElem_eq_tprod_setElem_sdiff s {b} fun _ ha ↦ ha ▸ hf₀

@[deprecated (since := "2026-06-03")]
alias tprod_eq_tprod_diff_singleton := tprod_eq_tprod_sdiff_singleton

@[to_additive]
/-
**tprod_eq_tprod_of_ne_one_bij** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_tprod_of_ne_one_bij {g : γ -> α} (i : mulSupport g -> β) (hi : In
jective i) (hf : mulSupport f subseteq Set.range i) (hfg : forall x, f (i x) = g
 x) : ∏' x, f x = ∏' y, g y
参数：i : mulSupport g -> β；hi : Injective i；hf : mulSupport f subseteq Set.range i
；hfg : forall x, f (i x) = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_subtype_mulSupport`：tprod_subtype_mulSupport (f : β -> α) : ∏' x :
 mulSupport f, f x = ∏' x, f x
· 使用定理 `Function.Injective.tprod_eq`：Function.Injective.tprod_eq {g : γ -> β} (h
g : Injective g) {f : β -> α} (hf : mulSupport f subseteq Set.range g) : ∏' c, f
 (g c) = ∏' b, f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprod_eq_tprod_of_ne_one_bij {g : γ → α} (i : mulSupport g → β) (hi : Injective i)
    (hf : mulSupport f ⊆ Set.range i) (hfg : ∀ x, f (i x) = g x) : ∏' x, f x = ∏' y, g y := by
  rw [← tprod_subtype_mulSupport g, ← hi.tprod_eq hf]
  simp only [hfg]

@[to_additive]
/-
**Equiv.tprod_eq_tprod_of_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.tprod_eq_tprod_of_mulSupport {f : β -> α} {g : γ -> α} (e : mulSuppo
rt f ≃ mulSupport g) (he : forall x, g (e x) = f x) : ∏' x, f x = ∏' y, g y
参数：e : mulSupport f ≃ mulSupport g；he : forall x, g (e x) = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_eq_tprod_of_ne_one_bij`：tprod_eq_tprod_of_ne_one_bij {g : γ -> α} 
(i : mulSupport g -> β) (hi : Injective i) (hf : mulSupport f subseteq Set.range
 i) (hfg : forall …
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Equiv.tprod_eq_tprod_of_mulSupport {f : β → α} {g : γ → α}
    (e : mulSupport f ≃ mulSupport g) (he : ∀ x, g (e x) = f x) :
    ∏' x, f x = ∏' y, g y :=
  .symm <| tprod_eq_tprod_of_ne_one_bij _ (Subtype.val_injective.comp e.injective) (by simp) he

@[to_additive]
/-
**tprod_dite_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_dite_right (P : Prop) [Decidable P] (x : β -> ¬P -> α) : ∏'[L] b, (i
f h : P then 1 else x b h) = if h : P then 1 else ∏'[L] b, x b h
参数：P : Prop；x : β -> ¬P -> α。
该定理/引理给出了一组等式。
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
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem tprod_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    ∏'[L] b, (if h : P then 1 else x b h) = if h : P then 1 else ∏'[L] b, x b h := by
  by_cases hP : P <;> simp [hP]

@[to_additive]
/-
**tprod_dite_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_dite_left (P : Prop) [Decidable P] (x : β -> P -> α) : ∏'[L] b, (if 
h : P then x b h else 1) = if h : P then ∏'[L] b, x b h else 1
参数：P : Prop；x : β -> P -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
-/
theorem tprod_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    ∏'[L] b, (if h : P then x b h else 1) = if h : P then ∏'[L] b, x b h else 1 := by
  by_cases hP : P <;> simp [hP]

@[to_additive (attr := simp)]
/-
**tprod_extend_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_extend_one {γ : Type*} {g : γ -> β} (hg : Injective g) (f : γ -> α) 
: ∏' y, extend g f 1 y = ∏' x, f x
参数：hg : Injective g；f : γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.tprod_eq`：Function.Injective.tprod_eq {g : γ -> β} (h
g : Injective g) {f : β -> α} (hf : mulSupport f subseteq Set.range g) : ∏' c, f
 (g c) = ∏' b, f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tprod_extend_one {γ : Type*} {g : γ → β} (hg : Injective g) (f : γ → α) :
    ∏' y, extend g f 1 y = ∏' x, f x := by
  have : mulSupport (extend g f 1) ⊆ Set.range g := mulSupport_subset_iff'.2 <| extend_apply' _ _
  simp_rw [← hg.tprod_eq this, hg.extend_apply]

@[to_additive]
/-
**tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem (s : γ -> Set β) (f : 
β -> α) (i : β) (hi : i in ⋃ d, s d) (hs : Pairwise (Disjoint on (fun j => s j i
nter f.mulSupport))) : ∏' d, (s d).mulIndicator f i = f i
参数：s : γ -> Set β；f : β -> α；i : β；hi : i in ⋃ d, s d；hs : Pairwise (Disjoint on
 (fun j => s j inter f.mulSupport))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_subtype_eq_of_mulSupport_subset`：tprod_subtype_eq_of_mulSupport_su
bset {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s) : ∏' x : s, f x = ∏
' x, f x
· 使用引理 `Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport`：mulSupport
_subset_subsingleton_of_disjoint_on_mulSupport [One β] {s : γ -> Set α} (f : α -
> β) (hs : Pairwise (Disjoint on (fun j => s j int…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem (s : γ → Set β) (f : β → α)
    (i : β) (hi : i ∈ ⋃ d, s d) (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) :
    ∏' d, (s d).mulIndicator f i = f i := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {j})]
  · aesop
  · exact Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f hs i j hj

@[to_additive]
/-
**tprod_mulIndicator_of_mem_union_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_mulIndicator_of_mem_union_disjoint (s : γ -> Set β) (f : β -> α) (hs
 : Pairwise (Disjoint on s)) (i : β) (hi : i in ⋃ d, s d) : ∏' d, (s d).mulIndic
ator f i = f i
参数：s : γ -> Set β；f : β -> α；hs : Pairwise (Disjoint on s)；i : β；hi : i in ⋃ d, 
s d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem`：tprod_mulIndicator_
of_disjoint_on_mulSupport_of_mem (s : γ -> Set β) (f : β -> α) (i : β) (hi : i i
n ⋃ d, s d) (hs : Pairwise (Disjoint on (…
· 使用定理 `pairwise_disjoint_mono`：pairwise_disjoint_mono [PartialOrder α] [OrderBo
t α] (hs : Pairwise (Disjoint on f)) (h : g <= f) : Pairwise (Disjoint on g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma tprod_mulIndicator_of_mem_union_disjoint (s : γ → Set β) (f : β → α)
    (hs : Pairwise (Disjoint on s)) (i : β) (hi : i ∈ ⋃ d, s d) :
    ∏' d, (s d).mulIndicator f i = f i :=
  tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem s f i hi (pairwise_disjoint_mono hs
    <| fun _ _ hi ↦ hi.1)

@[to_additive]
/-
**tprod_mulIndicator_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_mulIndicator_of_notMem (s : γ -> Set β) (f : β -> α) (i : β) (hi : f
orall d, i ∉ s d) : ∏' d, (s d).mulIndicator f i = 1
参数：s : γ -> Set β；f : β -> α；i : β；hi : forall d, i ∉ s d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tprod_mulIndicator_of_notMem (s : γ → Set β) (f : β → α) (i : β) (hi : ∀ d, i ∉ s d) :
    ∏' d, (s d).mulIndicator f i = 1 := by
  aesop

@[to_additive]
/-
**mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport (s : γ -> Set β) (f
 : β -> α) (hs : Pairwise (Disjoint on (fun j => s j inter f.mulSupport))) (i : 
β) : (⋃ d, s d).mulIndicator f i = ∏' d, (s d).mulIndicator f i
参数：s : γ -> Set β；f : β -> α；hs : Pairwise (Disjoint on (fun j => s j inter f.mu
lSupport))；i : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem`：tprod_mulIndicator_
of_disjoint_on_mulSupport_of_mem (s : γ -> Set β) (f : β -> α) (i : β) (hi : i i
n ⋃ d, s d) (hs : Pairwise (Disjoint on (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
-/
lemma mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport (s : γ → Set β) (f : β → α)
    (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) (i : β) :
    (⋃ d, s d).mulIndicator f i = ∏' d, (s d).mulIndicator f i := by
  by_cases h₀ : i ∈ ⋃ d, s d
  · simp only [h₀, hs, Set.mulIndicator_of_mem, tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem]
  · aesop

@[to_additive]
/-
**mulIndicator_iUnion_of_pairwise_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulIndicator_iUnion_of_pairwise_disjoint (s : γ -> Set β) (hs : Pairwise (
Disjoint on s)) (f : β -> α) : (⋃ d, s d).mulIndicator f = fun i => ∏' d, (s d).
mulIndicator f i
参数：s : γ -> Set β；hs : Pairwise (Disjoint on s)；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport`：mulIndicator_iUn
ion_of_pairwise_disjoint_on_mulSupport (s : γ -> Set β) (f : β -> α) (hs : Pairw
ise (Disjoint on (fun j => s j inter f.mulSu…
· 使用定理 `pairwise_disjoint_mono`：pairwise_disjoint_mono [PartialOrder α] [OrderBo
t α] (hs : Pairwise (Disjoint on f)) (h : g <= f) : Pairwise (Disjoint on g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mulIndicator_iUnion_of_pairwise_disjoint (s : γ → Set β) (hs : Pairwise (Disjoint on s))
    (f : β → α) : (⋃ d, s d).mulIndicator f = fun i ↦ ∏' d, (s d).mulIndicator f i := by
  ext i
  exact mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport s f (pairwise_disjoint_mono hs
    <| fun _ _ hi ↦ hi.1) i

variable [T2Space α]

@[to_additive]
/-
**Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd {α' : Type*} [Co
mmMonoid α'] [TopologicalSpace α'] {e : α' -> α} (hes : Function.Surjective e) (
h1 : e 1 = 1) {f : β -> α} {g : γ -> α'} (h : forall {a}, HasProd f (e a) ↔ HasP
rod g a) : ∏' b, f b = e (∏' c, g c)
参数：hes : Function.Surjective e；h1 : e 1 = 1；h : forall {a}, HasProd f (e a) ↔ Ha
sProd g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.multipliable_iff_of_hasProd_iff`：Function.Surjective
.multipliable_iff_of_hasProd_iff {α' : Type*} [CommMonoid α'] [TopologicalSpace 
α'] {e : α' -> α} (hes : Function.Surject…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd {α' : Type*} [CommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h1 : e 1 = 1) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasProd f (e a) ↔ HasProd g a) : ∏' b, f b = e (∏' c, g c) :=
  by_cases (fun x ↦ (h.mpr x.hasProd).tprod_eq) fun hg : ¬Multipliable g ↦ by
    have hf : ¬Multipliable f := mt (hes.multipliable_iff_of_hasProd_iff @h).1 hg
    simp [tprod_def, hf, hg, h1]

@[to_additive]
/-
**tprod_eq_tprod_of_hasProd_iff_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_tprod_of_hasProd_iff_hasProd {f : β -> α} {g : γ -> α} (h : foral
l {a}, HasProd f a ↔ HasProd g a) : ∏' b, f b = ∏' c, g c
参数：h : forall {a}, HasProd f a ↔ HasProd g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd`：Function.Surj
ective.tprod_eq_tprod_of_hasProd_iff_hasProd {α' : Type*} [CommMonoid α'] [Topol
ogicalSpace α'] {e : α' -> α} (hes : Function.S…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
theorem tprod_eq_tprod_of_hasProd_iff_hasProd {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasProd f a ↔ HasProd g a) : ∏' b, f b = ∏' c, g c :=
  surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd rfl @h

section ContinuousMul

variable [ContinuousMul α]

@[to_additive]
/-
**Multipliable.tprod_mul** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] {f g : β → α}   {L : SummationFilter β} [T2Space α] [ContinuousMul α] 
[L.NeBot],   Multipliable f L → Multipliable g L → ∏'[L] (b : β), f b * g b = (∏
'[L] (b : β), f b) * ∏'[L] (b : β), g b
参数：b : β；∏'[L] (b : β), f b；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_mul [L.NeBot]
    (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] b, (f b * g b) = (∏'[L] b, f b) * ∏'[L] b, g b :=
  (hf.hasProd.mul hg.hasProd).tprod_eq

@[to_additive]
/-
**Multipliable.tprod_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.tprod_pow [L.NeBot] (hf : Multipliable f L) (n : Nat) : ∏'[L]
 b, (f b) ^ n = (∏'[L] b, f b) ^ n
参数：hf : Multipliable f L；n : Nat。
该定理/引理给出了一组等式。
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Multipliable.tprod_mul`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMono
id α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2S
pace α] [Con…
· 使用引理 `Multipliable.pow`：Multipliable.pow (hf : Multipliable f L) (n : Nat) : M
ultipliable (f · ^ n) L
-/
lemma Multipliable.tprod_pow [L.NeBot] (hf : Multipliable f L) (n : ℕ) :
    ∏'[L] b, (f b) ^ n = (∏'[L] b, f b) ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, (hf.pow n).tprod_mul hf, hn]

@[to_additive]
/-
**Multipliable.tprod_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α]   {L : SummationFilter β} [T2Space α] [ContinuousMul α]
 [L.NeBot] {f : γ → β → α} {s : Finset γ},   (∀ i ∈ s, Multipliable (f i) L) → ∏
'[L] (b : β), ∏ i ∈ s, f i b = ∏ i ∈ s, ∏'[L] (b : β), f i b
参数：∀ i ∈ s, Multipliable (f i) L；b : β；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `hasProd_prod`：hasProd_prod {f : γ -> β -> α} {a : γ -> α} {s : Finset γ}
 : (forall i in s, HasProd (f i) (a i) L) -> HasProd (fun b => ∏ i in s, f i b) 
(∏…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_finsetProd [L.NeBot] {f : γ → β → α} {s : Finset γ}
    (hf : ∀ i ∈ s, Multipliable (f i) L) : ∏'[L] b, ∏ i ∈ s, f i b = ∏ i ∈ s, ∏'[L] b, f i b :=
  (hasProd_prod fun i hi ↦ (hf i hi).hasProd).tprod_eq

/-- Version of `tprod_eq_mul_tprod_ite` for `CommMonoid` rather than `CommGroup`.
Requires a different convergence assumption involving `Function.update`. -/
@[to_additive /-- Version of `tsum_eq_add_tsum_ite` for `AddCommMonoid` rather than `AddCommGroup`.
Requires a different convergence assumption involving `Function.update`. -/]
/-
**Multipliable.tprod_eq_mul_tprod_ite'** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] {L : SummationFilter β} [T2Space α]   [ContinuousMul α] [inst_4 : Deci
dableEq β] [L.LeAtTop] [L.NeBot] {f : β → α} (b : β),   Multipliable (Function.u
pdate f b 1) L → ∏'[L] (x : β), f x = f b * ∏'[L] (x : β), if x = b then 1 else 
f x
参数：b : β；Function.update f b 1；x : β；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_congr`：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'
[L] b, f b = ∏'[L] b, g b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Multipliable.tprod_mul`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMono
id α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2S
pace α] [Con…
· 使用定理 `hasProd_single`：hasProd_single {f : β -> α} (b : β) (hf : forall (b') (_
 : b' != b), f b' = 1) (L
· 使用定理 `tprod_eq_mulSingle`：tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) 
(hf : forall b' != b, f b' = 1) : ∏'[L] b, f b = f b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
-/
protected theorem Multipliable.tprod_eq_mul_tprod_ite' [DecidableEq β] [L.LeAtTop] [L.NeBot]
    {f : β → α} (b : β) (hf : Multipliable (update f b 1) L) :
    ∏'[L] x, f x = f b * ∏'[L] x, ite (x = b) 1 (f x) :=
  calc
    ∏'[L] x, f x = ∏'[L] x, (ite (x = b) (f x) 1 * update f b 1 x) :=
      tprod_congr fun n ↦ by split_ifs with h <;> simp [h]
    _ = (∏'[L] x, ite (x = b) (f x) 1) * ∏'[L] x, update f b 1 x :=
      Multipliable.tprod_mul ⟨ite (b = b) (f b) 1, hasProd_single b (fun _ hb ↦ if_neg hb) L⟩ hf
    _ = ite (b = b) (f b) 1 * ∏'[L] x, update f b 1 x := by
      congr
      exact tprod_eq_mulSingle b fun b' hb' ↦ if_neg hb'
    _ = f b * ∏'[L] x, ite (x = b) 1 (f x) := by
      simp only [update, if_true, eq_rec_constant, dite_eq_ite]

@[to_additive]
/-
**Multipliable.tprod_mul_tprod_compl** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] {f : β → α} [T2Space α]   [ContinuousMul α] {s : Set β},   Multipliabl
e (f ∘ Subtype.val) →     Multipliable (f ∘ Subtype.val) → (∏' (x : ↑s), f ↑x) *
 ∏' (x : ↑sᶜ), f ↑x = ∏' (x : β), f x
参数：f ∘ Subtype.val；f ∘ Subtype.val；∏' (x : ↑s), f ↑x；x : ↑sᶜ；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.mul_compl`：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) 
: s -> α) a) (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_mul_tprod_compl {s : Set β}
    (hs : Multipliable (f ∘ (↑) : s → α)) (hsc : Multipliable (f ∘ (↑) : ↑sᶜ → α)) :
    (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm

@[to_additive]
/-
**Multipliable.tprod_union_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] {f : β → α} [T2Space α]   [ContinuousMul α] {s t : Set β},   Disjoint 
s t →     Multipliable (f ∘ Subtype.val) →       Multipliable (f ∘ Subtype.val) 
→ ∏' (x : ↑(s ∪ t)), f ↑x = (∏' (x : ↑s), f ↑x) * ∏' (x : ↑t), f ↑x
参数：f ∘ Subtype.val；f ∘ Subtype.val；x : ↑(s ∪ t)；∏' (x : ↑s), f ↑x；x : ↑t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.mul_disjoint`：HasProd.mul_disjoint {s t : Set β} (hs : Disjoint 
s t) (ha : HasProd (f ∘ (↑) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : H
asProd (f …
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_union_disjoint {s t : Set β} (hd : Disjoint s t)
    (hs : Multipliable (f ∘ (↑) : s → α)) (ht : Multipliable (f ∘ (↑) : t → α)) :
    ∏' x : ↑(s ∪ t), f x = (∏' x : s, f x) * ∏' x : t, f x :=
  (hs.hasProd.mul_disjoint hd ht.hasProd).tprod_eq

@[to_additive]
/-
**Multipliable.tprod_finset_bUnion_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiplia
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] {f : β → α} [T2Space α]   [ContinuousMul α] {ι : Type u_4} {s : Finset
 ι} {t : ι → Set β},   (↑s).Pairwise (Function.onFun Disjoint t) →     (∀ i ∈ s,
 Multipliable (f ∘ Subtype.val)) → ∏' (x : ↑(⋃ i ∈ s, t i)), f ↑x = ∏ i ∈ s, ∏' 
(x : ↑(t i)), f ↑x
参数：↑s；Function.onFun Disjoint t；∀ i ∈ s, Multipliable (f ∘ Subtype.val)；x : ↑(⋃ 
i ∈ s, t i)；x : ↑(t i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasProd_prod_disjoint`：hasProd_prod_disjoint {ι} (s : Finset ι) {t : ι -
> Set β} {a : ι -> α} (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : forall i
 in s, HasP…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Multipliable (f ∘ (↑) : t i → α)) :
    ∏' x : ⋃ i ∈ s, t i, f x = ∏ i ∈ s, ∏' x : t i, f x :=
  (hasProd_prod_disjoint _ hd fun i hi ↦ (hf i hi).hasProd).tprod_eq

end ContinuousMul

end tprod

section CommMonoidWithZero
variable [CommMonoidWithZero α] [TopologicalSpace α] {f : β → α} {L : SummationFilter β}

/-
**hasProd_zero_of_exists_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProd_zero_of_exists_eq_zero (hf : exists b, f b = 0) [L.LeAtTop] : HasP
rod f 0 L
参数：hf : exists b, f b = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `SummationFilter.LeAtTop.le_atTop`：∀ {β : Type u_2} {L : SummationFilter 
β} [self : L.LeAtTop], L.filter ≤ Filter.atTop
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
-/
lemma hasProd_zero_of_exists_eq_zero (hf : ∃ b, f b = 0) [L.LeAtTop] : HasProd f 0 L := by
  obtain ⟨b, hb⟩ := hf
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_ge_atTop {b}).filter_mono L.le_atTop] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hb).symm
/-
**hasProd_zero_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProd_zero_zero [Nonempty β] [L.LeAtTop] : HasProd (fun _ => 0 : β -> α)
 0 L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProd_zero_of_exists_eq_zero`：hasProd_zero_of_exists_eq_zero (hf : exi
sts b, f b = 0) [L.LeAtTop] : HasProd f 0 L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hasProd_zero_zero [Nonempty β] [L.LeAtTop] : HasProd (fun _ ↦ 0 : β → α) 0 L := by
  obtain ⟨b⟩ := ‹Nonempty β›
  exact hasProd_zero_of_exists_eq_zero ⟨b, by simp⟩
/-
**multipliable_of_exists_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_of_exists_eq_zero (hf : exists b, f b = 0) [L.LeAtTop] : Mult
ipliable f L
参数：hf : exists b, f b = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProd_zero_of_exists_eq_zero`：hasProd_zero_of_exists_eq_zero (hf : exi
sts b, f b = 0) [L.LeAtTop] : HasProd f 0 L
-/
lemma multipliable_of_exists_eq_zero (hf : ∃ b, f b = 0) [L.LeAtTop] : Multipliable f L :=
  ⟨0, hasProd_zero_of_exists_eq_zero hf⟩
/-
**multipliable_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_zero [L.LeAtTop] : Multipliable (fun _ => 0 : β -> α) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `hasProd_zero_zero`：hasProd_zero_zero [Nonempty β] [L.LeAtTop] : HasProd 
(fun _ => 0 : β -> α) 0 L
-/
lemma multipliable_zero [L.LeAtTop] : Multipliable (fun _ ↦ 0 : β → α) L := by
  obtain hβ | hβ := isEmpty_or_nonempty β
  · simp
  · exact ⟨0, hasProd_zero_zero⟩
/-
**tprod_of_exists_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_of_exists_eq_zero [T2Space α] [L.NeBot] [L.LeAtTop] (hf : exists b, 
f b = 0) : ∏'[L] b, f b = 0
参数：hf : exists b, f b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用引理 `hasProd_zero_of_exists_eq_zero`：hasProd_zero_of_exists_eq_zero (hf : exi
sts b, f b = 0) [L.LeAtTop] : HasProd f 0 L
-/
lemma tprod_of_exists_eq_zero [T2Space α] [L.NeBot] [L.LeAtTop] (hf : ∃ b, f b = 0) :
    ∏'[L] b, f b = 0 :=
  (hasProd_zero_of_exists_eq_zero hf).tprod_eq
/-
**tprod_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoidWithZero α] [inst_1 : To
pologicalSpace α] {L : SummationFilter β}   [T2Space α] [Nonempty β] [L.NeBot] [
L.LeAtTop], ∏'[L] (x : β), 0 = 0
参数：x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用引理 `hasProd_zero_zero`：hasProd_zero_zero [Nonempty β] [L.LeAtTop] : HasProd 
(fun _ => 0 : β -> α) 0 L
-/
@[simp] lemma tprod_zero [T2Space α] [Nonempty β] [L.NeBot] [L.LeAtTop] :
    ∏'[L] _, (0 : α) = 0 :=
  hasProd_zero_zero.tprod_eq

end CommMonoidWithZero

