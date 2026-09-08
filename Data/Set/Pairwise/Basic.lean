/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Pairwise
public import Mathlib.Logic.Relation

/-!
# Relations holding pairwise

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `Pairwise`. It is possible that an intermediate file,
with more imports than `Logic.Pairwise` but not importing `Data.Set.Function` would be appropriate
to hold many of these basic facts.

## Main declarations

* `Set.PairwiseDisjoint`: `s.PairwiseDisjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `Disjoint`.

## Notes

The spelling `s.PairwiseDisjoint id` is preferred over `s.Pairwise Disjoint` to permit dot notation
on `Set.PairwiseDisjoint`, even though the latter unfolds to something nicer.
-/

@[expose] public section


open Function Order Set

variable {α β γ ι ι' : Type*} {r p : α → α → Prop}

section Pairwise

variable {f g : ι → α} {s t : Set α} {a b : α}

/-
**pairwise_on_bool** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_on_bool [Std.Symm r] {a b : α} : Pairwise (r on fun c => cond c a
 b) ↔ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
theorem pairwise_on_bool [Std.Symm r] {a b : α} : Pairwise (r on fun c ↦ cond c a b) ↔ r a b := by
  simpa [Pairwise, Function.onFun] using symm
/-
**pairwise_disjoint_on_bool** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_disjoint_on_bool [PartialOrder α] [OrderBot α] {a b : α} : Pairwi
se (Disjoint on fun c => cond c a b) ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pairwise_on_bool`：pairwise_on_bool [Std.Symm r] {a b : α} : Pairwise (r 
on fun c => cond c a b) ↔ r a b
-/
theorem pairwise_disjoint_on_bool [PartialOrder α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool
/-
**Std.Symm.pairwise_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Symm.pairwise_on [LinearOrder ι] [Std.Symm r] (f : ι -> α) : Pairwise 
(r on f) ↔ forall ⦃m n⦄, m < n -> r (f m) (f n) where mp h _m _n hmn
参数：f : ι -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
theorem Std.Symm.pairwise_on [LinearOrder ι] [Std.Symm r] (f : ι → α) :
    Pairwise (r on f) ↔ ∀ ⦃m n⦄, m < n → r (f m) (f n) where
  mp h _m _n hmn := h hmn.ne
  mpr h _m _n hmn := hmn.lt_or_gt.elim (@h _ _) fun h' ↦ symm_of r <| h h'

@[deprecated (since := "2026-06-10")] alias Symmetric.pairwise_on := Std.Symm.pairwise_on
/-
**pairwise_disjoint_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_disjoint_on [PartialOrder α] [OrderBot α] [LinearOrder ι] (f : ι 
-> α) : Pairwise (Disjoint on f) ↔ forall ⦃m n⦄, m < n -> Disjoint (f m) (f n)
参数：f : ι -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.pairwise_on`：Std.Symm.pairwise_on [LinearOrder ι] [Std.Symm r] 
(f : ι -> α) : Pairwise (r on f) ↔ forall ⦃m n⦄, m < n -> r (f m) (f n) where mp
 h _m _n h…
-/
theorem pairwise_disjoint_on [PartialOrder α] [OrderBot α] [LinearOrder ι] (f : ι → α) :
    Pairwise (Disjoint on f) ↔ ∀ ⦃m n⦄, m < n → Disjoint (f m) (f n) :=
  Std.Symm.pairwise_on f
/-
**pairwise_disjoint_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_disjoint_mono [PartialOrder α] [OrderBot α] (hs : Pairwise (Disjo
int on f)) (h : g <= f) : Pairwise (Disjoint on g)
参数：hs : Pairwise (Disjoint on f)；h : g <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
-/
theorem pairwise_disjoint_mono [PartialOrder α] [OrderBot α] (hs : Pairwise (Disjoint on f))
    (h : g ≤ f) : Pairwise (Disjoint on g) :=
  hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij
/-
**Pairwise.disjoint_extend_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pairwise.disjoint_extend_bot [PartialOrder γ] [OrderBot γ] {e : α -> β} {f
 : α -> γ} (hf : Pairwise (Disjoint on f)) (he : FactorsThrough f e) : Pairwise 
(Disjoint on extend e f ⊥)
参数：hf : Pairwise (Disjoint on f)；he : FactorsThrough f e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.FactorsThrough.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ
 : Sort u_3} {f : α → β} {g : α → γ},   Function.FactorsThrough g f → ∀ (e' : β 
→ γ) (a : α), Function.ext…
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `disjoint_bot_right`：disjoint_bot_right : Disjoint a ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
-/
theorem Pairwise.disjoint_extend_bot [PartialOrder γ] [OrderBot γ]
    {e : α → β} {f : α → γ} (hf : Pairwise (Disjoint on f)) (he : FactorsThrough f e) :
    Pairwise (Disjoint on extend e f ⊥) := by
  intro b₁ b₂ hne
  rcases em (∃ a₁, e a₁ = b₁) with ⟨a₁, rfl⟩ | hb₁
  · rcases em (∃ a₂, e a₂ = b₂) with ⟨a₂, rfl⟩ | hb₂
    · simpa only [onFun, he.extend_apply] using! hf (ne_of_apply_ne e hne)
    · simpa only [onFun, extend_apply' _ _ _ hb₂] using! disjoint_bot_right
  · simpa only [onFun, extend_apply' _ _ _ hb₁] using! disjoint_bot_left

namespace Set

/-
**Set.Pairwise.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t ⊆ s → s.Pairwise r → 
t.Pairwise r
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.mono (h : t ⊆ s) (hs : s.Pairwise r) : t.Pairwise r :=
  fun _x xt _y yt => hs (h xt) (h yt)
/-
**Set.Pairwise.mono'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r ≤ p → s.Pairwise r → 
s.Pairwise p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
-/
theorem Pairwise.mono' (H : r ≤ p) (hr : s.Pairwise r) : s.Pairwise p :=
  hr.imp H
/-
**Set.Pairwise.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, s.Pairwise r → ∀ (t : Set
 α), (s ∩ t).Pairwise r
参数：t : Set α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem Pairwise.inter_left (hs : s.Pairwise r) (t : Set α) : (s ∩ t).Pairwise r :=
  hs.mono Set.inter_subset_left
/-
**Set.Pairwise.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, s.Pairwise r → ∀ (t : Set
 α), (t ∩ s).Pairwise r
参数：t : Set α；t ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem Pairwise.inter_right (hs : s.Pairwise r) (t : Set α) : (t ∩ s).Pairwise r :=
  hs.mono Set.inter_subset_right
/-
**Set.pairwise_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_top (s : Set α) : s.Pairwise ⊤
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_of_forall`：pairwise_of_forall (s : Set α) (r : α -> α -> Pr
op) (h : forall a b, r a b) : s.Pairwise r
· 使用定理 `trivial`：True
-/
theorem pairwise_top (s : Set α) : s.Pairwise ⊤ :=
  pairwise_of_forall s _ fun _ _ => trivial
/-
**Set.Subsingleton.pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Subsingleton → ∀ (r : α → α → Prop), s.Pai
rwise r
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Subsingleton.pairwise (h : s.Subsingleton) (r : α → α → Prop) : s.Pairwise r :=
  fun _x hx _y hy hne => (hne (h hx hy)).elim

@[simp]
/-
**Set.pairwise_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pairwise r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
theorem pairwise_empty (r : α → α → Prop) : (∅ : Set α).Pairwise r :=
  subsingleton_empty.pairwise r

@[simp]
/-
**Set.pairwise_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_singleton (a : α) (r : α -> α -> Prop) : Set.Pairwise {a} r
参数：a : α；r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem pairwise_singleton (a : α) (r : α → α → Prop) : Set.Pairwise {a} r :=
  subsingleton_singleton.pairwise r
/-
**Set.pairwise_iff_of_refl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_iff_of_refl [Std.Refl r] : s.Pairwise r ↔ forall ⦃a⦄, a in s -> f
orall ⦃b⦄, b in s -> r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `of_eq`：of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b
-/
theorem pairwise_iff_of_refl [Std.Refl r] : s.Pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
  forall₄_congr fun _ _ _ _ => or_iff_not_imp_left.symm.trans <| or_iff_right_of_imp of_eq

alias ⟨Pairwise.of_refl, _⟩ := pairwise_iff_of_refl
/-
**Set.Nonempty.pairwise_iff_exists_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempt
y`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → Prop} {f : ι → α} [IsEquiv α 
r] {s : Set ι},   s.Nonempty → (s.Pairwise (Function.onFun r f) ↔ ∃ z, ∀ x ∈ s, 
r (f x) z)
参数：s.Pairwise (Function.onFun r f) ↔ ∃ z, ∀ x ∈ s, r (f x) z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
-/
theorem Nonempty.pairwise_iff_exists_forall [IsEquiv α r] {s : Set ι} (hs : s.Nonempty) :
    s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z := by
  constructor
  · rcases hs with ⟨y, hy⟩
    refine fun H => ⟨f y, fun x hx => ?_⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply Std.Refl.refl
    · exact H hx hy hne
  · rintro ⟨z, hz⟩ x hx y hy _
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (symm <| hz _ hy)

/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.pairwise_eq_iff_exists_eq` for a version that assumes `[Nonempty ι]` instead of
`Set.Nonempty s`. -/
/-
**Set.Nonempty.pairwise_eq_iff_exists_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty
`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {s : Set α},   s.Nonempty → ∀ {f : α → ι},
 (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z
参数：s.Pairwise fun x y => f x = f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.pairwise_iff_exists_forall`：∀ {α : Type u_1} {ι : Type u_4}
 {r : α → α → Prop} {f : ι → α} [IsEquiv α r] {s : Set ι},   s.Nonempty → (s.Pai
rwise (Function.onFun r f) ↔ …

--- 原说明 ---
For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and
 only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.pairwise_eq_iff_exists_eq` for a version that assumes `[Nonempty ι]` instea
d of
`Set.Nonempty s`.
-/
theorem Nonempty.pairwise_eq_iff_exists_eq {s : Set α} (hs : s.Nonempty) {f : α → ι} :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  hs.pairwise_iff_exists_forall
/-
**Set.pairwise_iff_exists_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α -> ι) {r : ι ->
 ι -> Prop} [IsEquiv ι r] : s.Pairwise (r on f) ↔ exists z, forall x in s, r (f 
x) z
参数：s : Set α；f : α -> ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.pairwise_iff_exists_forall`：∀ {α : Type u_1} {ι : Type u_4}
 {r : α → α → Prop} {f : ι → α} [IsEquiv α r] {s : Set ι},   s.Nonempty → (s.Pai
rwise (Function.onFun r f) ↔ …
-/
theorem pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α → ι) {r : ι → ι → Prop}
    [IsEquiv ι r] : s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  · exact hne.pairwise_iff_exists_forall

/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.Nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `Set.Nonempty s` instead of
`[Nonempty ι]`. -/
/-
**Set.pairwise_eq_iff_exists_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α -> ι) : (s.Pairw
ise fun x y => f x = f y) ↔ exists z, forall x in s, f x = z
参数：s : Set α；f : α -> ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_iff_exists_forall`：pairwise_iff_exists_forall [Nonempty ι] 
(s : Set α) (f : α -> ι) {r : ι -> ι -> Prop} [IsEquiv ι r] : s.Pairwise (r on f
) ↔ exists z, forall…

--- 原说明 ---
A function `f : α → ι` with nonempty codomain takes pairwise equal values on a s
et `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See al
so
`Set.Nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `Set.Nonempt
y s` instead of
`[Nonempty ι]`.
-/
theorem pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α → ι) :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  pairwise_iff_exists_forall s f
/-
**Set.pairwise_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_union : (s union t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ fo
rall a in s, forall b in t, a != b -> r a b ∧ r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pairwise_union :
    (s ∪ t).Pairwise r ↔
    s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b ∧ r b a := by
  grind [Set.Pairwise]
/-
**Set.pairwise_union_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_union_of_symm [Std.Symm r] : (s union t).Pairwise r ↔ s.Pairwise 
r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a != b -> r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.pairwise_union`：pairwise_union : (s union t).Pairwise r ↔ s.Pairwise
 r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a != b -> r a b ∧ r b a
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_union_of_symm [Std.Symm r] :
    (s ∪ t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b :=
  pairwise_union.trans <| by simp only [Std.Symm.iff, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_union_of_symmetric := pairwise_union_of_symm
/-
**Set.pairwise_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_insert : (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, 
a != b -> r a b ∧ r b a
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_insert :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b ∧ r b a := by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and, mem_singleton_iff, forall_eq]
/-
**Set.pairwise_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_insert_of_notMem (ha : a ∉ s) : (insert a s).Pairwise r ↔ s.Pairw
ise r ∧ forall b in s, r a b ∧ r b a
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.pairwise_insert`：pairwise_insert : (insert a s).Pairwise r ↔ s.Pairw
ise r ∧ forall b in s, a != b -> r a b ∧ r b a
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_insert_of_notMem (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_insert.trans <|
    and_congr_right' <| forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]
/-
**Set.Pairwise.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},   s.Pairwise r → 
(∀ b ∈ s, a ≠ b → r a b ∧ r b a) → (insert a s).Pairwise r
参数：∀ b ∈ s, a ≠ b → r a b ∧ r b a；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwise_insert`：pairwise_insert : (insert a s).Pairwise r ↔ s.Pairw
ise r ∧ forall b in s, a != b -> r a b ∧ r b a
-/
protected theorem Pairwise.insert (hs : s.Pairwise r) (h : ∀ b ∈ s, a ≠ b → r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  pairwise_insert.2 ⟨hs, h⟩
/-
**Set.Pairwise.insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},   a ∉ s → s.Pairw
ise r → (∀ b ∈ s, r a b ∧ r b a) → (insert a s).Pairwise r
参数：∀ b ∈ s, r a b ∧ r b a；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwise_insert_of_notMem`：pairwise_insert_of_notMem (ha : a ∉ s) : 
(insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, r a b ∧ r b a
-/
theorem Pairwise.insert_of_notMem (ha : a ∉ s) (hs : s.Pairwise r) (h : ∀ b ∈ s, r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  (pairwise_insert_of_notMem ha).2 ⟨hs, h⟩
/-
**Set.pairwise_insert_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_insert_of_symm [Std.Symm r] : (insert a s).Pairwise r ↔ s.Pairwis
e r ∧ forall b in s, a != b -> r a b
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
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
· 使用定理 `Function.instSymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Symm
 r], Std.Symm (Function.swap r)
· 使用定理 `instSymmNe_mathlib`：∀ (α : Sort u_1), Std.Symm Ne
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_insert_of_symm [Std.Symm r] :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b := by
  simp only [pairwise_insert, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_insert_of_symmetric := pairwise_insert_of_symm
/-
**Set.pairwise_insert_of_symm_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_insert_of_symm_of_notMem [Std.Symm r] (ha : a ∉ s) : (insert a s)
.Pairwise r ↔ s.Pairwise r ∧ forall b in s, r a b
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pairwise_insert_of_notMem`：pairwise_insert_of_notMem (ha : a ∉ s) : 
(insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, r a b ∧ r b a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_insert_of_symm_of_notMem [Std.Symm r] (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b := by
  simp only [pairwise_insert_of_notMem ha, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")]
alias pairwise_insert_of_symmetric_of_notMem := pairwise_insert_of_symm_of_notMem
/-
**Set.Pairwise.insert_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α} [Std.Symm r],   s.
Pairwise r → (∀ b ∈ s, a ≠ b → r a b) → (insert a s).Pairwise r
参数：∀ b ∈ s, a ≠ b → r a b；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
-/
theorem Pairwise.insert_of_symm [Std.Symm r] (hs : s.Pairwise r)
    (h : ∀ b ∈ s, a ≠ b → r a b) : (insert a s).Pairwise r :=
  pairwise_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias Pairwise.insert_of_symmetric := Pairwise.insert_of_symm
/-
**Set.pairwise_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_pair : Set.Pairwise {a, b} r ↔ a != b -> r a b ∧ r b a
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_pair : Set.Pairwise {a, b} r ↔ a ≠ b → r a b ∧ r b a := by simp [pairwise_insert]
/-
**Set.pairwise_pair_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_pair_of_symm [Std.Symm r] : Set.Pairwise {a, b} r ↔ a != b -> r a
 b
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_pair_of_symm [Std.Symm r] : Set.Pairwise {a, b} r ↔ a ≠ b → r a b := by
  simp [pairwise_insert_of_symm]

@[deprecated (since := "2026-06-10")] alias pairwise_pair_of_symmetric := pairwise_pair_of_symm
/-
**Set.pairwise_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r := by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]

@[simp]
/-
**Set.pairwise_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_bot_iff : s.Pairwise (⊥ : α -> α -> Prop) ↔ (s : Set α).Subsingle
ton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
theorem pairwise_bot_iff : s.Pairwise (⊥ : α → α → Prop) ↔ (s : Set α).Subsingleton :=
  ⟨fun h _a ha _b hb => h.eq ha hb id, fun h => h.pairwise _⟩

alias ⟨Pairwise.subsingleton, _⟩ := pairwise_bot_iff

/-- See also `Function.injective_iff_pairwise_ne` -/
/-
**Set.injOn_iff_pairwise_ne** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：injOn_iff_pairwise_ne {s : Set ι} : InjOn f s ↔ s.Pairwise (f · != f ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `Function.injective_iff_pairwise_ne`
-/
lemma injOn_iff_pairwise_ne {s : Set ι} : InjOn f s ↔ s.Pairwise (f · ≠ f ·) := by
  simp only [InjOn, Set.Pairwise, not_imp_not]

alias ⟨InjOn.pairwise_ne, _⟩ := injOn_iff_pairwise_ne
/-
**Set.Pairwise.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → Prop} {f : ι → α} {s : Set ι}
,   s.Pairwise (Function.onFun r f) → (f '' s).Pairwise r
参数：Function.onFun r f；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
protected theorem Pairwise.image {s : Set ι} (h : s.Pairwise (r on f)) : (f '' s).Pairwise r :=
  forall_mem_image.2 fun _x hx ↦ forall_mem_image.2 fun _y hy hne ↦ h hx hy <| ne_of_apply_ne _ hne

/-- See also `Set.Pairwise.image`. -/
/-
**Set.InjOn.pairwise_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → Prop} {f : ι → α} {s : Set ι}
,   Set.InjOn f s → ((f '' s).Pairwise r ↔ s.Pairwise (Function.onFun r f))
参数：(f '' s).Pairwise r ↔ s.Pairwise (Function.onFun r f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `Set.Pairwise.image`.
-/
theorem InjOn.pairwise_image {s : Set ι} (h : s.InjOn f) :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) := by
  simp +contextual [h.eq_iff, Set.Pairwise]
/-
**Set._root_.Pairwise.range_pairwise** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Pairwise.range_pairwise (hr : Pairwise (r on f)) : (Set.range f).Pairwise r :=
  image_univ ▸ (pairwise_univ.mpr hr).image

end Set

end Pairwise

/-
**pairwise_subtype_iff_pairwise_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_subtype_iff_pairwise_set (s : Set α) (r : α -> α -> Prop) : (Pair
wise fun (x : s) (y : s) => r x y) ↔ s.Pairwise r
参数：s : Set α；r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_subtype_iff_pairwise_set (s : Set α) (r : α → α → Prop) :
    (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pairwise r := by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne, Subtype.ext_iff]

alias ⟨Pairwise.set_of_subtype, Set.Pairwise.subtype⟩ := pairwise_subtype_iff_pairwise_set

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι → α}

/-- A set is `PairwiseDisjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.Pairwise Disjoint` is (definitionally) the same as `s.PairwiseDisjoint id`. We prefer the latter
in order to allow dot notation on `Set.PairwiseDisjoint`, even though the former unfolds more
nicely. -/
/-
**Set.PairwiseDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：PairwiseDisjoint (s : Set ι) (f : ι -> α) : Prop
参数：s : Set ι；f : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is `PairwiseDisjoint` under `f`, if the images of any distinct two element
s under `f`
are disjoint.

`s.Pairwise Disjoint` is (definitionally) the same as `s.PairwiseDisjoint id`. W
e prefer the latter
in order to allow dot notation on `Set.PairwiseDisjoint`, even though the former
 unfolds more
nicely.
-/
def PairwiseDisjoint (s : Set ι) (f : ι → α) : Prop :=
  s.Pairwise (Disjoint on f)
/-
**Set.PairwiseDisjoint.subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s t : Set ι} {f : ι → α},   t.PairwiseDisjoint f → s ⊆ t → s.PairwiseDisjoi
nt f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
theorem PairwiseDisjoint.subset (ht : t.PairwiseDisjoint f) (h : s ⊆ t) : s.PairwiseDisjoint f :=
  Pairwise.mono h ht
/-
**Set.PairwiseDisjoint.mono_on** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f g : ι → α},   s.PairwiseDisjoint f → (∀ ⦃i : ι⦄, i ∈ s → g i 
≤ f i) → s.PairwiseDisjoint g
参数：∀ ⦃i : ι⦄, i ∈ s → g i ≤ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
-/
theorem PairwiseDisjoint.mono_on (hs : s.PairwiseDisjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) :
    s.PairwiseDisjoint g := fun _a ha _b hb hab => (hs ha hb hab).mono (h ha) (h hb)
/-
**Set.PairwiseDisjoint.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f g : ι → α},   s.PairwiseDisjoint f → g ≤ f → s.PairwiseDisjoi
nt g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.mono_on`：∀ {α : Type u_1} {ι : Type u_4} [inst : Pa
rtialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f g : ι → α},   s.PairwiseDisjo
int f → (∀ ⦃i : ι⦄…
-/
theorem PairwiseDisjoint.mono (hs : s.PairwiseDisjoint f) (h : g ≤ f) : s.PairwiseDisjoint g :=
  hs.mono_on fun i _ => h i

@[simp]
/-
**Set.pairwiseDisjoint_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_empty : (∅ : Set ι).PairwiseDisjoint f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
theorem pairwiseDisjoint_empty : (∅ : Set ι).PairwiseDisjoint f :=
  pairwise_empty _

@[simp]
/-
**Set.pairwiseDisjoint_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_singleton (i : ι) (f : ι -> α) : PairwiseDisjoint {i} f
参数：i : ι；f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
theorem pairwiseDisjoint_singleton (i : ι) (f : ι → α) : PairwiseDisjoint {i} f :=
  pairwise_singleton i _

@[simp]
/-
**Set.pairwiseDisjoint_singleton'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_singleton' (s : Set ι) : s.PairwiseDisjoint (singleton : 
ι -> Set ι)
参数：s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pairwiseDisjoint_singleton' (s : Set ι) :
    s.PairwiseDisjoint (singleton : ι → Set ι) := by intro; grind
/-
**Set.pairwiseDisjoint_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_insert {i : ι} : (insert i s).PairwiseDisjoint f ↔ s.Pair
wiseDisjoint f ∧ forall j in s, i != j -> Disjoint (f i) (f j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
-/
theorem pairwiseDisjoint_insert {i : ι} :
    (insert i s).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧ ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j) :=
  pairwise_insert_of_symm
/-
**Set.pairwiseDisjoint_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_insert_of_notMem {i : ι} (hi : i ∉ s) : (insert i s).Pair
wiseDisjoint f ↔ s.PairwiseDisjoint f ∧ forall j in s, Disjoint (f i) (f j)
参数：hi : i ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_insert_of_symm_of_notMem`：pairwise_insert_of_symm_of_notMem
 [Std.Symm r] (ha : a ∉ s) : (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b i
n s, r a b
-/
theorem pairwiseDisjoint_insert_of_notMem {i : ι} (hi : i ∉ s) :
    (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ ∀ j ∈ s, Disjoint (f i) (f j) :=
  pairwise_insert_of_symm_of_notMem hi
/-
**Set.PairwiseDisjoint.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {i : ι}, (∀ j ∈ s, i ≠ j
 → Disjoint (f i) (f j)) → (insert i s).PairwiseDisjoint f
参数：∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)；insert i s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwiseDisjoint_insert`：pairwiseDisjoint_insert {i : ι} : (insert i
 s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ forall j in s, i != j -> Disjoin
t (f i) (f j)
-/
protected theorem PairwiseDisjoint.insert (hs : s.PairwiseDisjoint f) {i : ι}
    (h : ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  pairwiseDisjoint_insert.2 ⟨hs, h⟩
/-
**Set.PairwiseDisjoint.insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseD
isjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {i : ι}, i ∉ s → (∀ j ∈ 
s, Disjoint (f i) (f j)) → (insert i s).PairwiseDisjoint f
参数：∀ j ∈ s, Disjoint (f i) (f j)；insert i s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwiseDisjoint_insert_of_notMem`：pairwiseDisjoint_insert_of_notMem
 {i : ι} (hi : i ∉ s) : (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧
 forall j in s, Disjoint (f…
-/
theorem PairwiseDisjoint.insert_of_notMem (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
    (h : ∀ j ∈ s, Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  (pairwiseDisjoint_insert_of_notMem hi).2 ⟨hs, h⟩
/-
**Set.PairwiseDisjoint.image_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoi
nt`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {g : ι → ι}, f ∘ g ≤ f →
 (g '' s).PairwiseDisjoint f
参数：g '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem PairwiseDisjoint.image_of_le (hs : s.PairwiseDisjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
    (g '' s).PairwiseDisjoint f := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)
/-
**Set.InjOn.pairwiseDisjoint_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : PartialOrder α] [i
nst_1 : OrderBot α] {f : ι → α} {g : ι' → ι}   {s : Set ι'}, Set.InjOn g s → ((g
 '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g))
参数：(g '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.pairwise_image`：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → P
rop} {f : ι → α} {s : Set ι},   Set.InjOn f s → ((f '' s).Pairwise r ↔ s.Pairwis
e (Function.on…
-/
theorem InjOn.pairwiseDisjoint_image {g : ι' → ι} {s : Set ι'} (h : s.InjOn g) :
    (g '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g) :=
  h.pairwise_image
/-
**Set.PairwiseDisjoint.range** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f : ι → α} (g : ↑s → ι),   (∀ (i : ↑s), f (g i) ≤ f ↑i) → s.Pai
rwiseDisjoint f → (Set.range g).PairwiseDisjoint f
参数：g : ↑s → ι；∀ (i : ↑s), f (g i) ≤ f ↑i；Set.range g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem PairwiseDisjoint.range (g : s → ι) (hg : ∀ i : s, f (g i) ≤ f i)
    (ht : s.PairwiseDisjoint f) : (range g).PairwiseDisjoint f := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact ((ht x.2 y.2) fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)
/-
**Set.pairwiseDisjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_union : (s union t).PairwiseDisjoint f ↔ s.PairwiseDisjoi
nt f ∧ t.PairwiseDisjoint f ∧ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in t -> i != j
 -> Disjoint (f i) (f j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_union_of_symm`：pairwise_union_of_symm [Std.Symm r] : (s uni
on t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a
 != b -> r a b
-/
theorem pairwiseDisjoint_union :
    (s ∪ t).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧
        t.PairwiseDisjoint f ∧ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j) :=
  pairwise_union_of_symm
/-
**Set.PairwiseDisjoint.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s t : Set ι} {f : ι → α},   s.PairwiseDisjoint f →     t.PairwiseDisjoint f
 →       (∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)) → 
(s ∪ t).PairwiseDisjoint f
参数：∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)；s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwiseDisjoint_union`：pairwiseDisjoint_union : (s union t).Pairwis
eDisjoint f ↔ s.PairwiseDisjoint f ∧ t.PairwiseDisjoint f ∧ forall ⦃i⦄, i in s -
> forall ⦃j⦄, j …
-/
theorem PairwiseDisjoint.union (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
    (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)) : (s ∪ t).PairwiseDisjoint f :=
  pairwiseDisjoint_union.2 ⟨hs, ht, h⟩

-- classical
/-
**Set.PairwiseDisjoint.elim** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s
 → ¬Disjoint (f i) (f j) → i = j
参数：f i；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
-/
theorem PairwiseDisjoint.elim (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : ¬Disjoint (f i) (f j)) : i = j :=
  hs.eq hi hj h
/-
**Set.PairwiseDisjoint.eq_or_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDis
joint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot
 α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s
 → i = j ∨ Disjoint (f i) (f j)
参数：f i；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
-/
lemma PairwiseDisjoint.eq_or_disjoint
    (h : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    i = j ∨ Disjoint (f i) (f j) := by
  rw [or_iff_not_imp_right]
  exact h.elim hi hj
/-
**Set.pairwiseDisjoint_range_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_range_iff {α β : Type*} {f : α -> (Set β)} : (range f).Pa
irwiseDisjoint id ↔ forall x y, f x != f y -> Disjoint (f x) (f y)
参数：Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pairwiseDisjoint_range_iff {α β : Type*} {f : α → (Set β)} :
    (range f).PairwiseDisjoint id ↔ ∀ x y, f x ≠ f y → Disjoint (f x) (f y) := by
  aesop (add simp [PairwiseDisjoint, Set.Pairwise])

/-- If the range of `f` is pairwise disjoint, then the image of any set `s` under `f` is as well. -/
/-
**Set._root_.Pairwise.pairwiseDisjoint** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the range of `f` is pairwise disjoint, then the image of any set `s` under `f
` is as well.
-/
lemma _root_.Pairwise.pairwiseDisjoint (h : Pairwise (Disjoint on f)) (s : Set ι) :
    s.PairwiseDisjoint f := h.set_pairwise s

end PartialOrderBot

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {s : Set ι} {f : ι → α}

-- classical
/-
**Set.PairwiseDisjoint.elim'** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : SemilatticeInf α] [inst_1 : OrderB
ot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈
 s → f i ⊓ f j ≠ ⊥ → i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
-/
theorem PairwiseDisjoint.elim' (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : f i ⊓ f j ≠ ⊥) : i = j :=
  (hs.elim hi hj) fun hij => h hij.eq_bot
/-
**Set.PairwiseDisjoint.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`
。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : SemilatticeInf α] [inst_1 : OrderB
ot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈
 s → f i ≠ ⊥ → f i ≤ f j → i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim'`：∀ {α : Type u_1} {ι : Type u_4} [inst : Semi
latticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoin
t f → ∀ {i j : ι…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem PairwiseDisjoint.eq_of_le (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hf : f i ≠ ⊥) (hij : f i ≤ f j) : i = j :=
  (hs.elim' hi hj) fun h => hf <| (inf_of_le_left hij).symm.trans h

end SemilatticeInfBot

/-! ### Pairwise disjoint set of sets -/

variable {s : Set ι} {t : Set ι'}

/-
**Set.pairwiseDisjoint_range_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_range_singleton : (range (singleton : ι -> Set ι)).Pairwi
seDisjoint id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.range_pairwise`：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → Pr
op} {f : ι → α}, Pairwise (Function.onFun r f) → (Set.range f).Pairwise r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
-/
theorem pairwiseDisjoint_range_singleton :
    (range (singleton : ι → Set ι)).PairwiseDisjoint id :=
  Pairwise.range_pairwise fun _ _ => disjoint_singleton.2
/-
**Set.pairwiseDisjoint_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_fiber (f : ι -> α) (s : Set α) : s.PairwiseDisjoint fun a
 => f ⁻¹' {a}
参数：f : ι -> α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pairwiseDisjoint_fiber (f : ι → α) (s : Set α) : s.PairwiseDisjoint fun a => f ⁻¹' {a} :=
  fun _a _ _b _ h => disjoint_iff_inf_le.mpr fun _i ⟨hia, hib⟩ => h <| (Eq.symm hia).trans hib

-- classical
/-
**Set.PairwiseDisjoint.elim_set** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`
。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {s : Set ι} {f : ι → Set α},   s.PairwiseD
isjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ f i, a ∈ f j → i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
-/
theorem PairwiseDisjoint.elim_set {s : Set ι} {f : ι → Set α} (hs : s.PairwiseDisjoint f) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj <| not_disjoint_iff.2 ⟨a, hai, haj⟩
/-
**Set.PairwiseDisjoint.prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} {ι' : Type u_5} {s : Set ι}
 {t : Set ι'} {f : ι → Set α}   {g : ι' → Set β}, s.PairwiseDisjoint f → t.Pairw
iseDisjoint g → (s ×ˢ t).PairwiseDisjoint fun i => f i.1 ×ˢ g i.2
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Set.PairwiseDisjoint.elim_set`：∀ {α : Type u_1} {ι : Type u_4} {s : Set 
ι} {f : ι → Set α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ 
f i, a ∈ f j → i = …
-/
theorem PairwiseDisjoint.prod {f : ι → Set α} {g : ι' → Set β} (hs : s.PairwiseDisjoint f)
    (ht : t.PairwiseDisjoint g) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint fun i => f i.1 ×ˢ g i.2 :=
  fun ⟨_, _⟩ ⟨hi, hi'⟩ ⟨_, _⟩ ⟨hj, hj'⟩ hij =>
  disjoint_left.2 fun ⟨_, _⟩ ⟨hai, hbi⟩ ⟨haj, hbj⟩ =>
    hij <| Prod.ext (hs.elim_set hi hj _ hai haj) <| ht.elim_set hi' hj' _ hbi hbj
/-
**Set.pairwiseDisjoint_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_pi {ι' α : ι -> Type*} {s : forall i, Set (ι' i)} {f : fo
rall i, ι' i -> Set (α i)} (hs : forall i, (s i).PairwiseDisjoint (f i)) : ((uni
v : Set ι).pi s).PairwiseDisjoint fun I => (univ : Set ι).pi fun i => f _ (I i)
参数：ι' i；α i；hs : forall i, (s i).PairwiseDisjoint (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.PairwiseDisjoint.elim_set`：∀ {α : Type u_1} {ι : Type u_4} {s : Set 
ι} {f : ι → Set α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ 
f i, a ∈ f j → i = …
· 使用定理 `trivial`：True
-/
theorem pairwiseDisjoint_pi {ι' α : ι → Type*} {s : ∀ i, Set (ι' i)} {f : ∀ i, ι' i → Set (α i)}
    (hs : ∀ i, (s i).PairwiseDisjoint (f i)) :
    ((univ : Set ι).pi s).PairwiseDisjoint fun I => (univ : Set ι).pi fun i => f _ (I i) :=
  fun _ hI _ hJ hIJ =>
  disjoint_left.2 fun a haI haJ =>
    hIJ <|
      funext fun i =>
        (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
/-
**Set.pairwiseDisjoint_image_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_image_right_iff {f : α -> β -> γ} {s : Set α} {t : Set β}
 (hf : forall a in s, Injective (f a)) : (s.PairwiseDisjoint fun a => f a '' t) 
↔ (s ×ˢ t).InjOn fun p => f p.1 p.2
参数：hf : forall a in s, Injective (f a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t

--- 原说明 ---
The partial images of a binary function `f` whose partial evaluations are inject
ive are pairwise
disjoint iff `f` is injective .
-/
theorem pairwiseDisjoint_image_right_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ a ∈ s, Injective (f a)) :
    (s.PairwiseDisjoint fun a => f a '' t) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine ⟨fun hs x hx y hy (h : f _ _ = _) => ?_, fun hs x hx y hy h => ?_⟩
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.2
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
/-
**Set.pairwiseDisjoint_image_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_image_left_iff {f : α -> β -> γ} {s : Set α} {t : Set β} 
(hf : forall b in t, Injective fun a => f a b) : (t.PairwiseDisjoint fun b => (f
un a => f a b) '' s) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2
参数：hf : forall b in t, Injective fun a => f a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t

--- 原说明 ---
The partial images of a binary function `f` whose partial evaluations are inject
ive are pairwise
disjoint iff `f` is injective .
-/
theorem pairwiseDisjoint_image_left_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ b ∈ t, Injective fun a => f a b) :
    (t.PairwiseDisjoint fun b => (fun a => f a b) '' s) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine ⟨fun ht x hx y hy (h : f _ _ = _) => ?_, fun ht x hx y hy h => ?_⟩
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.1
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)
/-
**Set.exists_ne_mem_inter_of_not_pairwiseDisjoint** 是 Mathlib 中的一个引理，位于命名空间 `Set
`。
形式化陈述：exists_ne_mem_inter_of_not_pairwiseDisjoint {f : ι -> Set α} (h : ¬ s.Pair
wiseDisjoint f) : exists i in s, exists j in s, i != j ∧ exists x : α, x in f i 
inter f j
参数：h : ¬ s.PairwiseDisjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.bot_eq_empty`：bot_eq_empty : (⊥ : Set α) = ∅
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
lemma exists_ne_mem_inter_of_not_pairwiseDisjoint
    {f : ι → Set α} (h : ¬ s.PairwiseDisjoint f) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ∃ x : α, x ∈ f i ∩ f j := by
  change ¬ ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → ∀ t, t ≤ f i → t ≤ f j → t ≤ ⊥ at h
  simp only [not_forall] at h
  obtain ⟨i, hi, j, hj, h_ne, t, hfi, hfj, ht⟩ := h
  replace ht : t.Nonempty := by
    rwa [le_bot_iff, bot_eq_empty, ← Ne, ← nonempty_iff_ne_empty] at ht
  obtain ⟨x, hx⟩ := ht
  exact ⟨i, hi, j, hj, h_ne, x, hfi hx, hfj hx⟩
/-
**Set.exists_lt_mem_inter_of_not_pairwiseDisjoint** 是 Mathlib 中的一个引理，位于命名空间 `Set
`。
形式化陈述：exists_lt_mem_inter_of_not_pairwiseDisjoint [LinearOrder ι] {f : ι -> Set 
α} (h : ¬ s.PairwiseDisjoint f) : exists i in s, exists j in s, i < j ∧ exists x
, x in f i inter f j
参数：h : ¬ s.PairwiseDisjoint f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_ne_mem_inter_of_not_pairwiseDisjoint`：exists_ne_mem_inter_of_
not_pairwiseDisjoint {f : ι -> Set α} (h : ¬ s.PairwiseDisjoint f) : exists i in
 s, exists j in s, i != j ∧ exists x …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
-/
lemma exists_lt_mem_inter_of_not_pairwiseDisjoint [LinearOrder ι]
    {f : ι → Set α} (h : ¬ s.PairwiseDisjoint f) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ ∃ x, x ∈ f i ∩ f j := by
  obtain ⟨i, hi, j, hj, hne, x, hx₁, hx₂⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  rcases lt_or_lt_iff_ne.mpr hne with h_lt | h_lt
  · exact ⟨i, hi, j, hj, h_lt, x, hx₁, hx₂⟩
  · exact ⟨j, hj, i, hi, h_lt, x, hx₂, hx₁⟩
/-
**Set.pairwiseDisjoint_singleton_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {s : Set ι} {f : ι → α}, (s.PairwiseDisjoi
nt fun i => {f i}) ↔ Set.InjOn f s
参数：s.PairwiseDisjoint fun i => {f i}。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma pairwiseDisjoint_singleton_iff_injOn {f : ι → α} :
    s.PairwiseDisjoint (fun i ↦ ({f i} : Set α)) ↔ s.InjOn f := by
  simp [PairwiseDisjoint, InjOn, Set.Pairwise, not_imp_not]

end Set

/-
**exists_ne_mem_inter_of_not_pairwise_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_ne_mem_inter_of_not_pairwise_disjoint {f : ι -> Set α} (h : ¬ Pairw
ise (Disjoint on f)) : exists i j : ι, i != j ∧ exists x, x in f i inter f j
参数：h : ¬ Pairwise (Disjoint on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_ne_mem_inter_of_not_pairwiseDisjoint`：exists_ne_mem_inter_of_
not_pairwiseDisjoint {f : ι -> Set α} (h : ¬ s.PairwiseDisjoint f) : exists i in
 s, exists j in s, i != j ∧ exists x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pairwise_univ`：pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise 
r
-/
lemma exists_ne_mem_inter_of_not_pairwise_disjoint
    {f : ι → Set α} (h : ¬ Pairwise (Disjoint on f)) :
    ∃ i j : ι, i ≠ j ∧ ∃ x, x ∈ f i ∩ f j := by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩
/-
**exists_lt_mem_inter_of_not_pairwise_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_lt_mem_inter_of_not_pairwise_disjoint [LinearOrder ι] {f : ι -> Set
 α} (h : ¬ Pairwise (Disjoint on f)) : exists i j : ι, i < j ∧ exists x, x in f 
i inter f j
参数：h : ¬ Pairwise (Disjoint on f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_lt_mem_inter_of_not_pairwiseDisjoint`：exists_lt_mem_inter_of_
not_pairwiseDisjoint [LinearOrder ι] {f : ι -> Set α} (h : ¬ s.PairwiseDisjoint 
f) : exists i in s, exists j in s, i …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pairwise_univ`：pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise 
r
-/
lemma exists_lt_mem_inter_of_not_pairwise_disjoint [LinearOrder ι]
    {f : ι → Set α} (h : ¬ Pairwise (Disjoint on f)) :
    ∃ i j : ι, i < j ∧ ∃ x, x ∈ f i ∩ f j := by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_lt_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩
/-
**pairwise_disjoint_fiber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_disjoint_fiber (f : ι -> α) : Pairwise (Disjoint on fun a : α => 
f ⁻¹' {a})
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.pairwise_univ`：pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise 
r
· 使用定理 `Set.pairwiseDisjoint_fiber`：pairwiseDisjoint_fiber (f : ι -> α) (s : Set
 α) : s.PairwiseDisjoint fun a => f ⁻¹' {a}
-/
theorem pairwise_disjoint_fiber (f : ι → α) : Pairwise (Disjoint on fun a : α => f ⁻¹' {a}) :=
  pairwise_univ.1 <| Set.pairwiseDisjoint_fiber f univ
/-
**subsingleton_setOfPred_mem_iff_pairwise_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subsingleton_setOfPred_mem_iff_pairwise_disjoint {f : ι -> Set α} : (foral
l a, {i | a in f i}.Subsingleton) ↔ Pairwise (Disjoint on f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma subsingleton_setOfPred_mem_iff_pairwise_disjoint {f : ι → Set α} :
    (∀ a, {i | a ∈ f i}.Subsingleton) ↔ Pairwise (Disjoint on f) :=
  ⟨fun h _ _ hij ↦ disjoint_left.2 fun a hi hj ↦ hij (h a hi hj),
   fun h _ _ hx _ hy ↦ by_contra fun hne ↦ disjoint_left.1 (h hne) hx hy⟩

@[deprecated (since := "2026-07-09")]
alias subsingleton_setOf_mem_iff_pairwise_disjoint :=
  subsingleton_setOfPred_mem_iff_pairwise_disjoint

/-- Simp normal form of `pairwise_ne_iff_injective`. -/
/-
**pairwise_not_eq_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {f : ι → α}, (Pairwise fun i j => ¬f i = f
 j) ↔ Function.Injective f
参数：Pairwise fun i j => ¬f i = f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Simp normal form of `pairwise_ne_iff_injective`.
-/
@[simp] lemma pairwise_not_eq_iff_injective {f : ι → α} :
    Pairwise (fun i j ↦ ¬ f i = f j) ↔ f.Injective := by
  simp [Pairwise, Function.Injective, not_imp_not]
/-
**pairwise_ne_iff_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pairwise_ne_iff_injective {f : ι -> α} : Pairwise (fun i j => f i != f j) 
↔ f.Injective
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
lemma pairwise_ne_iff_injective {f : ι → α} : Pairwise (fun i j ↦ f i ≠ f j) ↔ f.Injective := by
  simp
