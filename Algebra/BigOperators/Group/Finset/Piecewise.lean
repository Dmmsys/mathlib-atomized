/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Piecewise

/-!
# Interaction of big operators with piecewise functions

This file proves lemmas on the sum and product of piecewise functions, including `ite` and `dite`.
-/

public section

variable {ι κ M β γ : Type*} {s : Finset ι}

namespace Finset

section CommMonoid

variable [CommMonoid M]

@[to_additive]
/-
**Finset.prod_apply_dite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_apply_dite {p : ι -> Prop} [DecidablePred p] [DecidablePred fun x => 
¬p x] (f : forall x : ι, p x -> γ) (g : forall x : ι, ¬p x -> γ) (h : γ -> M) : 
(∏ x in s, h (if hx : p x then f x hx else g x hx)) = (∏ x : {x in s | p x}, h (
f x.1 <| by simpa using (mem_filter.mp x.2).2)) * ∏ x : {x in s | ¬p x}, h (g x.
1 <| by simpa using (mem_filter.mp x.2).2)
参数：f : forall x : ι, p x -> γ；g : forall x : ι, ¬p x -> γ；h : γ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_not 
(s : Finset ι) (p : ι -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] (f
 : ι -> M) : (∏ x in s with …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem prod_apply_dite {p : ι → Prop} [DecidablePred p]
    [DecidablePred fun x => ¬p x] (f : ∀ x : ι, p x → γ) (g : ∀ x : ι, ¬p x → γ) (h : γ → M) :
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
  calc
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x ∈ s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x ∈ s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x ∈ s | p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x : {x ∈ s | ¬p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ (prod_attach _ _).symm (prod_attach _ _).symm
    _ = (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
          ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x _hx ↦
        congr_arg h (dif_pos <| by simpa using (mem_filter.mp x.2).2))
        (prod_congr rfl fun x _hx => congr_arg h (dif_neg <| by simpa using (mem_filter.mp x.2).2))

@[to_additive]
/-
**Finset.prod_apply_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_apply_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f g : ι -
> γ) (h : γ -> M) : (∏ x in s, h (if p x then f x else g x)) = (∏ x in s with p 
x, h (f x)) * ∏ x in s with ¬p x, h (g x)
参数：f g : ι -> γ；h : γ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_apply_dite`：prod_apply_dite {p : ι -> Prop} [DecidablePred p
] [DecidablePred fun x => ¬p x] (f : forall x : ι, p x -> γ) (g : forall x : ι, 
¬p x -> γ) (…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
theorem prod_apply_ite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f g : ι → γ)
    (h : γ → M) :
    (∏ x ∈ s, h (if p x then f x else g x)) =
      (∏ x ∈ s with p x, h (f x)) * ∏ x ∈ s with ¬p x, h (g x) :=
  (prod_apply_dite _ _ _).trans <| congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

@[to_additive]
/-
**Finset.prod_dite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_dite {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f : forall x :
 ι, p x -> M) (g : forall x : ι, ¬p x -> M) : ∏ x in s, (if hx : p x then f x hx
 else g x hx) = (∏ x : {x in s | p x}, f x.1 (by simpa using (mem_filter.mp x.2)
.2)) * ∏ x : {x in s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2)
参数：f : forall x : ι, p x -> M；g : forall x : ι, ¬p x -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply_dite`：prod_apply_dite {p : ι -> Prop} [DecidablePred p
] [DecidablePred fun x => ¬p x] (f : forall x : ι, p x -> γ) (g : forall x : ι, 
¬p x -> γ) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_dite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f : ∀ x : ι, p x → M)
    (g : ∀ x : ι, ¬p x → M) :
    ∏ x ∈ s, (if hx : p x then f x hx else g x hx) =
      (∏ x : {x ∈ s | p x}, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
/-
**Finset.prod_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f g : ι -> M) :
 ∏ x in s, (if p x then f x else g x) = (∏ x in s with p x, f x) * ∏ x in s with
 ¬p x, g x
参数：f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply_ite`：prod_apply_ite {s : Finset ι} {p : ι -> Prop} [De
cidablePred p] (f g : ι -> γ) (h : γ -> M) : (∏ x in s, h (if p x then f x else 
g x)) = (∏ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_ite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
/-
**Finset.prod_dite_of_false** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_dite_of_false {p : ι -> Prop} [DecidablePred p] (h : forall i in s, ¬
 p i) (f : forall i, p i -> M) (g : forall i, ¬ p i -> M) : ∏ i in s, (if hi : p
 i then f i hi else g i hi) = ∏ i : s, g i.1 (h _ i.2)
参数：h : forall i in s, ¬ p i；f : forall i, p i -> M；g : forall i, ¬ p i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij'`：prod_bij' (i : forall a in s, κ) (j : forall a in t, ι
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
lemma prod_dite_of_false {p : ι → Prop} [DecidablePred p] (h : ∀ i ∈ s, ¬ p i)
    (f : ∀ i, p i → M) (g : ∀ i, ¬ p i → M) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, g i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]
/-
**Finset.prod_ite_of_false** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_ite_of_false {p : ι -> Prop} [DecidablePred p] (h : forall x in s, ¬p
 x) (f g : ι -> M) : ∏ x in s, (if p x then f x else g x) = ∏ x in s, g x
参数：h : forall x in s, ¬p x；f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_dite_of_false`：prod_dite_of_false {p : ι -> Prop} [Decidable
Pred p] (h : forall i in s, ¬ p i) (f : forall i, p i -> M) (g : forall i, ¬ p i
 -> M) : ∏ i in…
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
lemma prod_ite_of_false {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, ¬p x) (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, g x :=
  (prod_dite_of_false h _ _).trans (prod_attach _ _)

@[to_additive]
/-
**Finset.prod_dite_of_true** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_dite_of_true {p : ι -> Prop} [DecidablePred p] (h : forall i in s, p 
i) (f : forall i, p i -> M) (g : forall i, ¬ p i -> M) : ∏ i in s, (if hi : p i 
then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2)
参数：h : forall i in s, p i；f : forall i, p i -> M；g : forall i, ¬ p i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij'`：prod_bij' (i : forall a in s, κ) (j : forall a in t, ι
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma prod_dite_of_true {p : ι → Prop} [DecidablePred p] (h : ∀ i ∈ s, p i) (f : ∀ i, p i → M)
    (g : ∀ i, ¬ p i → M) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> grind

@[to_additive]
/-
**Finset.prod_ite_of_true** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_ite_of_true {p : ι -> Prop} [DecidablePred p] (h : forall x in s, p x
) (f g : ι -> M) : ∏ x in s, (if p x then f x else g x) = ∏ x in s, f x
参数：h : forall x in s, p x；f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_dite_of_true`：prod_dite_of_true {p : ι -> Prop} [DecidablePr
ed p] (h : forall i in s, p i) (f : forall i, p i -> M) (g : forall i, ¬ p i -> 
M) : ∏ i in s,…
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
lemma prod_ite_of_true {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, f x :=
  (prod_dite_of_true h _ _).trans (prod_attach _ _)

@[to_additive]
/-
**Finset.prod_apply_ite_of_false** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_apply_ite_of_false {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ) (
k : γ -> M) (h : forall x in s, ¬p x) : (∏ x in s, k (if p x then f x else g x))
 = ∏ x in s, k (g x)
参数：f g : ι -> γ；k : γ -> M；h : forall x in s, ¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用引理 `Finset.prod_ite_of_false`：prod_ite_of_false {p : ι -> Prop} [DecidablePr
ed p] (h : forall x in s, ¬p x) (f g : ι -> M) : ∏ x in s, (if p x then f x else
 g x) = ∏ x in…
-/
theorem prod_apply_ite_of_false {p : ι → Prop} [DecidablePred p] (f g : ι → γ) (k : γ → M)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_false h _ _

@[to_additive]
/-
**Finset.prod_apply_ite_of_true** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_apply_ite_of_true {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ) (k
 : γ -> M) (h : forall x in s, p x) : (∏ x in s, k (if p x then f x else g x)) =
 ∏ x in s, k (f x)
参数：f g : ι -> γ；k : γ -> M；h : forall x in s, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用引理 `Finset.prod_ite_of_true`：prod_ite_of_true {p : ι -> Prop} [DecidablePred
 p] (h : forall x in s, p x) (f g : ι -> M) : ∏ x in s, (if p x then f x else g 
x) = ∏ x in s…
-/
theorem prod_apply_ite_of_true {p : ι → Prop} [DecidablePred p] (f g : ι → γ) (k : γ → M)
    (h : ∀ x ∈ s, p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (f x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_true h _ _

@[to_additive (attr := simp)]
/-
**Finset.prod_ite_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : ι -> M) : ∏ i in s, (if
 i in t then f i else 1) = ∏ i in s inter t, f i
参数：s t : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_filter`：prod_filter (p : ι -> Prop) [DecidablePred p] (f : ι
 -> M) : ∏ a in s with p a, f a = ∏ a in s, if p a then f a else 1
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
-/
theorem prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]

@[to_additive]
/-
**Finset.prod_attach_eq_prod_dite** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_attach_eq_prod_dite [Fintype ι] (s : Finset ι) (f : s -> M) [Decidabl
ePred (· in s)] : ∏ i in s.attach, f i = ∏ i, if h : i in s then f ⟨i, h⟩ else 1
参数：s : Finset ι；f : s -> M；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_dite`：prod_dite {s : Finset ι} {p : ι -> Prop} [DecidablePre
d p] (f : forall x : ι, p x -> M) (g : forall x : ι, ¬p x -> M) : ∏ x in s, (if 
hx : p…
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_mem_eq_of_subset`：∀ {α : Type u_1} {s t : Finset α} [inst 
: DecidablePred fun x => x ∈ s], s ⊆ t → {x ∈ t | x ∈ s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
lemma prod_attach_eq_prod_dite [Fintype ι] (s : Finset ι) (f : s → M) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite, Finset.univ_eq_attach, Finset.prod_const_one, mul_one]
  congr
  · simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

@[to_additive (attr := simp)]
/-
**Finset.prod_dite_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_dite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : forall x : ι, a =
 x -> M) : ∏ x in s, (if h : a = x then b x h else 1) = ite (a in s) (b a rfl) 1
参数：s : Finset ι；a : ι；b : forall x : ι, a = x -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
-/
theorem prod_dite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ∀ x : ι, a = x → M) :
    ∏ x ∈ s, (if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]
/-
**Finset.prod_dite_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : forall x : ι, x 
= a -> M) : ∏ x in s, (if h : x = a then b x h else 1) = ite (a in s) (b a rfl) 
1
参数：s : Finset ι；a : ι；b : forall x : ι, x = a -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
-/
theorem prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ∀ x : ι, x = a → M) :
    ∏ x ∈ s, (if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]
/-
**Finset.prod_ite_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) : (∏ x in 
s, ite (a = x) (b x) 1) = ite (a in s) (b a) 1
参数：s : Finset ι；a : ι；b : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dite_eq`：prod_dite_eq [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : forall x : ι, a = x -> M) : ∏ x in s, (if h : a = x then b x h else 1) = i
te (a in …
-/
theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `Finset.prod_ite_eq` is that the arguments to `Eq` are swapped. -/
@[to_additive (attr := simp) /-- A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped. -/]
/-
**Finset.prod_ite_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) : (∏ x in
 s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
参数：s : Finset ι；a : ι；b : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dite_eq'`：prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : 
ι) (b : forall x : ι, x = a -> M) : ∏ x in s, (if h : x = a then b x h else 1) =
 ite (a in…
-/
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
/-
**Finset.prod_ite_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_eq_of_mem [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h 
: a in s) : (∏ x in s, if a = x then b x else 1) = b a
参数：s : Finset ι；a : ι；b : ι -> M；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_eq`：prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (
b : ι -> M) : (∏ x in s, ite (a = x) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_ite_eq_of_mem [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  simp only [prod_ite_eq, if_pos h]

/-- The difference with `Finset.prod_ite_eq_of_mem` is that the arguments to `Eq` are swapped. -/
@[to_additive]
/-
**Finset.prod_ite_eq_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_eq_of_mem' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h
 : a in s) : (∏ x in s, if x = a then b x else 1) = b a
参数：s : Finset ι；a : ι；b : ι -> M；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The difference with `Finset.prod_ite_eq_of_mem` is that the arguments to `Eq` ar
e swapped.
-/
theorem prod_ite_eq_of_mem' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if x = a then b x else 1) = b a := by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]
/-
**Finset.prod_pi_mulSingle'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_pi_mulSingle' [DecidableEq ι] (a : ι) (x : M) (s : Finset ι) : ∏ a' i
n s, Pi.mulSingle a x a' = if a in s then x else 1
参数：a : ι；x : M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dite_eq'`：prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : 
ι) (b : forall x : ι, x = a -> M) : ∏ x in s, (if h : x = a then b x h else 1) =
 ite (a in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_pi_mulSingle' [DecidableEq ι] (a : ι) (x : M) (s : Finset ι) :
    ∏ a' ∈ s, Pi.mulSingle a x a' = if a ∈ s then x else 1 :=
  prod_dite_eq' _ _ _

@[to_additive (attr := simp)]
/-
**Finset.prod_pi_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_pi_mulSingle {M : ι -> Type*} [DecidableEq ι] [forall a, CommMonoid (
M a)] (a : ι) (f : forall a, M a) (s : Finset ι) : (∏ a' in s, Pi.mulSingle a' (
f a') a) = if a in s then f a else 1
参数：M a；a : ι；f : forall a, M a；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dite_eq`：prod_dite_eq [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : forall x : ι, a = x -> M) : ∏ x in s, (if h : a = x then b x h else 1) = i
te (a in …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_pi_mulSingle {M : ι → Type*} [DecidableEq ι] [∀ a, CommMonoid (M a)] (a : ι)
    (f : ∀ a, M a) (s : Finset ι) :
    (∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1 :=
  prod_dite_eq _ _ _

@[to_additive]
/-
**Finset.prod_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_piecewise [DecidableEq ι] (s t : Finset ι) (f g : ι -> M) : (∏ x in s
, (t.piecewise f g) x) = (∏ x in s inter t, f x) * ∏ x in s \ t, g x
参数：s t : Finset ι；f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite`：prod_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred 
p] (f g : ι -> M) : ∏ x in s, (if p x then f x else g x) = (∏ x in s with p x, f
 x) *…
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_eq_filter`：sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s
₁.filter (· ∉ s₂)
-/
theorem prod_piecewise [DecidableEq ι] (s t : Finset ι) (f g : ι → M) :
    (∏ x ∈ s, (t.piecewise f g) x) = (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, g x := by
  simp only [piecewise]
  rw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

@[to_additive]
/-
**Finset.prod_inter_mul_prod_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_inter_mul_prod_sdiff [DecidableEq ι] (s t : Finset ι) (f : ι -> M) : 
(∏ x in s inter t, f x) * ∏ x in s \ t, f x = ∏ x in s, f x
参数：s t : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_piecewise`：prod_piecewise [DecidableEq ι] (s t : Finset ι) (
f g : ι -> M) : (∏ x in s, (t.piecewise f g) x) = (∏ x in s inter t, f x) * ∏ x 
in s \ t, g…
-/
theorem prod_inter_mul_prod_sdiff [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by
  convert! (s.prod_piecewise t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

@[deprecated (since := "2026-06-03")] alias prod_inter_mul_prod_diff := prod_inter_mul_prod_sdiff

@[to_additive]
/-
**Finset.prod_eq_mul_prod_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_mul_prod_sdiff_singleton [DecidableEq ι] {s : Finset ι} (i : ι) (f
 : ι -> M) (h : i ∉ s -> f i = 1) : ∏ x in s, f x = f i * ∏ x in s \ {i}, f x
参数：i : ι；f : ι -> M；h : i ∉ s -> f i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.inter_singleton_of_mem`：inter_singleton_of_mem {a : α} {s : Finse
t α} (h : a in s) : s inter {a} = {a}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_inter_mul_prod_sdiff`：prod_inter_mul_prod_sdiff [DecidableEq
 ι] (s t : Finset ι) (f : ι -> M) : (∏ x in s inter t, f x) * ∏ x in s \ t, f x 
= ∏ x in s, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
theorem prod_eq_mul_prod_sdiff_singleton [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι → M)
    (h : i ∉ s → f i = 1) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  by_cases hs : i ∈ s
  · convert! (s.prod_inter_mul_prod_sdiff { i } f).symm
    simp [hs]
  · simp_all only [not_false_eq_true, forall_const, one_mul]
    apply Finset.prod_congr <;> aesop

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton := prod_eq_mul_prod_sdiff_singleton

@[to_additive]
/-
**Finset.prod_eq_mul_prod_sdiff_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：prod_eq_mul_prod_sdiff_singleton_of_mem [DecidableEq ι] {s : Finset ι} {i 
: ι} (h : i in s) (f : ι -> M) : ∏ x in s, f x = f i * ∏ x in s \ {i}, f x
参数：h : i in s；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton`：prod_eq_mul_prod_sdiff_singleto
n [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι -> M) (h : i ∉ s -> f i = 1) : ∏
 x in s, f x = f i * ∏ x in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem prod_eq_mul_prod_sdiff_singleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x :=
  prod_eq_mul_prod_sdiff_singleton _ _ (by simp_all)

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton_of_mem := prod_eq_mul_prod_sdiff_singleton_of_mem

@[to_additive]
/-
**Finset.prod_eq_prod_sdiff_singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_prod_sdiff_singleton_mul [DecidableEq ι] {s : Finset ι} {i : ι} (h
 : i in s) (f : ι -> M) : ∏ x in s, f x = (∏ x in s \ {i}, f x) * f i
参数：h : i in s；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem prod_eq_prod_sdiff_singleton_mul [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem h, mul_comm]

@[deprecated (since := "2026-06-03")]
alias prod_eq_prod_diff_singleton_mul := prod_eq_prod_sdiff_singleton_mul

@[to_additive]
/-
**Finset._root_.Fintype.prod_eq_mul_prod_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq ι] [Fintype ι] (a : ι) (f : ι → M) :
    ∏ i, f i = f a * ∏ i ∈ {a}ᶜ, f i :=
  prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ a) f

@[to_additive]
/-
**Finset._root_.Fintype.prod_eq_prod_compl_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq ι] [Fintype ι] (a : ι) (f : ι → M) :
    ∏ i, f i = (∏ i ∈ {a}ᶜ, f i) * f a :=
  prod_eq_prod_sdiff_singleton_mul (mem_univ a) f
/-
**Finset.dvd_prod_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset ι} (ha : a in s) : f a ∣ 
∏ i in s, f i
参数：f : ι -> M；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_prod_of_mem (f : ι → M) {a : ι} {s : Finset ι} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem ha]
    exact dvd_mul_right _ _

@[to_additive]
/-
**Finset.prod_update_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_update_of_notMem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∉ s) (
f : ι -> M) (b : M) : ∏ x in s, Function.update f i b x = ∏ x in s, f x
参数：h : i ∉ s；f : ι -> M；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_update_of_notMem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∉ s) (f : ι → M)
    (b : M) : ∏ x ∈ s, Function.update f i b x = ∏ x ∈ s, f x := by
  apply prod_congr rfl
  intro j hj
  have : j ≠ i := by
    rintro rfl
    exact h hj
  simp [this]

@[to_additive]
/-
**Finset.prod_update_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_update_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f 
: ι -> M) (b : M) : ∏ x in s, Function.update f i b x = b * ∏ x in s \ singleton
 i, f x
参数：h : i in s；f : ι -> M；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.update_eq_piecewise`：update_eq_piecewise {β : Type*} [DecidableEq
 ι] (f : ι -> β) (i : ι) (v : β) : update f i v = piecewise (singleton i) (fun _
 => v) f
· 使用定理 `Finset.prod_piecewise`：prod_piecewise [DecidableEq ι] (s t : Finset ι) (
f g : ι -> M) : (∏ x in s, (t.piecewise f g) x) = (∏ x in s inter t, f x) * ∏ x 
in s \ t, g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.inter_singleton_of_mem`：inter_singleton_of_mem {a : α} {s : Finse
t α} (h : a in s) : s inter {a} = {a}
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_update_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s) (f : ι → M) (b : M) :
    ∏ x ∈ s, Function.update f i b x = b * ∏ x ∈ s \ singleton i, f x := by
  rw [update_eq_piecewise, prod_piecewise]
  simp [h]

/-- See also `Finset.prod_ite_zero`. -/
@[to_additive /-- See also `Finset.sum_boole`. -/]
/-
**Finset.prod_ite_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_one (s : Finset ι) (p : ι -> Prop) [DecidablePred p] (h : forall 
i in s, forall j in s, p i -> p j -> i = j) (a : M) : ∏ i in s, ite (p i) a 1 = 
ite (exists i in s, p i) a 1
参数：s : Finset ι；p : ι -> Prop；h : forall i in s, forall j in s, p i -> p j -> i 
= j；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_eq_single_of_mem`：prod_eq_single_of_mem {s : Finset ι} {f : 
ι -> M} (a : ι) (h : a in s) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s,
 f x = f a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)

--- 原说明 ---
See also `Finset.prod_ite_zero`.
-/
theorem prod_ite_one (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : M) :
    ∏ i ∈ s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hpi]
    exact fun j hj hji ↦ if_neg fun hpj ↦ hji <| h _ hj _ hi hpj hpi
  · push Not at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive sum_boole_nsmul]
/-
**Finset.prod_pow_boole** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_pow_boole [DecidableEq ι] (s : Finset ι) (f : ι -> M) (a : ι) : (∏ x 
in s, f x ^ ite (a = x) 1 0) = ite (a in s) (f a) 1
参数：s : Finset ι；f : ι -> M；a : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `pow_ite`：pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) : a ^ (if p 
then b else c) = if p then a ^ b else a ^ c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_ite_eq`：prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (
b : ι -> M) : (∏ x in s, ite (a = x) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_pow_boole [DecidableEq ι] (s : Finset ι) (f : ι → M) (a : ι) :
    (∏ x ∈ s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp

@[to_additive]
/-
**Finset.prod_eq_prod_iff_single** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_eq_prod_iff_single [IsRightCancelMul M] {f g : ι -> M} {i : ι} (hi : 
i in s) (hfg : forall j in s, j != i -> f j = g j) : ∏ j in s, f j = ∏ j in s, g
 j ↔ f i = g i
参数：hi : i in s；hfg : forall j in s, j != i -> f j = g j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prod_eq_prod_iff_single [IsRightCancelMul M] {f g : ι → M} {i : ι} (hi : i ∈ s)
    (hfg : ∀ j ∈ s, j ≠ i → f j = g j) : ∏ j ∈ s, f j = ∏ j ∈ s, g j ↔ f i = g i := by
  classical
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi, prod_eq_mul_prod_sdiff_singleton_of_mem hi,
    prod_congr rfl (by simpa), mul_left_inj]

end CommMonoid

/-
**Finset.card_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_filter (p) [DecidablePred p] (s : Finset ι) : #{i in s | p i} = ∑ i i
n s, ite (p i) 1 0
参数：p；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_filter (p) [DecidablePred p] (s : Finset ι) :
    #{i ∈ s | p i} = ∑ i ∈ s, ite (p i) 1 0 := by simp [sum_ite]

end Finset

namespace Fintype

open Finset

variable [CommMonoid M] [Fintype ι]

@[to_additive]
/-
**Fintype.prod_ite_eq_ite_exists** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_ite_eq_ite_exists (p : ι -> Prop) [DecidablePred p] (h : forall i j, 
p i -> p j -> i = j) (a : M) : ∏ i, ite (p i) a 1 = ite (exists i, p i) a 1
参数：p : ι -> Prop；h : forall i j, p i -> p j -> i = j；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_one`：prod_ite_one (s : Finset ι) (p : ι -> Prop) [Decida
blePred p] (h : forall i in s, forall j in s, p i -> p j -> i = j) (a : M) : ∏ i
 in s, it…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : M) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [prod_ite_one univ p (by simpa using h)]

variable [DecidableEq ι]

@[to_additive]
/-
**Fintype.prod_ite_mem** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_ite_mem (s : Finset ι) (f : ι -> M) : ∏ i, (if i in s then f i else 1
) = ∏ i in s, f i
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_mem`：prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : 
ι -> M) : ∏ i in s, (if i in t then f i else 1) = ∏ i in s inter t, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_ite_mem (s : Finset ι) (f : ι → M) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  simp

/-- See also `Finset.prod_dite_eq`. -/
@[to_additive /-- See also `Finset.sum_dite_eq`. -/]
/-
**Fintype.prod_dite_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_dite_eq (i : ι) (f : forall j, i = j -> M) : ∏ j, (if h : i = j then 
f j h else 1) = f i rfl
参数：i : ι；f : forall j, i = j -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_dite_eq`：prod_dite_eq [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : forall x : ι, a = x -> M) : ∏ x in s, (if h : a = x then b x h else 1) = i
te (a in …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
See also `Finset.prod_dite_eq`.
-/
lemma prod_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_dite_eq'`. -/
@[to_additive /-- See also `Finset.sum_dite_eq'`. -/]
/-
**Fintype.prod_dite_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_dite_eq' (i : ι) (f : forall j, j = i -> M) : ∏ j, (if h : j = i then
 f j h else 1) = f i rfl
参数：i : ι；f : forall j, j = i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_dite_eq'`：prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : 
ι) (b : forall x : ι, x = a -> M) : ∏ x in s, (if h : x = a then b x h else 1) =
 ite (a in…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
See also `Finset.prod_dite_eq'`.
-/
lemma prod_dite_eq' (i : ι) (f : ∀ j, j = i → M) :
    ∏ j, (if h : j = i then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq`. -/
@[to_additive /-- See also `Finset.sum_ite_eq`. -/]
/-
**Fintype.prod_ite_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_ite_eq (i : ι) (f : ι -> M) : ∏ j, (if i = j then f j else 1) = f i
参数：i : ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_eq`：prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (
b : ι -> M) : (∏ x in s, ite (a = x) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
See also `Finset.prod_ite_eq`.
-/
lemma prod_ite_eq (i : ι) (f : ι → M) : ∏ j, (if i = j then f j else 1) = f i := by
  rw [Finset.prod_ite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq'`. -/
@[to_additive /-- See also `Finset.sum_ite_eq'`. -/]
/-
**Fintype.prod_ite_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_ite_eq' (i : ι) (f : ι -> M) : ∏ j, (if j = i then f j else 1) = f i
参数：i : ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
See also `Finset.prod_ite_eq'`.
-/
lemma prod_ite_eq' (i : ι) (f : ι → M) : ∏ j, (if j = i then f j else 1) = f i := by
  rw [Finset.prod_ite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_pi_mulSingle`. -/
@[to_additive /-- See also `Finset.sum_pi_single`. -/]
/-
**Fintype.prod_pi_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_pi_mulSingle {M : ι -> Type*} [forall i, CommMonoid (M i)] (i : ι) (f
 : forall i, M i) : ∏ j, Pi.mulSingle j (f j) i = f i
参数：M i；i : ι；f : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.prod_dite_eq`：prod_dite_eq (i : ι) (f : forall j, i = j -> M) : 
∏ j, (if h : i = j then f j h else 1) = f i rfl
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
See also `Finset.prod_pi_mulSingle`.
-/
lemma prod_pi_mulSingle {M : ι → Type*} [∀ i, CommMonoid (M i)] (i : ι) (f : ∀ i, M i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := prod_dite_eq _ _

/-- See also `Finset.prod_pi_mulSingle'`. -/
@[to_additive /-- See also `Finset.sum_pi_single'`. -/]
/-
**Fintype.prod_pi_mulSingle'** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_pi_mulSingle' (i : ι) (a : M) : ∏ j, Pi.mulSingle i a j = a
参数：i : ι；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.prod_dite_eq'`：prod_dite_eq' (i : ι) (f : forall j, j = i -> M) 
: ∏ j, (if h : j = i then f j h else 1) = f i rfl
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
See also `Finset.prod_pi_mulSingle'`.
-/
lemma prod_pi_mulSingle' (i : ι) (a : M) : ∏ j, Pi.mulSingle i a j = a := prod_dite_eq' _ _

end Fintype

