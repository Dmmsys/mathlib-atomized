/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Set.Card

/-!
# Representation of components by a set of vertices

## Main definition

* `SimpleGraph.ConnectedComponent.Represents` says that a set of vertices represents a set of
  components if it contains exactly one vertex from each component.
-/

@[expose] public section

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

namespace SimpleGraph.ConnectedComponent

/-- A set of vertices represents a set of components if it contains exactly one vertex from
each component. -/
/-
**SimpleGraph.ConnectedComponent.Represents** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGra
ph.ConnectedComponent`。
形式化陈述：Represents (s : Set V) (C : Set G.ConnectedComponent) : Prop
参数：s : Set V；C : Set G.ConnectedComponent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of vertices represents a set of components if it contains exactly one vert
ex from
each component.
-/
def Represents (s : Set V) (C : Set G.ConnectedComponent) : Prop :=
  Set.BijOn G.connectedComponentMk s C

namespace Represents

variable {C : Set G.ConnectedComponent} {s : Set V} {c : G.ConnectedComponent}

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.ConnectedComponent.Represents.image_out** 是 Mathlib 中的一个引理，位于命名空间 
`SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：image_out (C : Set G.ConnectedComponent) : Represents (Quot.out '' C) C
参数：C : Set G.ConnectedComponent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mk`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f
 : α → β},   Set.MapsTo f s t → Set.InjOn f s → Set.SurjOn f s t → Set.BijOn f s
 t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma image_out (C : Set G.ConnectedComponent) :
    Represents (Quot.out '' C) C :=
  Set.BijOn.mk (by rintro c ⟨x, ⟨hx, rfl⟩⟩; simp_all [connectedComponentMk]) (by
    rintro x ⟨c, ⟨hc, rfl⟩⟩ y ⟨d, ⟨hd, rfl⟩⟩ hxy
    simp only [connectedComponentMk] at hxy
    aesop) (fun _ _ ↦ by simpa [connectedComponentMk])
/-
**SimpleGraph.ConnectedComponent.Represents.existsUnique_rep** 是 Mathlib 中的一个引理，
位于命名空间 `SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：existsUnique_rep (hrep : Represents s C) (h : c in C) : exists! x, x in s 
inter c.supp
参数：hrep : Represents s C；h : c in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma existsUnique_rep (hrep : Represents s C) (h : c ∈ C) : ∃! x, x ∈ s ∩ c.supp := by
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hrep.2.2 h
  use x
  simp only [Set.mem_inter_iff, hx, mem_supp_iff, and_self, and_imp, true_and]
  exact fun y hy hyx ↦ hrep.2.1 hy hx hyx
/-
**SimpleGraph.ConnectedComponent.Represents.exists_inter_eq_singleton** 是 Mathli
b 中的一个引理，位于命名空间 `SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：exists_inter_eq_singleton (hrep : Represents s C) (h : c in C) : exists x,
 s inter c.supp = {x}
参数：hrep : Represents s C；h : c in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ConnectedComponent.Represents.existsUnique_rep`：existsUnique
_rep (hrep : Represents s C) (h : c in C) : exists! x, x in s inter c.supp
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_inter_eq_singleton (hrep : Represents s C) (h : c ∈ C) : ∃ x, s ∩ c.supp = {x} := by
  obtain ⟨a, ha⟩ := existsUnique_rep hrep h
  aesop
/-
**SimpleGraph.ConnectedComponent.Represents.disjoint_supp_of_notMem** 是 Mathlib 
中的一个引理，位于命名空间 `SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：disjoint_supp_of_notMem (hrep : Represents s C) (h : c ∉ C) : Disjoint s c
.supp
参数：hrep : Represents s C；h : c ∉ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma disjoint_supp_of_notMem (hrep : Represents s C) (h : c ∉ C) : Disjoint s c.supp := by
  rw [Set.disjoint_left]
  intro a ha hc
  simp only [mem_supp_iff] at hc
  subst hc
  exact h (hrep.1 ha)
/-
**SimpleGraph.ConnectedComponent.Represents.ncard_inter** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：ncard_inter (hrep : Represents s C) (h : c in C) : (s inter c.supp).ncard 
= 1
参数：hrep : Represents s C；h : c in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_one`：∀ {α : Type u_1} {s : Set α}, s.ncard = 1 ↔ ∃ a, s = {
a}
· 使用引理 `SimpleGraph.ConnectedComponent.Represents.exists_inter_eq_singleton`：exi
sts_inter_eq_singleton (hrep : Represents s C) (h : c in C) : exists x, s inter 
c.supp = {x}
-/
lemma ncard_inter (hrep : Represents s C) (h : c ∈ C) : (s ∩ c.supp).ncard = 1 := by
  rw [Set.ncard_eq_one]
  exact exists_inter_eq_singleton hrep h
/-
**SimpleGraph.ConnectedComponent.Represents.ncard_eq** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：ncard_eq (hrep : Represents s C) : s.ncard = C.ncard
参数：hrep : Represents s C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.ncard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → (f '' s).ncard = s.ncard
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
-/
lemma ncard_eq (hrep : Represents s C) : s.ncard = C.ncard :=
  hrep.image_eq ▸ hrep.injOn.ncard_image.symm
/-
**SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_mem** 是 Mathlib 中的一个引
理，位于命名空间 `SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：ncard_sdiff_of_mem (hrep : Represents s C) (h : c in C) : (c.supp \ s).nca
rd = c.supp.ncard - 1
参数：hrep : Represents s C；h : c in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ConnectedComponent.Represents.exists_inter_eq_singleton`：exi
sts_inter_eq_singleton (hrep : Represents s C) (h : c in C) : exists x, s inter 
c.supp = {x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.ncard_sdiff`：ncard_sdiff (hst : s subseteq t) (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
-/
lemma ncard_sdiff_of_mem (hrep : Represents s C) (h : c ∈ C) :
    (c.supp \ s).ncard = c.supp.ncard - 1 := by
  obtain ⟨a, ha⟩ := exists_inter_eq_singleton hrep h
  rw [← Set.sdiff_inter_self_eq_sdiff, ha, Set.ncard_sdiff, Set.ncard_singleton]
  simp [← ha]
/-
**SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_notMem** 是 Mathlib 中的
一个引理，位于命名空间 `SimpleGraph.ConnectedComponent.Represents`。
形式化陈述：ncard_sdiff_of_notMem (hrep : Represents s C) (h : c ∉ C) : (c.supp \ s).n
card = c.supp.ncard
参数：hrep : Represents s C；h : c ∉ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.sdiff_eq_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAl
gebra α] {a b : α}, Disjoint a b → b \ a = b
· 使用引理 `SimpleGraph.ConnectedComponent.Represents.disjoint_supp_of_notMem`：disjo
int_supp_of_notMem (hrep : Represents s C) (h : c ∉ C) : Disjoint s c.supp
-/
lemma ncard_sdiff_of_notMem (hrep : Represents s C) (h : c ∉ C) :
    (c.supp \ s).ncard = c.supp.ncard := by
  rw [(disjoint_supp_of_notMem hrep h).sdiff_eq_right]

end ConnectedComponent.Represents

/-
**SimpleGraph.ConnectedComponent.even_ncard_supp_sdiff_rep** 是 Mathlib 中的一个定理，位于
命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {s : Set V} (K : G.ConnectedComponent),
   SimpleGraph.ConnectedComponent.Represents s G.oddComponents → Even (K.supp \ 
s).ncard
参数：K : G.ConnectedComponent；K.supp \ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_notMem`：ncard_s
diff_of_notMem (hrep : Represents s C) (h : c ∉ C) : (c.supp \ s).ncard = c.supp
.ncard
· 使用引理 `Nat.ne_of_odd_add`：ne_of_odd_add (h : Odd (m + n)) : m != n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用引理 `SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_mem`：ncard_sdif
f_of_mem (hrep : Represents s C) (h : c in C) : (c.supp \ s).ncard = c.supp.ncar
d - 1
· 使用定理 `Nat.even_sub`：∀ {m n : ℕ}, n ≤ m → (Even (m - n) ↔ (Even m ↔ Even n))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
-/
lemma ConnectedComponent.even_ncard_supp_sdiff_rep {s : Set V} (K : G.ConnectedComponent)
    (hrep : ConnectedComponent.Represents s G.oddComponents) :
    Even (K.supp \ s).ncard := by
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_notMem
      (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · have : K.supp.ncard ≠ 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
    rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h), Nat.even_sub (by lia)]
    simpa [Nat.even_sub] using Nat.not_even_iff_odd.mp h

end SimpleGraph

