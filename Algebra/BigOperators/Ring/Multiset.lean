/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.Data.Multiset.Sections

/-! # Lemmas about `Multiset.sum` and `Multiset.prod` requiring extra algebra imports -/

public section


variable {ι M M₀ R : Type*}

namespace Multiset
section CommMonoid
variable [CommMonoid M] [HasDistribNeg M]

/-
**Multiset.prod_map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {M : Type u_2} [inst : CommMonoid M] [inst_1 : HasDistribNeg M] (s : Mul
tiset M),   (Multiset.map Neg.neg s).prod = (-1) ^ s.card * s.prod
参数：s : Multiset M；Multiset.map Neg.neg s；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.prod_map_neg`：prod_map_neg (l : List M) : (l.map Neg.neg).prod = (-
1) ^ l.length * l.prod
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma prod_map_neg (s : Multiset M) : (s.map Neg.neg).prod = (-1) ^ card s * s.prod :=
  Quotient.inductionOn s (by simp)

end CommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {s : Multiset M₀}

/-
**Multiset.prod_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_zero (h : (0 : M₀) in s) : s.prod = 0
参数：h : (0 : M₀) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_eq_zero (h : (0 : M₀) ∈ s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

variable [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀}
/-
**Multiset.prod_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {M₀ : Type u_3} [inst : CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nont
rivial M₀] {s : Multiset M₀},   s.prod = 0 ↔ 0 ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.quot_mk_to_coe`：quot_mk_to_coe (l : List α) : @Eq (Multiset α) 
⟦l⟧ l
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用定理 `List.prod_eq_zero_iff`：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] [Non
trivial M₀] [NoZeroDivisors M₀] {l : List M₀}, l.prod = 0 ↔ 0 ∈ l
-/
@[simp] lemma prod_eq_zero_iff : s.prod = 0 ↔ (0 : M₀) ∈ s :=
  Quotient.inductionOn s fun l ↦ by rw [quot_mk_to_coe, prod_coe]; exact List.prod_eq_zero_iff
/-
**Multiset.prod_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod != 0
参数：h : (0 : M₀) ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.prod_eq_zero_iff`：∀ {M₀ : Type u_3} [inst : CommMonoidWithZero 
M₀] [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀},   s.prod = 0 ↔ 0 ∈ s
-/
lemma prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod ≠ 0 := mt prod_eq_zero_iff.1 h

end CommMonoidWithZero

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] {a : R} {s : Multiset ι} {f : ι → R}

/-
**Multiset.sum_map_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sum_map_mul_left : sum (s.map fun i => a * f i) = a * sum (s.map f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
lemma sum_map_mul_left : sum (s.map fun i ↦ a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]
/-
**Multiset.sum_map_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sum_map_mul_right : sum (s.map fun i => f i * a) = sum (s.map f) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma sum_map_mul_right : sum (s.map fun i ↦ f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R] {s : Multiset R} {a : R}

/-
**Multiset.dvd_sum** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：dvd_sum : (forall x in s, a ∣ x) -> a ∣ s.sum
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
-/
lemma dvd_sum : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
  Multiset.induction_on s (fun _ ↦ dvd_zero _) fun x s ih h ↦ by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy ↦ h _ <| mem_cons.2 <| Or.inr hy)

end NonUnitalSemiring

section CommSemiring
variable [CommSemiring R]

/-
**Multiset.prod_map_sum** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_sum {s : Multiset (Multiset R)} : prod (s.map sum) = sum ((Sectio
ns s).map prod)
参数：Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.sections_cons`：sections_cons (s : Multiset (Multiset α)) (m : M
ultiset α) : Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.con
s a)
· 使用定理 `Multiset.map_bind`：map_bind (m : Multiset α) (n : α -> Multiset β) (f : 
β -> γ) : map f (bind m n) = bind m fun a => map f (n a)
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.sum_bind`：∀ {α : Type u_1} {β : Type v} [inst : AddCommMonoid β
] (s : Multiset α) (t : α → Multiset β),   (s.bind t).sum = (Multiset.map (fun a
 => (t …
· 使用引理 `Multiset.sum_map_mul_left`：sum_map_mul_left : sum (s.map fun i => a * f 
i) = a * sum (s.map f)
· 使用引理 `Multiset.sum_map_mul_right`：sum_map_mul_right : sum (s.map fun i => f i 
* a) = sum (s.map f) * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
lemma prod_map_sum {s : Multiset (Multiset R)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
/-
**Multiset.prod_map_add** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_add {s : Multiset ι} {f g : ι -> R} : prod (s.map fun i => f i + 
g i) = sum ((antidiagonal s).map fun p => (p.1.map f).prod * (p.2.map g).prod)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.sum_map_mul_left`：sum_map_mul_left : sum (s.map fun i => a * f 
i) = a * sum (s.map f)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Multiset.sum_map_add`：∀ {ι : Type u_2} {M : Type u_5} [inst : AddCommMon
oid M] {m : Multiset ι} {f g : ι → M},   (Multiset.map (fun i => f i + g i) m).s
um = (Mult…
· 使用定理 `Multiset.antidiagonal_cons`：antidiagonal_cons (a : α) (s) : antidiagonal
 (a ::ₘ s) = map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a
) id) (antidiago…
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma prod_map_add {s : Multiset ι} {f g : ι → R} :
    prod (s.map fun i ↦ f i + g i) =
      sum ((antidiagonal s).map fun p ↦ (p.1.map f).prod * (p.2.map g).prod) := by
  refine s.induction_on ?_ fun a s ih ↦ ?_
  · simp only [map_zero, prod_zero, antidiagonal_zero, map_singleton, mul_one, sum_singleton]
  · simp only [map_cons, prod_cons, ih, sum_map_mul_left.symm, add_mul, mul_left_comm (f a),
      mul_left_comm (g a), sum_map_add, antidiagonal_cons, Prod.map_fst, Prod.map_snd,
      id_eq, map_add, map_map, Function.comp_apply, mul_assoc, sum_add]
    exact add_comm _ _

end CommSemiring
end Multiset

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

/-
**Commute.multiset_sum_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：multiset_sum_right (a : R) (h : forall b in s, Commute a b) : Commute a s.
sum
参数：a : R；h : forall b in s, Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.quot_mk_to_coe`：quot_mk_to_coe (l : List α) : @Eq (Multiset α) 
⟦l⟧ l
· 使用定理 `Multiset.sum_coe`：∀ {M : Type u_3} [inst : AddCommMonoid M] (l : List M)
, (↑l).sum = l.sum
· 使用引理 `Commute.list_sum_right`：list_sum_right (a : R) (l : List R) (h : forall 
b in l, Commute a b) : Commute a l.sum
-/
theorem multiset_sum_right (a : R) (h : ∀ b ∈ s, Commute a b) : Commute a s.sum := by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe, sum_coe]
  exact Commute.list_sum_right _ _ h
/-
**Commute.multiset_sum_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：multiset_sum_left (b : R) (h : forall a in s, Commute a b) : Commute s.sum
 b
参数：b : R；h : forall a in s, Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Commute.multiset_sum_right`：multiset_sum_right (a : R) (h : forall b in 
s, Commute a b) : Commute a s.sum
-/
theorem multiset_sum_left (b : R) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b :=
  ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

end Commute

