/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Set

/-! ### List.takeWhile and List.dropWhile -/

public section

namespace List

variable {α : Type*} (p : α → Bool)

/-
**List.dropWhile_get_zero_not** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) : ¬p
 ((l.dropWhile p).get ⟨0, hl⟩)
参数：l : List α；hl : 0 < (l.dropWhile p).length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.dropWhile_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, p a = true → List.dropWhile p (a :: l) = List.dropWhile p l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).get ⟨0, hl⟩) := by
  induction l with
  | nil => cases hl
  | cons hd tl IH =>
    simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]
/-
**List.length_dropWhile_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_dropWhile_le (l : List α) : (dropWhile p l).length <= l.length
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_dropWhile_le (l : List α) : (dropWhile p l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [dropWhile, length_cons]
    split
    · lia
    · simp

variable {p} {l : List α}

@[simp]
/-
**List.dropWhile_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropWhile_eq_nil_iff : dropWhile p l = [] ↔ forall x in l, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.dropWhile_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, p a = true → List.dropWhile p (a :: l) = List.dropWhile p l
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.dropWhile_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, ¬p a = true → List.dropWhile p (a :: l) = a :: l
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction l with
  | nil => simp [dropWhile]
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]
/-
**List.dropWhile_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropWhile_eq_self_iff : dropWhile p l = l ↔ forall hl : 0 < l.length, ¬p (
l[0]'hl)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.dropWhile.eq_2`：∀ {α : Type u} (p : α → Bool) (a : α) (as : List α)
,   List.dropWhile p (a :: as) =     match p a with     | true => List.dropWhile
 p as    …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `List.length_dropWhile_le`：length_dropWhile_le (l : List α) : (dropWhile 
p l).length <= l.length
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dropWhile_eq_self_iff : dropWhile p l = l ↔ ∀ hl : 0 < l.length, ¬p (l[0]'hl) := by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [dropWhile]
    by_cases h_p_hd : p hd
    · simp only [h_p_hd, length_cons, Nat.zero_lt_succ, getElem_cons_zero, not_true_eq_false,
        imp_false, iff_false]
      intro h
      replace h := congrArg length h
      have := length_dropWhile_le p tl
      simp at h
      lia
    · simp [h_p_hd]

@[simp]
/-
**List.takeWhile_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeWhile_eq_self_iff : takeWhile p l = l ↔ forall x in l, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.takeWhile_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, p a = true → List.takeWhile p (a :: l) = a :: List.takeWhile p l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.takeWhile_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, ¬p a = true → List.takeWhile p (a :: l) = []
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction l with
  | nil => simp
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]
/-
**List.takeWhile_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeWhile_eq_nil_iff : takeWhile p l = [] ↔ forall hl : 0 < l.length, ¬p (
l.get ⟨0, hl⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.takeWhile_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, p a = true → List.takeWhile p (a :: l) = a :: List.takeWhile p l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.takeWhile_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, ¬p a = true → List.takeWhile p (a :: l) = []
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩) := by
  induction l with
  | nil =>
    simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  | cons x xs IH => by_cases hp : p x <;> simp [hp]
/-
**List.mem_takeWhile_imp** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_takeWhile_imp {x : α} (hx : x in takeWhile p l) : p x
参数：hx : x in takeWhile p l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
-/
theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx
/-
**List.takeWhile_takeWhile** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeWhile_takeWhile (p q : α -> Bool) (l : List α) : takeWhile p (takeWhil
e q l) = takeWhile (fun a => p a ∧ q a) l
参数：p q : α -> Bool；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.decide_and`：∀ (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidabl
e p] [dq : Decidable q], decide (p ∧ q) = (decide p && decide q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.takeWhile_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, p a = true → List.takeWhile p (a :: l) = a :: List.takeWhile p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `List.takeWhile_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l :
 List α}, ¬p a = true → List.takeWhile p (a :: l) = []
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem takeWhile_takeWhile (p q : α → Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction l with
  | nil => simp
  | cons hd tl IH => by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]
/-
**List.takeWhile_idem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.takeWhile_takeWhile`：takeWhile_takeWhile (p q : α -> Bool) (l : Lis
t α) : takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.decide_coe`：∀ (b : Bool) [inst : Decidable (b = true)], decide (b =
 true) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

variable (p) (l)
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma find?_eq_head?_dropWhile_not :
    l.find? p = (l.dropWhile (fun x ↦ !(p x))).head? := by
  induction l
  case nil => simp
  case cons head tail hi =>
    set ph := p head with phh
    rcases ph with rfl | rfl
    · have phh' : ¬(p head = true) := by simp [phh.symm]
      rw [find?_cons_of_neg phh', dropWhile_cons_of_pos]
      · exact hi
      · simpa using phh
    · rw [find?_cons_of_pos phh.symm, dropWhile_cons_of_neg]
      · simp
      · simpa using phh
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma find?_not_eq_head?_dropWhile :
    l.find? (fun x ↦ !(p x)) = (l.dropWhile p).head? := by
  convert! l.find?_eq_head?_dropWhile_not ?_
  simp

variable {p} {l}
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma find?_eq_head_dropWhile_not (h : ∃ x ∈ l, p x) :
    l.find? p = some ((l.dropWhile (fun x ↦ !(p x))).head (by simpa using h)) := by
  rw [l.find?_eq_head?_dropWhile_not p, ← head_eq_iff_head?_eq_some]
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma find?_not_eq_head_dropWhile (h : ∃ x ∈ l, ¬p x) :
    l.find? (fun x ↦ !(p x)) = some ((l.dropWhile p).head (by simpa using h)) := by
  convert! l.find?_eq_head_dropWhile_not ?_
  · simp
  · simpa using h

end List

