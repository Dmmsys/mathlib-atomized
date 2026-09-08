/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Multiset.Bind

/-!
# Sections of a multiset
-/

@[expose] public section

assert_not_exists Ring

namespace Multiset

variable {α : Type*}

section Sections

/-- The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is a member of the corresponding multiset.
-/
/-
**Multiset.Sections** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Sections (s : Multiset (Multiset α)) : Multiset (Multiset α)
参数：s : Multiset (Multiset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is a member of the corre
sponding multiset.
-/
def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]

@[simp]
/-
**Multiset.sections_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sections_zero : Sections (0 : Multiset (Multiset α)) = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sections_zero : Sections (0 : Multiset (Multiset α)) = {0} :=
  rfl

@[simp]
/-
**Multiset.sections_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sections_cons (s : Multiset (Multiset α)) (m : Multiset α) : Sections (m :
:ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a)
参数：s : Multiset (Multiset α)；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.recOn_cons`：recOn_cons (a : α) (m : Multiset α) : (a ::ₘ m).rec
On C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq)
-/
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a) :=
  recOn_cons m s
/-
**Multiset.coe_sections** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (l : List (List α)), (↑(List.map (fun l => ↑l) l)).Sectio
ns = ↑(List.map (fun l => ↑l) l.sections)
参数：l : List (List α)；↑(List.map (fun l => ↑l) l)；List.map (fun l => ↑l) l.sectio
ns。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sections :
    ∀ l : List (List α),
      Sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sections]
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l]
    simp [Function.comp_def, List.flatMap]

@[simp]
/-
**Multiset.sections_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sections_add (s t : Multiset (Multiset α)) : Sections (s + t) = (Sections 
s).bind fun m => (Sections t).map (m + ·)
参数：s t : Multiset (Multiset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.singleton_bind`：singleton_bind : bind {a} f = f a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.sections_cons`：sections_cons (s : Multiset (Multiset α)) (m : M
ultiset α) : Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.con
s a)
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.map_bind`：map_bind (m : Multiset α) (n : α -> Multiset β) (f : 
β -> γ) : map f (bind m n) = bind m fun a => map f (n a)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.bind_assoc`：bind_assoc {s : Multiset α} {f : α -> Multiset β} {
g : β -> Multiset γ} : (s.bind f).bind g = s.bind fun a => (f a).bind g
· 使用定理 `Multiset.bind_map`：bind_map (m : Multiset α) (n : β -> Multiset γ) (f : 
α -> β) : bind (map f m) n = bind m fun a => n (f a)
-/
theorem sections_add (s t : Multiset (Multiset α)) :
    Sections (s + t) = (Sections s).bind fun m => (Sections t).map (m + ·) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map]
/-
**Multiset.mem_sections** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_sections {s : Multiset (Multiset α)} : forall {a}, a in Sections s ↔ s
.Rel (fun s a => a in s) a
参数：Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sections_cons`：sections_cons (s : Multiset (Multiset α)) (m : M
ultiset α) : Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.con
s a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mem_sections {s : Multiset (Multiset α)} :
    ∀ {a}, a ∈ Sections s ↔ s.Rel (fun s a => a ∈ s) a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih, rel_cons_left, eq_comm]
/-
**Multiset.card_sections** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.ma
p card)
参数：Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sections_cons`：sections_cons (s : Multiset (Multiset α)) (m : M
ultiset α) : Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.con
s a)
· 使用定理 `Multiset.card_bind`：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp +contextual)

end Sections

end Multiset

