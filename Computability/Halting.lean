/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.RE
public import Mathlib.Data.Set.Subsingleton

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

public section

open Encodable Denumerable
open Computable Part
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace ComputablePred

variable {α : Type*} [Primcodable α]

/-- **Rice's Theorem** -/
/-
**ComputablePred.rice** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：rice (C : Set (Nat ->. Nat)) (h : ComputablePred fun c => eval c in C) {f 
g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f in C) : g in C
参数：C : Set (Nat ->. Nat)；h : ComputablePred fun c => eval c in C；hf : Nat.Partre
c f；hg : Nat.Partrec g；fC : f in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.Code.fixed_point₂`：fixed_point₂ {f : Code -> Nat ->. Nat} (h
f : Partrec₂ f) : exists c : Code, eval c = f c
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Partrec.cond`：cond {c : α -> Bool} {f : α ->. σ} {g : α ->. σ} (hc : Com
putable c) (hf : Partrec f) (hg : Partrec g) : Partrec fun a => cond (c a) (f a)
 (…
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.cond_decide`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (t e 
: α), (bif decide p then t else e) = if p then t else e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
**Rice's Theorem**
-/
theorem rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C := by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c ∈ C <;> simp_all
/-
**ComputablePred.rice** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：rice (C : Set (Nat ->. Nat)) (h : ComputablePred fun c => eval c in C) {f 
g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f in C) : g in C
参数：C : Set (Nat ->. Nat)；h : ComputablePred fun c => eval c in C；hf : Nat.Partre
c f；hg : Nat.Partrec g；fC : f in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.Code.fixed_point₂`：fixed_point₂ {f : Code -> Nat ->. Nat} (h
f : Partrec₂ f) : exists c : Code, eval c = f c
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Partrec.cond`：cond {c : α -> Bool} {f : α ->. σ} {g : α ->. σ} (hc : Com
putable c) (hf : Partrec f) (hg : Partrec g) : Partrec fun a => cond (c a) (f a)
 (…
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.cond_decide`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (t e 
: α), (bif decide p then t else e) = if p then t else e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ := by
  exact
      have hC : ∀ f, f ∈ C ↔ eval f ∈ eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C0
            (hC _).2 <|
              rice (eval '' C) (h.of_eq hC)
                (Partrec.nat_iff.1 <| eval_part.comp (const cf) Computable.id)
                (Partrec.nat_iff.1 <| eval_part.comp (const cg) Computable.id) ((hC _).1 fC),
        fun h => by {
          obtain rfl | rfl := h <;> simpa [ComputablePred, Set.mem_empty_iff_false] using
            Computable.const _}⟩

/-- The Halting problem is recursively enumerable -/
/-
**ComputablePred.halting_problem_re** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：halting_problem_re (n) : REPred fun c => (eval c n).Dom
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.dom_re`：Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f 
: α ->. β} (h : Partrec f) : REPred fun a => (f a).Dom
· 使用定理 `Partrec₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type 
u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] 
[in…
· 使用定理 `Nat.Partrec.Code.eval_part`：eval_part : Partrec₂ eval
· 使用定理 `Computable.id`：∀ {α : Type u_1} [inst : Primcodable α], Computable id
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s

--- 原说明 ---
The Halting problem is recursively enumerable
-/
theorem halting_problem_re (n) : REPred fun c => (eval c n).Dom :=
  (eval_part.comp Computable.id (Computable.const _)).dom_re

/-- The **Halting problem** is not computable -/
/-
**ComputablePred.halting_problem** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：∀ (n : ℕ), ¬ComputablePred fun c => (c.eval n).Dom
参数：n : ℕ；c.eval n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComputablePred.rice`：rice (C : Set (Nat ->. Nat)) (h : ComputablePred fu
n c => eval c in C) {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f in C
) : g in …
· 使用定理 `Nat.Partrec.none`：none : Nat.Partrec fun _ => none
· 使用定理 `trivial`：True

--- 原说明 ---
The **Halting problem** is not computable
-/
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom
  | h => rice { f | (f n).Dom } h Nat.Partrec.zero Nat.Partrec.none trivial
/-
**ComputablePred.halting_problem_not_re** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePre
d`。
形式化陈述：∀ (n : ℕ), ¬REPred fun c => ¬(c.eval n).Dom
参数：n : ℕ；c.eval n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComputablePred.halting_problem`：∀ (n : ℕ), ¬ComputablePred fun c => (c.e
val n).Dom
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ComputablePred.computable_iff_re_compl_re'`：computable_iff_re_compl_re' 
{p : α -> Prop} : ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a
· 使用定理 `ComputablePred.halting_problem_re`：halting_problem_re (n) : REPred fun c
 => (eval c n).Dom
-/
theorem halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom
  | h => halting_problem _ <| computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩

end ComputablePred

