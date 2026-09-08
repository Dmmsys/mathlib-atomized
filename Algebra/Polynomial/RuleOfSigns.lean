/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic

/-!

# Descartes' Rule of Signs

We define the "sign changes" in the coefficients of a polynomial, and prove Descartes'
Rule of Signs: a real polynomial has at most as many positive roots as there are sign
changes. A sign change is when there is a positive coefficient followed by a negative
coefficient, or vice versa, with any number of zero coefficients in between.

## Main Definitions

- `Polynomial.signVariations`: The number of sign changes in a polynomial's coefficients,
  where `0` coefficients are ignored.

## Main theorem

- `Polynomial.roots_countP_pos_le_signVariations`. States that
  `P.roots.countP (0 < ·) ≤ P.signVariations`, so that positive roots are counted with multiplicity.
  It's currently proved for any `CommRing` with `IsStrictOrderedRing`. There is likely some correct
  statement in terms of a (noncommutative) `Ring`, but `Polynomial.roots` is only defined for
  commutative rings.

## Reference

[Wikipedia: Descartes' Rule of Signs](https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs)
-/

@[expose] public section

namespace Polynomial

section Semiring
variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

/-- Counts the number of times that the coefficients in a polynomial change sign, with
the convention that 0 can count as either sign. -/
/-
**Polynomial.signVariations** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：signVariations : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Counts the number of times that the coefficients in a polynomial change sign, wi
th
the convention that 0 can count as either sign.
-/
def signVariations : ℕ :=
  letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· ≠ 0)
  (nonzero_signs.destutter (· ≠ ·)).length - 1

variable (R) in
@[simp]
/-
**Polynomial.signVariations_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：signVariations_zero : signVariations (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter.congr_simp`：∀ {α : Type u_1} (R R_1 : α → α → Prop),   R 
= R_1 →     ∀ {inst : DecidableRel R} [inst_1 : DecidableRel R_1] (a a_1 : List 
α),       a = a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Polynomial.coeffList_zero`：coeffList_zero : (0 : R[X]).coeffList = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem signVariations_zero : signVariations (0 : R[X]) = 0 := by
  simp [signVariations]

/-- Sign variations of a monomial are always zero. -/
@[simp]
/-
**Polynomial.signVariations_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：signVariations_monomial (d : Nat) (c : R) : signVariations (monomial d c) 
= 0
参数：d : Nat；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `Polynomial.signVariations_zero`：signVariations_zero : signVariations (0 
: R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.destutter.congr_simp`：∀ {α : Type u_1} (R R_1 : α → α → Prop),   R 
= R_1 →     ∀ {inst : DecidableRel R} [inst_1 : DecidableRel R_1] (a a_1 : List 
α),       a = a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Polynomial.coeffList_eraseLead`：coeffList_eraseLead (h : P != 0) : P.coe
ffList = P.leadingCoeff :: (.replicate (P.natDegree - P.eraseLead.degree.succ) 0
 ++ P.eraseLead.coef…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.monomial_eq_zero_iff`：monomial_eq_zero_iff (t : R) (n : Nat) 
: monomial n t = 0 ↔ t = 0
· 使用定理 `Polynomial.leadingCoeff_monomial`：leadingCoeff_monomial (a : R) (n : Nat
) : leadingCoeff (monomial n a) = a
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.eraseLead_monomial`：eraseLead_monomial (i : Nat) (r : R) : er
aseLead (monomial i r) = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Polynomial.coeffList_zero`：coeffList_zero : (0 : R[X]).coeffList = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {α_1 : Type u_2} {f
 : α → α_1},   List.map f (List.replicate n a) = List.replicate n (f a)
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.not_false`：(!false) = true
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Sign variations of a monomial are always zero.
-/
theorem signVariations_monomial (d : ℕ) (c : R) : signVariations (monomial d c) = 0 := by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, signVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

/-- If the first two signs are the same, then `signVariations` is unchanged by `eraseLead` -/
/-
**Polynomial.signVariations_eraseLead** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：signVariations_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign
 P.nextCoeff) : signVariations P.eraseLead = signVariations P
参数：h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `Polynomial.signVariations_zero`：signVariations_zero : signVariations (0 
: R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.coeffList_eq_cons_leadingCoeff`：coeffList_eq_cons_leadingCoef
f (h : P != 0) : exists ls, P.coeffList = P.leadingCoeff :: ls
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.nextCoeff_eq_zero_of_eraseLead_eq_zero`：nextCoeff_eq_zero_of_
eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff = 0
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Polynomial.leadingCoeff_eraseLead_eq_nextCoeff`：leadingCoeff_eraseLead_e
q_nextCoeff (h : f.nextCoeff != 0) : f.eraseLead.leadingCoeff = f.nextCoeff
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Polynomial.coeffList_eraseLead`：coeffList_eraseLead (h : P != 0) : P.coe
ffList = P.leadingCoeff :: (.replicate (P.natDegree - P.eraseLead.degree.succ) 0
 ++ P.eraseLead.coef…
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {α_1 : Type u_2} {f
 : α → α_1},   List.map f (List.replicate n a) = List.replicate n (f a)
· 使用定理 `List.filter_append`：∀ {α : Type u_1} {p : α → Bool} (l₁ l₂ : List α), Li
st.filter p (l₁ ++ l₂) = List.filter p l₁ ++ List.filter p l₂
· 使用定理 `List.filter_replicate_of_neg`：∀ {α : Type u_1} {p : α → Bool} {n : ℕ} {a
 : α}, ¬p a = true → List.filter p (List.replicate n a) = []
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If the first two signs are the same, then `signVariations` is unchanged by `eras
eLead`
-/
theorem signVariations_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff) :
    signVariations P.eraseLead = signVariations P := by
  by_cases hpz : P = 0
  · simp_all
  · have h₂ : nextCoeff P ≠ 0 := by intro; simp_all
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    simp [signVariations, List.destutter, leadingCoeff_eraseLead_eq_nextCoeff h₂, hl, h, h₂,
      coeffList_eraseLead hpz]

/-- If we drop the leading coefficient, the sign changes drop by 0 or 1 depending on whether
the first two nonzero coefficients match. -/
/-
**Polynomial.signVariations_eq_eraseLead_add_ite** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：signVariations_eq_eraseLead_add_ite {P : Polynomial R} (h : P != 0) : sign
Variations P = signVariations P.eraseLead + if SignType.sign P.leadingCoeff = -S
ignType.sign P.eraseLead.leadingCoeff then 1 else 0
参数：h : P != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.signVariations.eq_1`：∀ {R : Type u_1} [inst : Semiring R] [in
st_1 : LinearOrder R] (P : Polynomial R),   P.signVariations =     (List.destutt
er (fun x1 x2 => x1 …
· 使用定理 `Polynomial.coeffList_eraseLead`：coeffList_eraseLead (h : P != 0) : P.coe
ffList = P.leadingCoeff :: (.replicate (P.natDegree - P.eraseLead.degree.succ) 0
 ++ P.eraseLead.coef…
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {α_1 : Type u_2} {f
 : α → α_1},   List.map f (List.replicate n a) = List.replicate n (f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.destutter.congr_simp`：∀ {α : Type u_1} (R R_1 : α → α → Prop),   R 
= R_1 →     ∀ {inst : DecidableRel R} [inst_1 : DecidableRel R_1] (a a_1 : List 
α),       a = a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.coeffList_eq_nil`：coeffList_eq_nil {P : R[X]} : P.coeffList =
 [] ↔ P = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `List.filter_replicate_of_neg`：∀ {α : Type u_1} {p : α → Bool} {n : ℕ} {a
 : α}, ¬p a = true → List.filter p (List.replicate n a) = []
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `Bool.not_true`：(!true) = false
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If we drop the leading coefficient, the sign changes drop by 0 or 1 depending on
 whether
the first two nonzero coefficients match.
-/
theorem signVariations_eq_eraseLead_add_ite {P : Polynomial R} (h : P ≠ 0) :
    signVariations P = signVariations P.eraseLead + if SignType.sign P.leadingCoeff
      = -SignType.sign P.eraseLead.leadingCoeff then 1 else 0 := by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) ≠ 0 := by simp_all
  rw [signVariations, signVariations, coeffList_eraseLead hpz]
  rw [List.map_cons, List.map_append, List.map_replicate]
  rcases h_eL : P.eraseLead.coeffList with _ | ⟨c, cs⟩
  · simp [coeffList_eq_nil.mp h_eL, h]
  simp only [List.filter_append, List.filter_replicate, List.map_cons, List.filter, ne_eq, hsl]
  have h₁ : SignType.sign c ≠ 0 := by
    by_contra h₂
    suffices eraseLead P = 0 by grind [coeffList_zero]
    by_contra h
    have := coeffList_eq_cons_leadingCoeff h
    grind [leadingCoeff_eq_zero, sign_eq_zero_iff]
  simp only [decide_not, sign_zero, List.destutter, Bool.false_eq_true, reduceIte, h₁,
    decide_false, Bool.not_false, List.nil_append, List.destutter', decide_true, Bool.not_true]
  obtain rfl : c = leadingCoeff P.eraseLead := by
    have h_eL : eraseLead P ≠ 0 := by simp [← coeffList_eq_nil, h_eL]
    obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h_eL
    grind
  by_cases h₄ : SignType.sign P.leadingCoeff = SignType.sign P.eraseLead.leadingCoeff
  · grind [SignType.neg_eq_self_iff]
  rw [if_pos h₄, if_pos ?_]
  · grind [Nat.sub_add_cancel, List.length_pos_of_ne_nil, List.destutter'_ne_nil]
  cases _ : SignType.sign P.leadingCoeff
  <;> cases _ : SignType.sign P.eraseLead.leadingCoeff
  <;> grind [= SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.neg_eq_neg_one, neg_neg]

/-- We can only lose, not gain, sign changes if we drop the leading coefficient. -/
/-
**Polynomial.signVariations_eraseLead_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：signVariations_eraseLead_le : signVariations P.eraseLead <= signVariations
 P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `Polynomial.signVariations_zero`：signVariations_zero : signVariations (0 
: R[X]) = 0

--- 原说明 ---
We can only lose, not gain, sign changes if we drop the leading coefficient.
-/
theorem signVariations_eraseLead_le : signVariations P.eraseLead ≤ signVariations P := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

/-- We can only lose at most one sign changes if we drop the leading coefficient. -/
/-
**Polynomial.signVariations_le_eraseLead_succ** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：signVariations_le_eraseLead_succ : signVariations P <= signVariations P.er
aseLead + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.signVariations_zero`：signVariations_zero : signVariations (0 
: R[X]) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
We can only lose at most one sign changes if we drop the leading coefficient.
-/
theorem signVariations_le_eraseLead_succ : signVariations P ≤ signVariations P.eraseLead + 1 := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] (P : Polynomial R) {x : R}

/-- The number of sign changes does not change if we negate. -/
@[simp]
/-
**Polynomial.signVariations_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：signVariations_neg : signVariations (-P) = signVariations P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.signVariations.eq_1`：∀ {R : Type u_1} [inst : Semiring R] [in
st_1 : LinearOrder R] (P : Polynomial R),   P.signVariations =     (List.destutt
er (fun x1 x2 => x1 …
· 使用定理 `Polynomial.coeffList_neg`：coeffList_neg : (-P).coeffList = P.coeffList.m
ap (-·)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.destutter.congr_simp`：∀ {α : Type u_1} (R R_1 : α → α → Prop),   R 
= R_1 →     ∀ {inst : DecidableRel R} [inst_1 : DecidableRel R_1] (a a_1 : List 
α),       a = a…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.filter_map`：∀ {β : Type u_1} {α : Type u_2} {f : β → α} {p : α → Bo
ol} {l : List β},   List.filter p (List.map f l) = List.map f (List.filter (p ∘ 
f) l)
· 使用定理 `List.comp_map`：comp_map (h : β -> γ) (g : α -> β) (l : List α) : map (h 
∘ g) l = map h (map g l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The number of sign changes does not change if we negate.
-/
theorem signVariations_neg : signVariations (-P) = signVariations P := by
  rw [signVariations, signVariations, coeffList_neg]
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x : R) => -x) = (fun x => -x) ∘ SignType.sign := by
    grind [Left.sign_neg]
  have h_neg_destutter (l : List SignType) :
      (l.destutter (¬· = ·)).map (- ·) = (l.map (- ·)).destutter (¬· = ·) := by
    grind [List.map_destutter, neg_inj]
  rw [hsc, List.comp_map, ← h_neg_destutter, List.length_map]
  congr 5
  funext
  simp [SignType.sign]

end OrderedRing

section StrictOrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

/-- The number of sign changes does not change if we multiply by any nonzero scalar. -/
@[simp]
/-
**Polynomial.signVariations_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：signVariations_C_mul (P : Polynomial R) (hx : η != 0) : signVariations (C 
η * P) = signVariations P
参数：P : Polynomial R；hx : η != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.signVariations.eq_1`：∀ {R : Type u_1} [inst : Semiring R] [in
st_1 : LinearOrder R] (P : Polynomial R),   P.signVariations =     (List.destutt
er (fun x1 x2 => x1 …
· 使用定理 `Polynomial.coeffList_C_mul`：coeffList_C_mul {x : R} (hx : x != 0) : (C x
 * P).coeffList = P.coeffList.map (x * ·)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.comp_map`：comp_map (h : β -> γ) (g : α -> β) (l : List α) : map (h 
∘ g) l = map h (map g l)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The number of sign changes does not change if we multiply by any nonzero scalar.
-/
theorem signVariations_C_mul (P : Polynomial R) (hx : η ≠ 0) :
    signVariations (C η * P) = signVariations P := by
  wlog! hx2 : 0 < η
  · simpa [lt_of_le_of_ne hx2, hx] using this (η := -η) (P := -P)
  rw [signVariations, signVariations]
  rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2)), ← List.comp_map]
  congr 5
  funext
  simp [hx2, sign_mul]

/-- If P's coefficients start with signs `[+, -, ...]`, then multiplying by a binomial `X - η`
  commutes with `eraseLead` in the number of sign changes. This is because the product of
  `P` and `X - η` has the pattern `[+, -, ...]` as well, so then `P.eraseLead` starts with
  `[-,...]`, and multiplying by `X - η` gives `[-, ...]` too. -/
/-
**Polynomial.signVariations_eraseLead_mul_X_sub_C** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
形式化陈述：signVariations_eraseLead_mul_X_sub_C (hη : 0 < η) (hP₀ : 0 < leadingCoeff 
P) (hc : P.nextCoeff < 0) : ((X - C η) * P).eraseLead.signVariations = ((X - C η
) * P.eraseLead).signVariations
参数：hη : 0 < η；hP₀ : 0 < leadingCoeff P；hc : P.nextCoeff < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.exists_eq_add_one`：∀ {a : ℕ}, (∃ n, a = n + 1) ↔ 0 < a
· 使用定理 `Polynomial.natDegree_pos_of_nextCoeff_ne_zero`：natDegree_pos_of_nextCoef
f_ne_zero (h : p.nextCoeff != 0) : 0 < p.natDegree
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.nextCoeff_eq_zero_of_eraseLead_eq_zero`：nextCoeff_eq_zero_of_
eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff = 0
· 使用引理 `Polynomial.natDegree_eraseLead_add_one`：natDegree_eraseLead_add_one (h :
 f.nextCoeff != 0) : f.eraseLead.natDegree + 1 = f.natDegree
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If P's coefficients start with signs `[+, -, ...]`, then multiplying by a binomi
al `X - η`
  commutes with `eraseLead` in the number of sign changes. This is because the p
roduct of
  `P` and `X - η` has the pattern `[+, -, ...]` as well, so then `P.eraseLead` s
tarts with
  `[-,...]`, and multiplying by `X - η` gives `[-, ...]` too.
-/
lemma signVariations_eraseLead_mul_X_sub_C (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
    (hc : P.nextCoeff < 0) :
    ((X - C η) * P).eraseLead.signVariations = ((X - C η) * P.eraseLead).signVariations := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one.mpr (natDegree_pos_of_nextCoeff_ne_zero hc.ne)
  have hndxP : natDegree ((X - C η) * P) = P.natDegree + 1 := by
    have hPn0 : P ≠ 0 :=
      leadingCoeff_ne_zero.mp hP₀.ne'
    rw [natDegree_mul (X_sub_C_ne_zero η) hPn0, natDegree_X_sub_C, add_comm]
  have hndxeP : natDegree ((X - C η) * P.eraseLead) = P.natDegree := by
    have hePn0 : P.eraseLead ≠ 0 :=
      mt nextCoeff_eq_zero_of_eraseLead_eq_zero hc.ne
    rw [natDegree_mul (X_sub_C_ne_zero η) hePn0, natDegree_X_sub_C, add_comm]
    exact natDegree_eraseLead_add_one hc.ne
  have hQ : ((X - C η) * P).nextCoeff = coeff P d - η * coeff P (d + 1) := by
    grind [nextCoeff_of_natDegree_pos, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ, sub_neg]
    trans 0
    · grind [nextCoeff_of_natDegree_pos]
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP, natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [signVariations, signVariations, this]
    have : 0 < natDegree ((X - C η) * P.eraseLead) := by lia
    grind [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff,
      LT.lt.ne, sign_neg, coeffList_eraseLead, ne_zero_of_natDegree_gt,
      nextCoeff_eq_zero_of_eraseLead_eq_zero]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0, ← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP, hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne, ← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ, mul_sub, sub_mul, sub_mul, X_mul_monomial, C_mul_monomial, monomial_sub]
  rw [leadingCoeff, nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos), hd, Nat.add_sub_cancel]
  abel

/-- This lemma is really a specialization of `succ_signVariations_le_sub_mul` to monomials. -/
/-
**Polynomial.succ_signVariations_X_sub_C_mul_monomial** 是 Mathlib 中的一个引理，位于命名空间 
`Polynomial`。
形式化陈述：succ_signVariations_X_sub_C_mul_monomial {d c} (hc : c != 0) (hη : 0 < η) 
: (monomial d c).signVariations + 1 <= ((X - C η) * monomial d c).signVariations
参数：hc : c != 0；hη : 0 < η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is really a specialization of `succ_signVariations_le_sub_mul` to mon
omials.
-/
lemma succ_signVariations_X_sub_C_mul_monomial {d c} (hc : c ≠ 0) (hη : 0 < η) :
    (monomial d c).signVariations + 1 ≤ ((X - C η) * monomial d c).signVariations := by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) ≠ 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c ≠ SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', signVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using! List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)
/-
**Polynomial.exists_cons_of_leadingCoeff_pos** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_cons_of_leadingCoeff_pos (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff ≠ 0) :
    ∃ c₀ cs, ((X - C η) * P).coeffList = P.leadingCoeff :: c₀ :: cs ∧
      ((X - C η) * P.eraseLead).coeffList = P.nextCoeff :: cs := by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅ : (X - C η) ≠ 0 := X_sub_C_ne_zero η
  have h₆ : P.eraseLead ≠ 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  apply leadingCoeff_eraseLead_eq_nextCoeff at h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅ h₆)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have h₇ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅ h₃, natDegree_X_sub_C, add_comm]
    have h₈ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        h₅, h₆, h₂, h₄, add_comm 1]
    have : P.eraseLead.natDegree + 2 = ((X - C η) * P.eraseLead).coeffList.length := by
      simp [h₅, h₆, natDegree_mul, add_comm 1]
    have : P.natDegree + 2 = ((X - C η) * P).coeffList.length := by simp [X_sub_C_ne_zero, h₃, h₇]
    have := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    by_cases h₉ : ((X - C η) * P).nextCoeff = 0
    · suffices ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        #adaptation_note
        /--
        Moving from `nightly-2025-10-13` to `nightly-2025-10-19`
        we now need to provide an intermediate step.
        -/
        have : ((X - C η) * P).natDegree - ((X - C η) * P).eraseLead.degree.succ = n + 1 := by grind
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, eq_of_sub_eq_zero, coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      grind [coeff_X_sub_C_mul, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]

/-- If a polynomial starts with two positive coefficients, then the sign changes in the product
`(X - η) * P` is the same as `(X - η) * P.eraseLead`. This lemma lets us do induction on the
degree of P when P starts with matching coefficient signs. Of course this is also true when the
first two coefficients of P are *negative*, but we just prove the case where they're positive
since it's cleaner and sufficient for the later use. -/
/-
**Polynomial.signVariations_X_sub_C_mul_eraseLead_le** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial`。
形式化陈述：signVariations_X_sub_C_mul_eraseLead_le (h : 0 < P.leadingCoeff) (h₂ : 0 <
 P.nextCoeff) : signVariations ((X - C η) * P.eraseLead) <= signVariations ((X -
 C η) * P)
参数：h : 0 < P.leadingCoeff；h₂ : 0 < P.nextCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Polynomial.RuleOfSigns.0.Polynomial.exists_cons
_of_leadingCoeff_pos`：∀ {R : Type u_1} [inst : Ring R] [inst_1 : LinearOrder R] 
[IsStrictOrderedRing R] {P : Polynomial R} (η : R),   0 < P.leadingCoeff →     P
.n…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `List.length_pos_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → 0 < l
.length
· 使用定理 `List.destutter'_ne_nil`：∀ {α : Type u_1} (l : List α) (R : α → α → Prop)
 [inst : DecidableRel R] {a : α}, List.destutter' R a l ≠ []
· 使用定理 `List.filter_cons`：∀ {α : Type u_1} {x : α} {xs : List α} {p : α → Bool},
   List.filter p (x :: xs) = if p x = true then x :: List.filter p xs else List.
filter…
· 使用定理 `List.destutter'.congr_simp`：∀ {α : Type u_1} (R R_1 : α → α → Prop),   R
 = R_1 →     ∀ {inst : DecidableRel R} [inst_1 : DecidableRel R_1] (a a_1 : α), 
      a = a_1 → …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.destutter'_cons`：∀ {α : Type u_1} (l : List α) (R : α → α → Prop) [
inst : DecidableRel R] {a b : α},   List.destutter' R a (b :: l) = if R a b then
 a :: List…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.destutter_cons'`：destutter_cons' : (a :: l).destutter R = destutter
' R a l

--- 原说明 ---
If a polynomial starts with two positive coefficients, then the sign changes in 
the product
`(X - η) * P` is the same as `(X - η) * P.eraseLead`. This lemma lets us do indu
ction on the
degree of P when P starts with matching coefficient signs. Of course this is als
o true when the
first two coefficients of P are *negative*, but we just prove the case where the
y're positive
since it's cleaner and sufficient for the later use.
-/
lemma signVariations_X_sub_C_mul_eraseLead_le (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff) :
    signVariations ((X - C η) * P.eraseLead) ≤ signVariations ((X - C η) * P) := by
  obtain ⟨c₀, cs, ⟨hcs, hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h h₂.ne'
  simp +decide only [hcs, hecs, h, h₂, signVariations, List.destutter, List.map_cons, sign_pos,
    List.filter_cons_of_pos, tsub_le_iff_right,
    Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  rw [List.filter_cons]
  split; swap --does c₀ = 0? If so, the trailing nonzero coefficient lists are identical.
  · rfl
  rw [List.destutter'_cons]
  split; swap --does SignType.sign c₀ = 1? If so, the destutter doesn't care about it.
  · rfl
  rcases hcs : (cs.map SignType.sign).filter fun x ↦ decide (x ≠ 0) with _ | ⟨r, rs⟩
  · simp
  · rw [← List.destutter_cons', ← List.destutter_cons']
    grind [List.destutter_cons_cons]

-- TODO: fix non-terminal simp below; simp followed by rfl
set_option linter.flexible false in
/-- Multiplying a polynomial by a linear term `X - η` adds at least one sign change. This is the
basis for the induction in `roots_countP_pos_le_signVariations`. -/
/-
**Polynomial.succ_signVariations_le_X_sub_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P != 0) : signVariat
ions P + 1 <= signVariations ((X - C η) * P)
参数：hη : 0 < η；hP : P != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_X_sub_C_mul`：coeff_X_sub_C_mul {p : R[X]} {r : R} {a : 
Nat} : coeff ((X - C r) * p) (a + 1) = coeff p a - r * coeff p (a + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.withBotSucc_degree_eq_natDegree_add_one`：withBotSucc_degree_e
q_natDegree_add_one (h : p != 0) : p.degree.succ = p.natDegree + 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.destutter.congr_simp`：∀ {α : Type u_1} (R R_1 : α → α → Prop),   R 
= R_1 →     ∀ {inst : DecidableRel R} [inst_1 : DecidableRel R_1] (a a_1 : List 
α),       a = a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
Multiplying a polynomial by a linear term `X - η` adds at least one sign change.
 This is the
basis for the induction in `roots_countP_pos_le_signVariations`.
-/
theorem succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P ≠ 0) :
    signVariations P + 1 ≤ signVariations ((X - C η) * P) := by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with | _ d ih =>
  -- can assume it starts positive, otherwise negate P
  wlog h_lC : 0 < leadingCoeff P generalizing P with H
  · simpa using @H (-P) (by simpa) (by simpa) (by grind [leadingCoeff_eq_zero, leadingCoeff_neg])
  --Adding a new root doesn't make the product zero, and increases degree by exactly one.
  have h_mul : (X - C η) * P ≠ 0 := mul_ne_zero (X_sub_C_ne_zero η) hP
  have h_deg_mul : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hP, natDegree_X_sub_C, add_comm]
  rcases d with _ | d
  · --P is zero degree, therefore a constant.
    have hcQ : 0 < coeff P 0 := by grind [leadingCoeff]
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      simp_all [coeff_X_sub_C_mul, coeff_eq_zero_of_natDegree_lt]
    dsimp [signVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hP, withBotSucc_degree_eq_natDegree_add_one h_mul]
    simp [h_deg_mul, hxcQ, hη, hcQ, hd, List.range_succ]
  -- P is positive degree. Set up some temporary variables for signs for the nextCoeffs.
  generalize hs_nC : SignType.sign P.nextCoeff = s_nC
  generalize hs_nC_mul : SignType.sign ((X - C η) * P).nextCoeff = s_nC_mul
  --We're really doing induction on `P.eraseLead` in a sense
  have h_ih : P.eraseLead.natDegree < d + 1 := by grind [eraseLead_natDegree_le]
  have h_mul_lC : SignType.sign ((X - C η) * P).leadingCoeff = 1 := by simp [h_lC]
  have h_ηP : 0 < η * coeff P (d + 1) := by grind [leadingCoeff, mul_pos]
  rcases s_nC.trichotomy with rfl | rfl | rfl; rotate_left
  · -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    obtain rfl : s_nC_mul = -1 := by
      have : coeff P d = 0 := by simpa [nextCoeff, hd] using hs_nC
      simp [*, ← hs_nC_mul, nextCoeff, coeff_X_sub_C_mul]
    /- We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
      hypothesis on eraseLead P. but that isn't actually true: we could have P a monomial
      and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
      true as written for P ≠ 0.) So we need to do a case-split and handle this separately. -/
    by_cases eraseLead P = 0
    · grind [succ_signVariations_X_sub_C_mul_monomial,
        eraseLead_add_monomial_natDegree_leadingCoeff, zero_add]
    · /- Dropping the lead of the product exactly drops the first two of the eraseLead. This
        decreases the sign variations of the eraseLead by at least one, and of the product by at
       most one, so we can induct. -/
      have : signVariations ((X - C η) * P).eraseLead + 1 =
          signVariations ((X - C η) * P) := by
        simp [-leadingCoeff_mul, ← sign_ne_zero,
          signVariations_eq_eraseLead_add_ite h_mul, leadingCoeff_eraseLead_eq_nextCoeff,
          hs_nC_mul, h_mul_lC]
      have : ((X - C η) * P.eraseLead).signVariations ≤
          ((X - C η) * P).eraseLead.signVariations := by
        have := signVariations_eraseLead_le (eraseLead ((X - C η) * P))
        rwa [← eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne']
        grind [sign_eq_zero_iff]
      grind [signVariations_le_eraseLead_succ]
  all_goals (
    have h₁ : nextCoeff P ≠ 0 := by simp [← sign_ne_zero, hs_nC]
    specialize ih _ h_ih (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl
    have : P.signVariations = P.eraseLead.signVariations + ?_ := by
      simp [signVariations_eq_eraseLead_add_ite hP, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        hs_nC, h_lC]
      exact rfl)
  · /- P starts with [+,+,...]. (X-C)*P starts with [+,?,...]. After dropping the lead of P, this
      becomes [+,...] and [+,...]. So the sign variations on P are unchanged when we induct, while
      (X-C)*P can only lose at most one sign change. -/
    grind [sign_eq_one_iff, signVariations_X_sub_C_mul_eraseLead_le]
  · /- P starts with [+,-,...], so (X-C)*P starts with [+,-,...]. After dropping the lead of P, this
    becomes [-,...] and [-,...]. Dropping the first one of each decreases (X-C)*P by one and P by
    one, so we can induct. -/
    trans ((X - C η) * P).eraseLead.signVariations + 1
    · grind [signVariations_eraseLead_mul_X_sub_C, sign_eq_neg_one_iff]
    · suffices SignType.sign ((X - C η) * P).nextCoeff = -1 by
        simp +decide [signVariations_eq_eraseLead_add_ite h_mul, h_lC,
          leadingCoeff_eraseLead_eq_nextCoeff, ← sign_eq_zero_iff, this]
      grind [← sign_eq_neg_one_iff, coeff_X_sub_C_mul, nextCoeff]

end StrictOrderedRing
section CommStrictOrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (P : Polynomial R)

/-- **Descartes' Rule of Signs**: the number of positive roots is at most the number of sign
variations. -/
/-
**Polynomial.roots_countP_pos_le_signVariations** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) <= signVariati
ons P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Polynomial.isRoot_of_mem_roots`：isRoot_of_mem_roots (h : a in p.roots) :
 IsRoot p a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.countP.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `Polynomial.ne_zero_of_mem_roots`：ne_zero_of_mem_roots (h : a in p.roots)
 : p != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Multiset.countP_cons_of_pos`：countP_cons_of_pos {a : α} (s) : p a -> cou
ntP p (a ::ₘ s) = countP p s + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.succ_signVariations_le_X_sub_C_mul`：succ_signVariations_le_X_
sub_C_mul (hη : 0 < η) (hP : P != 0) : signVariations P + 1 <= signVariations ((
X - C η) * P)
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0

--- 原说明 ---
**Descartes' Rule of Signs**: the number of positive roots is at most the number
 of sign
variations.
-/
theorem roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) ≤ signVariations P := by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P -- Induct on number of roots.
  · exact zero_le
  rename_i ih
  have hp : P ≠ 0 := by grind [roots_zero, Multiset.countP_zero]
  -- we can take a positive root, η, because the number of roots is positive
  obtain ⟨η, η_root, η_pos⟩ : ∃ x, x ∈ P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  -- (X - η) divides P(X), so write P(X) = (X - η) * Q(X)
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  -- P has at least num_roots sign variations
  grw [ih Q, succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]

end CommStrictOrderedRing
end Polynomial

