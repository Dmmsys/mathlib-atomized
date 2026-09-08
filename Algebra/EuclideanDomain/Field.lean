/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Instances for Euclidean domains

* `Field.toEuclideanDomain`: shows that any field is a Euclidean domain.
-/

public section

namespace Field

variable {K : Type*} [Field K]

-- see Note [lower instance priority]
/-
**Field.** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toEuclideanDomain : EuclideanDomain K :=
{ toCommRing := toCommRing
  quotient := (· / ·), remainder := fun a b => a - a * b / b, quotient_zero := div_zero,
  quotient_mul_add_remainder_eq := fun a b => by
    by_cases h : b = 0 <;> simp [h, mul_div_cancel₀]
  r := fun a b => a = 0 ∧ b ≠ 0,
  r_wellFounded :=
    WellFounded.intro fun _ =>
      (Acc.intro _) fun _ ⟨hb, _⟩ => (Acc.intro _) fun _ ⟨_, hnb⟩ => False.elim <| hnb hb,
  remainder_lt := fun a b hnb => by simp [hnb],
  mul_left_not_lt := fun _ _ hnb ⟨hab, hna⟩ => Or.casesOn (mul_eq_zero.1 hab) hna hnb }

@[simp]
/-
**Field.mod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (a b : K), a % b = a - a * b / b
参数：a b : K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem mod_eq (a b : K) : a % b = a - a * b / b := rfl

@[simp]
/-
**Field.gcd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K] (a b : K), Eucl
ideanDomain.gcd a b = if a = 0 then b else a
参数：a b : K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd.eq_def`：∀ {R : Type u} [inst : EuclideanDomain R] [i
nst_1 : DecidableEq R] (a b : R),   EuclideanDomain.gcd a b =     if a0 : a = 0 
then b     else …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
-/
protected theorem gcd_eq [DecidableEq K] (a b : K) :
    EuclideanDomain.gcd a b = if a = 0 then b else a := by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]
/-
**Field.gcd_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K] (b : K), Euclid
eanDomain.gcd 0 b = b
参数：b : K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.gcd_eq`：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K]
 (a b : K), EuclideanDomain.gcd a b = if a = 0 then b else a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
protected theorem gcd_zero_eq [DecidableEq K] (b : K) :
    EuclideanDomain.gcd 0 b = b := by
  rw [Field.gcd_eq, if_pos rfl]
/-
**Field.gcd_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K] {a : K}, a ≠ 0 
→ ∀ (b : K), EuclideanDomain.gcd a b = a
参数：b : K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.gcd_eq`：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K]
 (a b : K), EuclideanDomain.gcd a b = if a = 0 then b else a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
protected theorem gcd_eq_of_ne [DecidableEq K] {a : K} (ha : a ≠ 0) (b : K) :
    EuclideanDomain.gcd a b = a := by
  rw [Field.gcd_eq, if_neg ha]

end Field

