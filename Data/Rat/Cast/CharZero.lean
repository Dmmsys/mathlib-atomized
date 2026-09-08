/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Casts of rational numbers into characteristic zero fields (or division rings).
-/

@[expose] public section

open Function

variable {F ι α β : Type*}

namespace Rat
variable [DivisionRing α] [CharZero α] {p q : ℚ}

@[stacks 09FR "Characteristic zero case."]
/-
**Rat.cast_injective** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_injective : Injective ((↑) : Rat -> α) | ⟨n₁, d₁, d₁0, c₁⟩, ⟨n₂, d₂, 
d₂0, c₂⟩, h => by have d₁a : (d₁ : α) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.mkRat_eq_iff`：∀ {d₁ d₂ : ℕ} {n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (mkRat n₁
 d₁ = mkRat n₂ d₂ ↔ n₁ * ↑d₂ = n₂ * ↑d₁)
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.inv_left₀`：inv_left₀ (h : Commute a b) : Commute a⁻¹ b
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Rat.cast_divInt_of_ne_zero`：cast_divInt_of_ne_zero (a : Int) {b : Int} (
b0 : (b : α) != 0) : (a /. b : α) = a / b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma cast_injective : Injective ((↑) : ℚ → α)
  | ⟨n₁, d₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk_eq_divInt, mk_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero _ (by simpa), cast_divInt_of_ne_zero _ (by simpa)] at h
    norm_cast at h
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.eq,
      ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_natCast d₁,
      ← Int.cast_mul, ← Int.cast_natCast d₂, ← Int.cast_mul, Int.cast_inj, ← mkRat_eq_iff d₁0 d₂0]
      at h
/-
**Rat.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] {p q : ℚ}, ↑p = ↑q ↔
 p = q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Rat.cast_injective`：cast_injective : Injective ((↑) : Rat -> α) | ⟨n₁, d
₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by have d₁a : (d₁ : α) != 0
-/
@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff
/-
**Rat.cast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] {p : ℚ}, ↑p = 0 ↔ p 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用引理 `Rat.cast_injective`：cast_injective : Injective ((↑) : Rat -> α) | ⟨n₁, d
₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by have d₁a : (d₁ : α) != 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
-/
@[simp, norm_cast] lemma cast_eq_zero : (p : α) = 0 ↔ p = 0 := cast_injective.eq_iff' cast_zero
/-
**Rat.cast_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_ne_zero : (p : α) != 0 ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Rat.cast_eq_zero`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] 
{p : ℚ}, ↑p = 0 ↔ p = 0
-/
lemma cast_ne_zero : (p : α) ≠ 0 ↔ p ≠ 0 := cast_eq_zero.ne
/-
**Rat.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q : ℚ), ↑(p + q) 
= ↑p + ↑q
参数：p q : ℚ；p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.cast_add_of_ne_zero`：cast_add_of_ne_zero {q r : Rat} (hq : (q.den : 
α) != 0) (hr : (r.den : α) != 0) : (q + r : Rat) = (q + r : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
-/
@[simp, norm_cast] lemma cast_add (p q : ℚ) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')
/-
**Rat.cast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q : ℚ), ↑(p - q) 
= ↑p - ↑q
参数：p q : ℚ；p - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_sub_of_ne_zero`：∀ {α : Type u_3} [inst : DivisionRing α] {p q :
 ℚ}, ↑p.den ≠ 0 → ↑q.den ≠ 0 → ↑(p - q) = ↑p - ↑q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
-/
@[simp, norm_cast] lemma cast_sub (p q : ℚ) : ↑(p - q) = (p - q : α) :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')
/-
**Rat.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q : ℚ), ↑(p * q) 
= ↑p * ↑q
参数：p q : ℚ；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_mul_of_ne_zero`：∀ {α : Type u_3} [inst : DivisionRing α] {p q :
 ℚ}, ↑p.den ≠ 0 → ↑q.den ≠ 0 → ↑(p * q) = ↑p * ↑q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
-/
@[simp, norm_cast] lemma cast_mul (p q : ℚ) : ↑(p * q) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

variable (α) in
/-- Coercion `ℚ → α` as a `RingHom`. -/
/-
**Rat.castHom** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：castHom : Rat ->+* α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q

--- 原说明 ---
Coercion `ℚ → α` as a `RingHom`.
-/
def castHom : ℚ →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add
/-
**Rat.coe_castHom** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [inst_1 : CharZero α], ⇑(Rat.cast
Hom α) = Rat.cast
参数：Rat.castHom α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ → α) := rfl
/-
**Rat.cast_inv** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p : ℚ), ↑p⁻¹ = (↑p)
⁻¹
参数：p : ℚ；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
@[simp, norm_cast] lemma cast_inv (p : ℚ) : ↑(p⁻¹) = (p⁻¹ : α) := map_inv₀ (castHom α) _
/-
**Rat.cast_div** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q : ℚ), ↑(p / q) 
= ↑p / ↑q
参数：p q : ℚ；p / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
@[simp, norm_cast] lemma cast_div (p q : ℚ) : ↑(p / q) = (p / q : α) := map_div₀ (castHom α) ..

@[simp, norm_cast]
/-
**Rat.cast_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_zpow (p : Rat) (n : Int) : ↑(p ^ n) = (p ^ n : α)
参数：p : Rat；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma cast_zpow (p : ℚ) (n : ℤ) : ↑(p ^ n) = (p ^ n : α) := map_zpow₀ (castHom α) ..

@[norm_cast]
/-
**Rat.cast_divInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_divInt (a b : Int) : (a /. b : α) = a / b
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_divInt (a b : ℤ) : (a /. b : α) = a / b := by
  simp only [divInt_eq_div, cast_div, cast_intCast]

end Rat

namespace NNRat
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

/-
**NNRat.cast_injective** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_injective : Injective ((↑) : Rat>=0 -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.num_div_den`：num_div_den (q : Rat>=0) : (q.num : Rat>=0) / q.den =
 q
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNRat.den_ne_zero`：∀ (q : ℚ≥0), q.den ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Commute.div_eq_div_iff`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a b
 c d : G₀},   Commute b d → b ≠ 0 → d ≠ 0 → (a / b = c / d ↔ a * d = c * b)
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
-/
lemma cast_injective : Injective ((↑) : ℚ≥0 → α) := by
  rintro p q hpq
  rw [NNRat.cast_def, NNRat.cast_def, Commute.div_eq_div_iff] at hpq
  on_goal 1 => rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  · norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals apply den_ne_zero
  exact Nat.cast_commute ..
/-
**NNRat.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α] {p q : ℚ≥0}, ↑p 
= ↑q ↔ p = q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `NNRat.cast_injective`：cast_injective : Injective ((↑) : Rat>=0 -> α)
-/
@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff
/-
**NNRat.cast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α] {q : ℚ≥0}, ↑q = 
0 ↔ q = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `NNRat.cast_inj`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] {p q : ℚ≥0}, ↑p = ↑q ↔ p = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma cast_eq_zero : (q : α) = 0 ↔ q = 0 := by rw [← cast_zero, cast_inj]
/-
**NNRat.cast_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_ne_zero : (q : α) != 0 ↔ q != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NNRat.cast_eq_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZe
ro α] {q : ℚ≥0}, ↑q = 0 ↔ q = 0
-/
lemma cast_ne_zero : (q : α) ≠ 0 ↔ q ≠ 0 := cast_eq_zero.not
/-
**NNRat.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α] (p q : ℚ≥0), ↑(p
 + q) = ↑p + ↑q
参数：p q : ℚ≥0；p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNRat.cast_add_of_ne_zero`：cast_add_of_ne_zero (hq : (q.den : α) != 0) (
hr : (r.den : α) != 0) : ↑(q + r) = (q + r : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNRat.den_pos`：∀ (q : ℚ≥0), 0 < q.den
-/
@[simp, norm_cast] lemma cast_add (p q : ℚ≥0) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')
/-
**NNRat.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α] (p q : ℚ≥0), ↑(p
 * q) = ↑p * ↑q
参数：p q : ℚ≥0；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNRat.cast_mul_of_ne_zero`：cast_mul_of_ne_zero (hq : (q.den : α) != 0) (
hr : (r.den : α) != 0) : ↑(q * r) = (q * r : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNRat.den_pos`：∀ (q : ℚ≥0), 0 < q.den
-/
@[simp, norm_cast] lemma cast_mul (p q) : (p * q : ℚ≥0) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

variable (α) in
/-- Coercion `ℚ≥0 → α` as a `RingHom`. -/
/-
**NNRat.castHom** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：castHom : Rat>=0 ->+* α where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
· 使用定理 `NNRat.cast_mul`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p * q) = ↑p * ↑q
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `NNRat.cast_add`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p + q) = ↑p + ↑q

--- 原说明 ---
Coercion `ℚ≥0 → α` as a `RingHom`.
-/
def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add
/-
**NNRat.coe_castHom** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [inst_1 : CharZero α], ⇑(NNRa
t.castHom α) = NNRat.cast
参数：NNRat.castHom α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_castHom : ⇑(castHom α) = (↑) := rfl
/-
**NNRat.cast_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α] (p : ℚ≥0), ↑p⁻¹ 
= (↑p)⁻¹
参数：p : ℚ≥0；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
@[simp, norm_cast] lemma cast_inv (p) : (p⁻¹ : ℚ≥0) = (p : α)⁻¹ := map_inv₀ (castHom α) _
/-
**NNRat.cast_div** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α] (p q : ℚ≥0), ↑(p
 / q) = ↑p / ↑q
参数：p q : ℚ≥0；p / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
@[simp, norm_cast] lemma cast_div (p q) : (p / q : ℚ≥0) = (p / q : α) := map_div₀ (castHom α) ..

@[simp, norm_cast]
/-
**NNRat.cast_zpow** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_zpow (q : Rat>=0) (p : Int) : ↑(q ^ p) = ((q : α) ^ p : α)
参数：q : Rat>=0；p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma cast_zpow (q : ℚ≥0) (p : ℤ) : ↑(q ^ p) = ((q : α) ^ p : α) := map_zpow₀ (castHom α) ..

@[simp]
/-
**NNRat.cast_divNat** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_divNat (a b : Nat) : (divNat a b : α) = a / b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `NNRat.cast_div`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `Rat.mkRat_eq_div`：∀ (a : ℤ) (b : ℕ), mkRat a b = ↑a / ↑b
-/
lemma cast_divNat (a b : ℕ) : (divNat a b : α) = a / b := by
  rw [← cast_natCast, ← cast_natCast b, ← cast_div]
  congr
  ext
  apply Rat.mkRat_eq_div

end NNRat

