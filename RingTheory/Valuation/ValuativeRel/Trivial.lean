/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!

# Trivial Valuative Relations

Trivial valuative relations relate all non-zero elements to each other. Equivalently,
all elements are related to `1`: the relation is equal to the relation induced
by the trivial valuation which sends all non-zero elements to `1`.

## TODO

A trivial valuative relation is equivalent to the value group being isomorphic to `WithZero Unit`.

-/

@[expose] public section

namespace ValuativeRel

variable {R Γ : Type} [Ring R] [DecidableEq R] [IsDomain R]
  [LinearOrderedCommGroupWithZero Γ]

open WithZero

/-- The trivial valuative relation on a domain `R`, such that all non-zero elements are related.
The domain condition is necessary so that the relation is closed when multiplying.
-/
@[instance_reducible]
/-
**ValuativeRel.trivialRel** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：trivialRel {R : Type} [Semiring R] [DecidableEq R] [IsDomain R] : Valuativ
eRel R where vle x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial valuative relation on a domain `R`, such that all non-zero elements 
are related.
The domain condition is necessary so that the relation is closed when multiplyin
g.
-/
def trivialRel {R : Type} [Semiring R] [DecidableEq R] [IsDomain R] : ValuativeRel R where
  vle x y := if y = 0 then x = 0 else True
  vle_total _ _ := by split_ifs <;> simp_all
  vle_trans _ _ := by split_ifs; simp_all
  vle_add _ _ := by split_ifs; simp_all
  mul_vle_mul_left _ _ := by split_ifs at * <;> simp_all
  vle_mul_cancel _ := by split_ifs <;> simp_all
  not_vle_one_zero := by split_ifs <;> simp_all
  vle_mul_comm {_ _} := by simpa using Or.symm
/-
**ValuativeRel.eq_trivialRel_of_compatible_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuat
iveRel`。
形式化陈述：eq_trivialRel_of_compatible_one [h : ValuativeRel R] [hv : Valuation.Compa
tible (1 : Valuation R Γ)] : h = trivialRel
参数：1 : Valuation R Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ValuativeRel.ext`：∀ {R : Type u_1} {inst : Semiring R} {x y : ValuativeR
el R}, ValuativeRel.vle = ValuativeRel.vle → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.Compatible.vle_iff_le`：∀ {R : Type u_1} {Γ : Type u_2} {inst :
 Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ} {v : Valuation R Γ}   {ins
t_2 : ValuativeRel R}…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Valuation.one_apply_of_ne_zero`：one_apply_of_ne_zero {x : R} (hx : x != 
0) : (1 : Valuation R Γ₀) x = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma eq_trivialRel_of_compatible_one [h : ValuativeRel R]
    [hv : Valuation.Compatible (1 : Valuation R Γ)] : h = trivialRel := by
  ext
  change _ ↔ if _ = 0 then _ else _
  rw [hv.vle_iff_le]
  split_ifs <;>
  simp_all [Valuation.one_apply_of_ne_zero, Valuation.one_apply_le_one]
/-
**ValuativeRel.trivialRel_eq_ofValuation_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuativ
eRel`。
形式化陈述：trivialRel_eq_ofValuation_one : trivialRel = ValuativeRel.ofValuation (1 :
 Valuation R Γ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ValuativeRel.eq_trivialRel_of_compatible_one`：eq_trivialRel_of_compatibl
e_one [h : ValuativeRel R] [hv : Valuation.Compatible (1 : Valuation R Γ)] : h =
 trivialRel
· 使用定理 `Valuation.Compatible.ofValuation`：∀ {S : Type u_3} {Γ : Type u_4} [inst 
: Ring S] [inst_1 : LinearOrderedCommGroupWithZero Γ] (v : Valuation S Γ),   v.C
ompatible
-/
lemma trivialRel_eq_ofValuation_one :
    trivialRel = ValuativeRel.ofValuation (1 : Valuation R Γ) := by
  convert! (eq_trivialRel_of_compatible_one (Γ := Γ)).symm
  exact Valuation.Compatible.ofValuation 1

variable (R Γ) in
/-
**ValuativeRel.subsingleton_units_valueGroupWithZero_of_trivialRel** 是 Mathlib 中
的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：subsingleton_units_valueGroupWithZero_of_trivialRel [ValuativeRel R] [Valu
ation.Compatible (1 : Valuation R Γ)] : Subsingleton (ValueGroupWithZero R)ˣ
参数：1 : Valuation R Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `ValuativeRel.isEquiv`：isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWi
thZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] (v₁ : Valuation R Γ₁) (v₂ : Valu
ation R Γ₂…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用引理 `ValuativeRel.exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq
`：exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (γ : (ValueGroupWi
thZero R)ˣ) : exists (a b : posSubmonoid R), valuation R a / v…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsEquiv.eq_iff`：eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = 
v₁ s ↔ v₂ r = v₂ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ValuativeRel.one_apply_posSubmonoid`：one_apply_posSubmonoid [Nontrivial 
R] [NoZeroDivisors R] [DecidablePred fun x : R => x = 0] (x : posSubmonoid R) : 
(1 : Valuation R Γ) x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subsingleton_units_valueGroupWithZero_of_trivialRel [ValuativeRel R]
    [Valuation.Compatible (1 : Valuation R Γ)] :
    Subsingleton (ValueGroupWithZero R)ˣ := by
  constructor
  intro a b
  have : (valuation R).IsEquiv (1 : Valuation R Γ) := isEquiv _ _
  obtain ⟨r, s, hr⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq a
  obtain ⟨t, u, ht⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq b
  rw [Units.ext_iff, ← hr, ← ht, div_eq_div_iff, ← map_mul, ← map_mul, this.eq_iff] <;>
  simp [one_apply_posSubmonoid]
/-
**ValuativeRel.not_isNontrivial_of_trivialRel** 是 Mathlib 中的一个引理，位于命名空间 `Valuati
veRel`。
形式化陈述：not_isNontrivial_of_trivialRel [ValuativeRel R] [Valuation.Compatible (1 :
 Valuation R Γ)] : ¬ IsNontrivial R
参数：1 : Valuation R Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `ValuativeRel.subsingleton_units_valueGroupWithZero_of_trivialRel`：subsin
gleton_units_valueGroupWithZero_of_trivialRel [ValuativeRel R] [Valuation.Compat
ible (1 : Valuation R Γ)] : Subsingleton (ValueGroupWi…
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma not_isNontrivial_of_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)] :
    ¬ IsNontrivial R := by
  rintro ⟨⟨x, hx, hx'⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp_all
  · simp_all [Subsingleton.elim u 1]
/-
**ValuativeRel.isDiscrete_trivialRel** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：isDiscrete_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuatio
n R Γ)] : IsDiscrete R
参数：1 : Valuation R Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用引理 `ValuativeRel.subsingleton_units_valueGroupWithZero_of_trivialRel`：subsin
gleton_units_valueGroupWithZero_of_trivialRel [ValuativeRel R] [Valuation.Compat
ible (1 : Valuation R Γ)] : Subsingleton (ValueGroupWi…
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Units.val_lt_val`：val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α
) < b ↔ a < b
-/
lemma isDiscrete_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)] :
    IsDiscrete R := by
  refine ⟨⟨0, zero_lt_one, fun x ↦ ?_⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp
  · rw [← Units.val_one, Units.val_lt_val]
    simp

end ValuativeRel

