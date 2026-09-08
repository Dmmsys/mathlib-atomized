/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Additive characters valued in the unit circle

This file defines additive characters, valued in the unit circle, from either
* the ring `ZMod N` for any non-zero natural `N`,
* the additive circle `ℝ / T ⬝ ℤ`, for any real `T`.

These results are separate from `Analysis.SpecialFunctions.Complex.Circle` in order to reduce
the imports of that file.
-/

@[expose] public section

open Complex Function

open scoped Real

/-- The canonical map from the additive to the multiplicative circle, as an `AddChar`. -/
/-
**AddCircle.toCircle_addChar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCircle.toCircle_addChar {T : Real} : AddChar (AddCircle T) Circle where
 toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.toCircle_zero`：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
· 使用定理 `AddCircle.toCircle_add`：toCircle_add (x y : AddCircle T) : toCircle (x +
 y) = toCircle x * toCircle y

--- 原说明 ---
The canonical map from the additive to the multiplicative circle, as an `AddChar
`.
-/
noncomputable def AddCircle.toCircle_addChar {T : ℝ} : AddChar (AddCircle T) Circle where
  toFun := toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

open AddCircle

namespace ZMod

/-!
### Additive characters valued in the complex circle
-/

open scoped Real

variable {N : ℕ} [NeZero N]

/-- The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N` to
`exp (2 * π * I * j / N)`. -/
/-
**ZMod.toCircle** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：toCircle : AddChar (ZMod N) Circle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N
` to
`exp (2 * π * I * j / N)`.
-/
noncomputable def toCircle : AddChar (ZMod N) Circle :=
  toCircle_addChar.compAddMonoidHom toAddCircle
/-
**ZMod.toCircle_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toCircle_intCast (j : Int) : toCircle (j : ZMod N) = exp (2 * π * I * j / 
N)
参数：j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.toCircle.eq_1`：∀ {N : ℕ} [inst : NeZero N], ZMod.toCircle = AddCirc
le.toCircle_addChar.compAddMonoidHom ZMod.toAddCircle
· 使用定理 `AddChar.compAddMonoidHom_apply`：∀ {A : Type u_1} {B : Type u_2} {M : Typ
e u_3} [inst : AddMonoid A] [inst_1 : AddMonoid B] [inst_2 : Monoid M]   (ψ : Ad
dChar B M) (f : A →+…
· 使用定理 `AddCircle.toCircle_zero`：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
· 使用定理 `AddCircle.toCircle_add`：toCircle_add (x y : AddCircle T) : toCircle (x +
 y) = toCircle x * toCircle y
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddCircle.toCircle_addChar.eq_1`：∀ {T : ℝ}, AddCircle.toCircle_addChar =
 { toFun := AddCircle.toCircle, map_zero_eq_one' := ⋯, map_add_eq_mul' := ⋯ }
· 使用定理 `AddChar.coe_mk`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [in
st_1 : Monoid M] (f : A → M) (map_zero_eq_one' : f 0 = 1)   (map_add_eq_mul' : ∀
 (a …
· 使用定理 `AddCircle.scaled_exp_map_periodic`：scaled_exp_map_periodic : Function.Pe
riodic (fun x => Circle.exp (2 * π / T * x)) T
· 使用定理 `AddCircle.toCircle.eq_1`：∀ {T : ℝ}, AddCircle.toCircle = ⋯.lift
· 使用引理 `ZMod.toAddCircle_intCast`：toAddCircle_intCast (j : Int) : toAddCircle (j
 : ZMod N) = ↑(j / N : Real)
· 使用定理 `Function.Periodic.lift_coe`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{c : α} [inst : AddGroup α] (h : Function.Periodic f c) (a : α),   h.lift ↑a = f
 a
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 51 条，此处仅展示前 30 条）
-/
lemma toCircle_intCast (j : ℤ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  rw [toCircle, AddChar.compAddMonoidHom_apply, toCircle_addChar, AddChar.coe_mk,
    AddCircle.toCircle, toAddCircle_intCast, Function.Periodic.lift_coe, Circle.coe_exp]
  push_cast
  ring_nf
/-
**ZMod.toCircle_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toCircle_natCast (j : Nat) : toCircle (j : ZMod N) = exp (2 * π * I * j / 
N)
参数：j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ZMod.toCircle_intCast`：toCircle_intCast (j : Int) : toCircle (j : ZMod N
) = exp (2 * π * I * j / N)
-/
lemma toCircle_natCast (j : ℕ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  simpa using toCircle_intCast (N := N) j

/--
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMod.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toCircle_intCast` instead.
-/
/-
**ZMod.toCircle_apply** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toCircle_apply (j : ZMod N) : toCircle j = exp (2 * π * I * j.val / N)
参数：j : ZMod N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ZMod.toCircle_natCast`：toCircle_natCast (j : Nat) : toCircle (j : ZMod N
) = exp (2 * π * I * j / N)
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a

--- 原说明 ---
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMo
d.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toCircle_intCast` instea
d.
-/
lemma toCircle_apply (j : ZMod N) :
    toCircle j = exp (2 * π * I * j.val / N) := by
  rw [← toCircle_natCast, natCast_zmod_val]
/-
**ZMod.toCircle_eq_circleExp** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toCircle_eq_circleExp (j : ZMod N) : toCircle j = Circle.exp (2 * π * (j.v
al / N))
参数：j : ZMod N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.toCircle_apply`：toCircle_apply (j : ZMod N) : toCircle j = exp (2 *
 π * I * j.val / N)
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
（共 35 条，此处仅展示前 30 条）
-/
lemma toCircle_eq_circleExp (j : ZMod N) :
    toCircle j = Circle.exp (2 * π * (j.val / N)) := by
  ext
  rw [toCircle_apply, Circle.coe_exp]
  push_cast
  congr; ring
/-
**ZMod.injective_toCircle** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：injective_toCircle : Injective (toCircle : ZMod N -> Circle)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddCircle.injective_toCircle`：injective_toCircle (hT : T != 0) : Functio
n.Injective (@toCircle T)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `ZMod.toAddCircle_injective`：toAddCircle_injective : Function.Injective (
toAddCircle : ZMod N -> _)
-/
lemma injective_toCircle : Injective (toCircle : ZMod N → Circle) :=
  (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

/-- The additive character from `ZMod N` to `ℂ`, sending `j mod N` to `exp (2 * π * I * j / N)`. -/
/-
**ZMod.stdAddChar** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：stdAddChar : AddChar (ZMod N) Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive character from `ZMod N` to `ℂ`, sending `j mod N` to `exp (2 * π * 
I * j / N)`.
-/
noncomputable def stdAddChar : AddChar (ZMod N) ℂ := Circle.coeHom.compAddChar toCircle

set_option backward.isDefEq.respectTransparency.types false in
/-
**ZMod.stdAddChar_coe** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：stdAddChar_coe (j : Int) : stdAddChar (j : ZMod N) = exp (2 * π * I * j / 
N)
参数：j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.coeHom_apply`：∀ (self : ↥(Submonoid.unitSphere ℂ)), Circle.coeHom
 self = ↑self
· 使用引理 `ZMod.toCircle_intCast`：toCircle_intCast (j : Int) : toCircle (j : ZMod N
) = exp (2 * π * I * j / N)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by simp [stdAddChar, toCircle_intCast]
/-
**ZMod.stdAddChar_apply** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j)
参数：j : ZMod N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j) := rfl
/-
**ZMod.injective_stdAddChar** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：injective_stdAddChar : Injective (stdAddChar : AddChar (ZMod N) Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用引理 `ZMod.injective_toCircle`：injective_toCircle : Injective (toCircle : ZMod
 N -> Circle)
-/
lemma injective_stdAddChar : Injective (stdAddChar : AddChar (ZMod N) ℂ) :=
  Subtype.coe_injective.comp injective_toCircle

/-- The standard additive character `ZMod N → ℂ` is primitive. -/
/-
**ZMod.isPrimitive_stdAddChar** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：isPrimitive_stdAddChar (N : Nat) [NeZero N] : (stdAddChar (N
参数：N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.zmod_char_primitive_of_eq_one_only_at_zero`：zmod_char_primitive_
of_eq_one_only_at_zero (n : Nat) (ψ : AddChar (ZMod n) C) (hψ : forall a, ψ a = 
1 -> a = 0) : IsPrimitive ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ZMod.injective_stdAddChar`：injective_stdAddChar : Injective (stdAddChar 
: AddChar (ZMod N) Complex)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1

--- 原说明 ---
The standard additive character `ZMod N → ℂ` is primitive.
-/
lemma isPrimitive_stdAddChar (N : ℕ) [NeZero N] :
    (stdAddChar (N := N)).IsPrimitive := by
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht ↦ ?_)
  rwa [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff] at ht

/-- `ZMod.toCircle` as an `AddChar` into `rootsOfUnity n Circle`. -/
/-
**ZMod.rootsOfUnityAddChar** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：rootsOfUnityAddChar (n : Nat) [NeZero n] : AddChar (ZMod n) (rootsOfUnity 
n Circle) where toFun x
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZMod.toCircle` as an `AddChar` into `rootsOfUnity n Circle`.
-/
noncomputable def rootsOfUnityAddChar (n : ℕ) [NeZero n] :
    AddChar (ZMod n) (rootsOfUnity n Circle) where
  toFun x := ⟨toUnits (ZMod.toCircle x), by ext; simp [← AddChar.map_nsmul_eq_pow]⟩
  map_zero_eq_one' := by simp
  map_add_eq_mul' _ _ := by ext; simp [AddChar.map_add_eq_mul]
/-
**ZMod.rootsOfUnityAddChar_val** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ) [inst : NeZero n] (x : ZMod n), ↑↑((ZMod.rootsOfUnityAddChar n) 
x) = ZMod.toCircle x
参数：n : ℕ；x : ZMod n；(ZMod.rootsOfUnityAddChar n) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rootsOfUnityAddChar_val (n : ℕ) [NeZero n] (x : ZMod n) :
    (rootsOfUnityAddChar n x).val = toCircle x := by
  rfl

end ZMod

variable (n : ℕ) [NeZero n]

/-- Interpret `n`-th roots of unity in `ℂ` as elements of the circle -/
/-
**rootsOfUnitytoCircle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootsOfUnitytoCircle : (rootsOfUnity n Complex) ->* Circle where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `n`-th roots of unity in `ℂ` as elements of the circle
-/
noncomputable def rootsOfUnitytoCircle : (rootsOfUnity n ℂ) →* Circle where
  toFun := fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Equivalence of the nth roots of unity of the Circle with nth roots of unity of the complex
numbers -/
/-
**rootsOfUnityCircleEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n Complex 
where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence of the nth roots of unity of the Circle with nth roots of unity of t
he complex
numbers
-/
noncomputable def rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := (rootsOfUnityUnitsMulEquiv ℂ n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity', MonoidHom.coe_toHomUnits, ← map_pow, ← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasEnoughRootsOfUnity Circle n := (rootsOfUnityCircleEquiv n).symm.hasEnoughRootsOfUnity
/-
**rootsOfUnityCircleEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (n : ℕ) [inst : NeZero n] (w : ↥(rootsOfUnity n Circle)), ↑↑((rootsOfUni
tyCircleEquiv n) w) = ↑↑↑w
参数：n : ℕ；w : ↥(rootsOfUnity n Circle)；(rootsOfUnityCircleEquiv n) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rootsOfUnityCircleEquiv_apply (w : rootsOfUnity n Circle) :
    ((rootsOfUnityCircleEquiv n w).val : ℂ) = ((w.val : Circle) : ℂ) :=
  rfl

open Real in
/-
**rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val (j : ZMod n) : (roots
OfUnityCircleEquiv n (ZMod.rootsOfUnityAddChar n j)).val = Complex.exp (2 * π * 
I * j.val / n)
参数：j : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.rootsOfUnityAddChar_val`：∀ (n : ℕ) [inst : NeZero n] (x : ZMod n), 
↑↑((ZMod.rootsOfUnityAddChar n) x) = ZMod.toCircle x
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val (j : ZMod n) :
    (rootsOfUnityCircleEquiv n (ZMod.rootsOfUnityAddChar n j)).val
      = Complex.exp (2 * π * I * j.val / n) := by
  simp [← ZMod.toCircle_natCast, -ZMod.natCast_val, ZMod.natCast_zmod_val]
/-
**surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar (n : Nat) [NeZ
ero n] : Surjective (rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.mem_rootsOfUnity`：∀ (n : ℕ) [NeZero n] (x : ℂˣ), x ∈ rootsOfUnit
y n ℂ ↔ ∃ i < n, Complex.exp (2 * ↑Real.pi * Complex.I * (↑i / ↑n)) = ↑x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.rootsOfUnityAddChar_val`：∀ (n : ℕ) [inst : NeZero n] (x : ZMod n), 
↑↑((ZMod.rootsOfUnityAddChar n) x) = ZMod.toCircle x
· 使用引理 `ZMod.toCircle_natCast`：toCircle_natCast (j : Nat) : toCircle (j : ZMod N
) = exp (2 * π * I * j / N)
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar (n : ℕ) [NeZero n] :
    Surjective (rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n) := fun ⟨w, hw⟩ ↦ by
  obtain ⟨j, hj1, hj2⟩ := (Complex.mem_rootsOfUnity n w).mp hw
  exact ⟨j, by simp [Units.ext_iff, Subtype.ext_iff, ← hj2, ZMod.toCircle_natCast, mul_div_assoc]⟩
/-
**bijective_rootsOfUnityAddChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bijective_rootsOfUnityAddChar : Bijective (ZMod.rootsOfUnityAddChar n) whe
re left _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddChar.coe_mk`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [in
st_1 : Monoid M] (f : A → M) (map_zero_eq_one' : f 0 = 1)   (map_add_eq_mul' : ∀
 (a …
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ZMod.injective_toCircle`：injective_toCircle : Injective (toCircle : ZMod
 N -> Circle)
· 使用定理 `Function.Surjective.of_comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Injec
tive f → Function.Surj…
· 使用定理 `surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar`：surjective_
rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar (n : Nat) [NeZero n] : Surjecti
ve (rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnity…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
lemma bijective_rootsOfUnityAddChar :
    Bijective (ZMod.rootsOfUnityAddChar n) where
  left _ _ := by simp [ZMod.rootsOfUnityAddChar, ZMod.injective_toCircle.eq_iff]
  right := (surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar n).of_comp_left
    (rootsOfUnityCircleEquiv n).injective
