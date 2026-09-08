/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `Circle.exp` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `Circle` and `ℝ`, see
`Circle.argPartialEquiv` and `Circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/

@[expose] public section


open Complex Function Set

open Real

namespace Circle

/-
**Circle.injective_arg** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：injective_arg : Injective fun z : Circle => arg z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.ext_norm_arg`：ext_norm_arg {x y : Complex} (h₁ : ‖x‖ = ‖y‖) (h₂ 
: x.arg = y.arg) : x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Circle.norm_coe`：norm_coe (z : Circle) : ‖(z : Complex)‖ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem injective_arg : Injective fun z : Circle => arg z := fun z w h =>
  Subtype.ext <| ext_norm_arg (z.norm_coe.trans w.norm_coe.symm) h

@[simp]
/-
**Circle.arg_eq_arg** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：arg_eq_arg {z w : Circle} : arg z = arg w ↔ z = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Circle.injective_arg`：injective_arg : Injective fun z : Circle => arg z
-/
theorem arg_eq_arg {z w : Circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff

@[simp]
/-
**Circle.arg_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：arg_eq_zero {z : Circle} : arg z = 0 ↔ z = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_one`：Complex.arg 1 = 0
· 使用定理 `Circle.arg_eq_arg`：arg_eq_arg {z w : Circle} : arg z = arg w ↔ z = w
-/
theorem arg_eq_zero {z : Circle} : arg z = 0 ↔ z = 1 := by
  simpa using arg_eq_arg (w := 1)
/-
**Circle.arg_exp** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：arg_exp {x : Real} (h₁ : -π < x) (h₂ : x <= π) : arg (exp x) = x
参数：h₁ : -π < x；h₂ : x <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `Complex.arg_cos_add_sin_mul_I`：arg_cos_add_sin_mul_I {θ : Real} (hθ : θ 
in Set.Ioc (-π) π) : arg (cos θ + sin θ * I) = θ
-/
theorem arg_exp {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (exp x) = x := by
  rw [coe_exp, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]

@[simp]
/-
**Circle.exp_arg** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：exp_arg (z : Circle) : exp (arg z) = z
参数：z : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.injective_arg`：injective_arg : Injective fun z : Circle => arg z
· 使用定理 `Circle.arg_exp`：arg_exp {x : Real} (h₁ : -π < x) (h₂ : x <= π) : arg (ex
p x) = x
· 使用定理 `Complex.neg_pi_lt_arg`：neg_pi_lt_arg (x : Complex) : -π < arg x
· 使用定理 `Complex.arg_le_pi`：arg_le_pi (x : Complex) : arg x <= π
-/
theorem exp_arg (z : Circle) : exp (arg z) = z :=
  injective_arg <| arg_exp (neg_pi_lt_arg _) (arg_le_pi _)

/-- `Complex.arg ∘ (↑)` and `Circle.exp` define a partial equivalence between `Circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`. -/
@[simps -fullyApplied]
/-
**Circle.argPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：argPartialEquiv : PartialEquiv Circle Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z

--- 原说明 ---
`Complex.arg ∘ (↑)` and `Circle.exp` define a partial equivalence between `Circl
e` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`.
-/
noncomputable def argPartialEquiv : PartialEquiv Circle ℝ where
  toFun := arg ∘ (↑)
  invFun := exp
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := exp_arg z
  right_inv' _ hx := arg_exp hx.1 hx.2

/-- `Complex.arg` and `Circle.exp ∘ (↑)` define an equivalence between `Circle` and `(-π, π]`. -/
@[simps -fullyApplied]
/-
**Circle.argEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：argEquiv : Circle ≃ Ioc (-π) π where toFun z
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `trivial`：True

--- 原说明 ---
`Complex.arg` and `Circle.exp ∘ (↑)` define an equivalence between `Circle` and 
`(-π, π]`.
-/
noncomputable def argEquiv : Circle ≃ Ioc (-π) π where
  toFun z := ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := exp ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
  right_inv x := Subtype.ext <| argPartialEquiv.right_inv x.2
/-
**Circle.leftInverse_exp_arg** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：leftInverse_exp_arg : LeftInverse exp (arg ∘ (↑))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z
-/
lemma leftInverse_exp_arg : LeftInverse exp (arg ∘ (↑)) := exp_arg
/-
**Circle.invOn_arg_exp** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：invOn_arg_exp : InvOn (arg ∘ (↑)) exp (Ioc (-π) π) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.invOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InvOn (↑e.symm) (↑e) e.source e.target
-/
lemma invOn_arg_exp : InvOn (arg ∘ (↑)) exp (Ioc (-π) π) univ := argPartialEquiv.symm.invOn
/-
**Circle.surjOn_exp_neg_pi_pi** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：surjOn_exp_neg_pi_pi : SurjOn exp (Ioc (-π) π) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.surjOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.SurjOn (↑e) e.source e.target
-/
lemma surjOn_exp_neg_pi_pi : SurjOn exp (Ioc (-π) π) univ := argPartialEquiv.symm.surjOn

set_option backward.isDefEq.respectTransparency false in
/-
**Circle.exp_eq_exp** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_eq_exp {x y : Real} : exp x = exp y ↔ exists m : Int, x = y + m * (2 *
 π)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `Complex.exp_eq_exp_iff_exists_int`：exp_eq_exp_iff_exists_int {x y : Comp
lex} : exp x = exp y ↔ exists n : Int, x = y + n * (2 * π * I)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exp_eq_exp {x y : ℝ} : exp x = exp y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, coe_exp, coe_exp, exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast
/-
**Circle.periodic_exp** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：periodic_exp : Periodic exp (2 * π)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ exists m : 
Int, x = y + m * (2 * π)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma periodic_exp : Periodic exp (2 * π) := fun z ↦ exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩
/-
**Circle.exp_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：Circle.exp (2 * Real.pi) = 1
参数：2 * Real.pi。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
-/
@[simp] lemma exp_two_pi : exp (2 * π) = 1 := periodic_exp.eq.trans exp_zero
/-
**Circle.exp_int_mul_two_pi** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_int_mul_two_pi (n : Int) : exp (n * (2 * π)) = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.exp_intCast_mul`：∀ (x : ℝ) (z : ℤ), Circle.exp (↑z * x) = Circle.
exp x ^ z
· 使用定理 `Circle.exp_two_pi`：Circle.exp (2 * Real.pi) = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exp_int_mul_two_pi (n : ℤ) : exp (n * (2 * π)) = 1 :=
  ext <| by simp
/-
**Circle.exp_two_pi_mul_int** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_two_pi_mul_int (n : Int) : exp (2 * π * n) = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Circle.exp_int_mul_two_pi`：exp_int_mul_two_pi (n : Int) : exp (n * (2 * 
π)) = 1
-/
lemma exp_two_pi_mul_int (n : ℤ) : exp (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n
/-
**Circle.exp_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_eq_one {r : Real} : exp r = 1 ↔ exists n : Int, r = n * (2 * π)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exp_eq_one {r : ℝ} : exp r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]
/-
**Circle.exp_inj** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_inj {r s : Real} : exp r = exp s ↔ r ≡ s [PMOD (2 * π)]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Circle.exp_sub`：∀ (x y : ℝ), Circle.exp (x - y) = Circle.exp x / Circle.
exp y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exp_inj {r s : ℝ} : exp r = exp s ↔ r ≡ s [PMOD (2 * π)] := by
  simp [AddCommGroup.modEq_iff_zsmul', ← exp_eq_one, div_eq_one, eq_comm (a := exp r)]
/-
**Circle.exp_sub_two_pi** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_sub_two_pi (x : Real) : exp (x - 2 * π) = exp x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (x : α), f (x - c) = f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)
-/
lemma exp_sub_two_pi (x : ℝ) : exp (x - 2 * π) = exp x := periodic_exp.sub_eq x
/-
**Circle.exp_add_two_pi** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_add_two_pi (x : Real) : exp (x + 2 * π) = exp x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)
-/
lemma exp_add_two_pi (x : ℝ) : exp (x + 2 * π) = exp x := periodic_exp x
/-
**Circle.exp_injOn_of_forall_sub_mem_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_injOn_of_forall_sub_mem_Ioo {s : Set Real} (hs : forall x in s, forall
 y in s, x - y in Ioo (-2 * π) (2 * π)) : InjOn exp s
参数：hs : forall x in s, forall y in s, x - y in Ioo (-2 * π) (2 * π)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Real.cos_eq_one_iff_of_lt_of_lt`：cos_eq_one_iff_of_lt_of_lt {x : Real} (
hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) : cos x = 1 ↔ x = 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.exp_ofReal_mul_I_re`：exp_ofReal_mul_I_re (x : Real) : (exp (x * 
I)).re = Real.cos x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Complex.exp_eq_exp_iff_exp_sub_eq_one`：exp_eq_exp_iff_exp_sub_eq_one {x 
y : Complex} : exp x = exp y ↔ exp (x - y) = 1
-/
lemma exp_injOn_of_forall_sub_mem_Ioo {s : Set ℝ}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Ioo (-2 * π) (2 * π)) : InjOn exp s := by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero, ← cos_eq_one_iff_of_lt_of_lt h1 h2, ← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one, ← sub_mul, ← ofReal_sub, Complex.ext_iff] at heq
  exact heq.1
/-
**Circle.exp_injOn_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_injOn_Icc {a b : Real} (h : b - a < 2 * π) : InjOn exp (Icc a b)
参数：h : b - a < 2 * π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.exp_injOn_of_forall_sub_mem_Ioo`：exp_injOn_of_forall_sub_mem_Ioo 
{s : Set Real} (hs : forall x in s, forall y in s, x - y in Ioo (-2 * π) (2 * π)
) : InjOn exp s
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 46 条，此处仅展示前 30 条）
-/
lemma exp_injOn_Icc {a b : ℝ} (h : b - a < 2 * π) : InjOn exp (Icc a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith
/-
**Circle.exp_injOn_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_injOn_Ico {a b : Real} (h : b - a <= 2 * π) : InjOn exp (Ico a b)
参数：h : b - a <= 2 * π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.exp_injOn_of_forall_sub_mem_Ioo`：exp_injOn_of_forall_sub_mem_Ioo 
{s : Set Real} (hs : forall x in s, forall y in s, x - y in Ioo (-2 * π) (2 * π)
) : InjOn exp s
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 48 条，此处仅展示前 30 条）
-/
lemma exp_injOn_Ico {a b : ℝ} (h : b - a ≤ 2 * π) : InjOn exp (Ico a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith
/-
**Circle.exp_injOn_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_injOn_Ioc {a b : Real} (h : b - a <= 2 * π) : InjOn exp (Ioc a b)
参数：h : b - a <= 2 * π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.exp_injOn_of_forall_sub_mem_Ioo`：exp_injOn_of_forall_sub_mem_Ioo 
{s : Set Real} (hs : forall x in s, forall y in s, x - y in Ioo (-2 * π) (2 * π)
) : InjOn exp s
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 48 条，此处仅展示前 30 条）
-/
lemma exp_injOn_Ioc {a b : ℝ} (h : b - a ≤ 2 * π) : InjOn exp (Ioc a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

/-- The image under `Circle.exp` of the interval of angles `(-r, r)`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Circle.centeredArc** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：centeredArc (r : Real) : Set Circle
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def centeredArc (r : ℝ) : Set Circle :=
  exp '' {x | |x| < r}
/-
**Circle.bijOn_exp_Ioo_centeredArc** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：bijOn_exp_Ioo_centeredArc {r : Real} (hr : r <= π) : BijOn Circle.exp (Ioo
 (-r) r) (centeredArc r)
参数：hr : r <= π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用引理 `Circle.exp_injOn_Ico`：exp_injOn_Ico {a b : Real} (h : b - a <= 2 * π) : 
InjOn exp (Ico a b)
-/
theorem bijOn_exp_Ioo_centeredArc {r : ℝ} (hr : r ≤ π) :
    BijOn Circle.exp (Ioo (-r) r) (centeredArc r) := by
  simp_rw [centeredArc, abs_lt, Set.Ioo_def]
  refine exp_injOn_Ico ?_ |>.mono Ioo_subset_Ico_self |>.bijOn_image
  grind
/-
**Circle.centeredArc_mono** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：centeredArc_mono {r s : Real} (h : r <= s) : centeredArc r subseteq center
edArc s
参数：h : r <= s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem centeredArc_mono {r s : ℝ} (h : r ≤ s) : centeredArc r ⊆ centeredArc s := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.trans_le h, rfl⟩
/-
**Circle.mem_centeredArc** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：mem_centeredArc {r : Real} (hr : r <= π) {z : Circle} : z in centeredArc r
 ↔ |arg z| < r
参数：hr : r <= π。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.arg_exp`：arg_exp {x : Real} (h₁ : -π < x) (h₂ : x <= π) : arg (ex
p x) = x
· 使用定理 `neg_lt_of_abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearO
rder α] [AddLeftMono α] {a b : α} [AddRightMono α],   |a| < b → -b < a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder
 α] {a b : α}, |a| < b → a < b
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z
-/
theorem mem_centeredArc {r : ℝ} (hr : r ≤ π) {z : Circle} :
    z ∈ centeredArc r ↔ |arg z| < r := by
  refine ⟨?_, fun hz ↦ ⟨arg z, hz, exp_arg z⟩⟩
  rintro ⟨t, ht, rfl⟩
  have htπ : |t| < π := ht.trans_le hr
  rwa [arg_exp (neg_lt_of_abs_lt htπ) (lt_of_abs_lt htπ).le]
/-
**Circle.centeredArc_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：centeredArc_eq_empty {r : Real} (hr : r <= 0) : centeredArc r = ∅
参数：hr : r <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem centeredArc_eq_empty {r : ℝ} (hr : r ≤ 0) : centeredArc r = ∅ := by
  contrapose! hr
  obtain ⟨-, x, hx, rfl⟩ := hr
  exact (abs_nonneg x).trans_lt hx

@[simp]
/-
**Circle.centeredArc_zero** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：centeredArc_zero : centeredArc 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.centeredArc_eq_empty`：centeredArc_eq_empty {r : Real} (hr : r <= 
0) : centeredArc r = ∅
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem centeredArc_zero : centeredArc 0 = ∅ :=
  centeredArc_eq_empty le_rfl
/-
**Circle.mem_centeredArc_div** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：mem_centeredArc_div {z : Circle} {s : Real} {n : Nat} (hs : s <= π) (h1 : 
z in centeredArc (π / n)) (h2 : z ^ n in centeredArc s) : z in centeredArc (s / 
n)
参数：hs : s <= π；h1 : z in centeredArc (π / n)；h2 : z ^ n in centeredArc s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Circle.centeredArc_eq_empty`：centeredArc_eq_empty {r : Real} (hr : r <= 
0) : centeredArc r = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Circle.centeredArc_zero`：centeredArc_zero : centeredArc 0 = ∅
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Circle.mem_centeredArc`：mem_centeredArc {r : Real} (hr : r <= π) {z : Ci
rcle} : z in centeredArc r ↔ |arg z| < r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `div_le_self`：div_le_self (ha : 0 <= a) (hb : 1 <= b) : a / b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_div_iff₀'`：lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Complex.arg_coe_angle_toReal_eq_arg`：arg_coe_angle_toReal_eq_arg (z : Co
mplex) : (arg z : Real.Angle).toReal = arg z
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.Angle.nsmul_toReal_eq_mul`：nsmul_toReal_eq_mul {n : Nat} (h : n != 
0) {θ : Angle} : (n • θ).toReal = n * θ.toReal ↔ θ.toReal in Set.Ioc (-π / n) (π
 / n)
· 使用定理 `Set.mem_Ioc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo b a → x ∈ Set.Ioc b a
（共 38 条，此处仅展示前 30 条）
-/
theorem mem_centeredArc_div {z : Circle} {s : ℝ} {n : ℕ} (hs : s ≤ π)
    (h1 : z ∈ centeredArc (π / n)) (h2 : z ^ n ∈ centeredArc s) :
    z ∈ centeredArc (s / n) := by
  have hs0 : 0 < s := by
    contrapose! h2
    simp [centeredArc_eq_empty h2]
  have hn0 : n ≠ 0 := by
    contrapose! h1
    simp [h1]
  have hn : 1 ≤ (n : ℝ) := by simpa [Nat.one_le_iff_ne_zero]
  rw [mem_centeredArc ((div_le_self hs0.le hn).trans hs),
    lt_div_iff₀' (one_pos.trans_le hn)]
  rw [mem_centeredArc (div_le_self pi_nonneg hn)] at h1
  rwa [mem_centeredArc hs, coe_pow, ← arg_coe_angle_toReal_eq_arg, arg_pow_coe_angle,
    (Angle.nsmul_toReal_eq_mul hn0).mpr (mem_Ioc_of_Ioo ?_), abs_mul, Nat.abs_cast,
    arg_coe_angle_toReal_eq_arg] at h2
  rwa [neg_div, mem_Ioo, ← abs_lt, arg_coe_angle_toReal_eq_arg]
/-
**Circle.exp_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_surjective : Surjective exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z
-/
lemma exp_surjective : Surjective exp := fun z => ⟨z.val.arg, exp_arg z⟩
/-
**Circle.** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PathConnectedSpace Circle := exp_surjective.pathConnectedSpace exp.continuous

variable {x y : Circle}

/-- Length of the anti-clockwise arc from `x` to `y`. -/
@[grind]
/-
**Circle.angleDiff** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：angleDiff (x y : Circle) : Real
参数：x y : Circle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Length of the anti-clockwise arc from `x` to `y`.
-/
noncomputable def angleDiff (x y : Circle) : ℝ :=
  if x.val.arg ≤ y.val.arg then y.val.arg - x.val.arg else 2 * π + y.val.arg - x.val.arg

@[simp]
/-
**Circle.angleDiff_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：angleDiff_nonneg (x y : Circle) : 0 <= angleDiff x y
参数：x y : Circle。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma angleDiff_nonneg (x y : Circle) : 0 ≤ angleDiff x y := by
  grind [neg_pi_lt_arg y.val, arg_le_pi x.val]
/-
**Circle.angleDiff_pos** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：angleDiff_pos (h : x != y) : 0 < angleDiff x y
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma angleDiff_pos (h : x ≠ y) : 0 < angleDiff x y := by
  grind [arg_eq_arg, neg_pi_lt_arg y.val, arg_le_pi x.val]
/-
**Circle.angleDiff_lt_two_pi** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：angleDiff_lt_two_pi (x y : Circle) : angleDiff x y < 2 * π
参数：x y : Circle。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma angleDiff_lt_two_pi (x y : Circle) : angleDiff x y < 2 * π := by
  grind [neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
/-
**Circle.angleDiff_add_angleDiff** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：angleDiff_add_angleDiff (h : x != y) : angleDiff x y + angleDiff y x = 2 *
 π
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma angleDiff_add_angleDiff (h : x ≠ y) : angleDiff x y + angleDiff y x = 2 * π := by
  grind [arg_eq_arg, neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
/-
**Circle.exp_angleDiff_mul** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_angleDiff_mul : exp (angleDiff x y) * x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z
· 使用定理 `Circle.exp_add`：exp_add (x y : Real) : exp (x + y) = exp x * exp y
· 使用定理 `Circle.angleDiff.eq_1`：∀ (x y : Circle), x.angleDiff y = if (↑x).arg ≤ (
↑y).arg then (↑y).arg - (↑x).arg else 2 * Real.pi + (↑y).arg - (↑x).arg
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Circle.exp_two_pi`：Circle.exp (2 * Real.pi) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma exp_angleDiff_mul : exp (angleDiff x y) * x = y := by
  rw [← exp_arg x, ← exp_add, angleDiff]
  split_ifs with hxy <;> simp
/-
**Circle.Icc_union_Icc_angleDiff_add_arg** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：Icc_union_Icc_angleDiff_add_arg (h : x != y) : Icc x.val.arg (angleDiff x 
y + x.val.arg) union Icc y.val.arg (angleDiff y x + y.val.arg) = Icc (min x.val.
arg y.val.arg) (min x.val.arg y.val.arg + 2 * π)
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Icc_union_Icc_angleDiff_add_arg (h : x ≠ y) :
    Icc x.val.arg (angleDiff x y + x.val.arg) ∪ Icc y.val.arg (angleDiff y x + y.val.arg) =
    Icc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]
/-
**Circle.Ico_union_Ico_angleDiff_add_arg** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：Ico_union_Ico_angleDiff_add_arg (h : x != y) : Ico x.val.arg (angleDiff x 
y + x.val.arg) union Ico y.val.arg (angleDiff y x + y.val.arg) = Ico (min x.val.
arg y.val.arg) (min x.val.arg y.val.arg + 2 * π)
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ico_union_Ico_angleDiff_add_arg (h : x ≠ y) :
    Ico x.val.arg (angleDiff x y + x.val.arg) ∪ Ico y.val.arg (angleDiff y x + y.val.arg) =
    Ico (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]
/-
**Circle.Ioc_union_Ioc_angleDiff_add_arg** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：Ioc_union_Ioc_angleDiff_add_arg (h : x != y) : Ioc x.val.arg (angleDiff x 
y + x.val.arg) union Ioc y.val.arg (angleDiff y x + y.val.arg) = Ioc (min x.val.
arg y.val.arg) (min x.val.arg y.val.arg + 2 * π)
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioc_union_Ioc_angleDiff_add_arg (h : x ≠ y) :
    Ioc x.val.arg (angleDiff x y + x.val.arg) ∪ Ioc y.val.arg (angleDiff y x + y.val.arg) =
    Ioc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

/-- Path from `x` to `y` on the circle traversing in anti-clockwise direction. -/
/-
**Circle.path** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：path (x y : Circle) : Path x y
参数：x y : Circle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Path from `x` to `y` on the circle traversing in anti-clockwise direction.
-/
noncomputable def path (x y : Circle) : Path x y :=
  (Path.segment x.val.arg <| angleDiff x y + x.val.arg).map exp.continuous
    |>.cast (by simp) (by simp)

@[simp]
/-
**Circle.path_apply** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：path_apply (x y : Circle) (a : unitInterval) : path x y a = exp (Path.segm
ent x.val.arg (x.angleDiff y + x.val.arg) a)
参数：x y : Circle；a : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Path.map_coe`：map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) : (
γ.map h : I -> Y) = f ∘ γ
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma path_apply (x y : Circle) (a : unitInterval) :
    path x y a = exp (Path.segment x.val.arg (x.angleDiff y + x.val.arg) a) := by
  simp [path]

@[simp]
/-
**Circle.coe_path** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：coe_path (x y : Circle) : (path x y : _ -> _) = exp ∘ ⇑(Path.segment x.val
.arg (x.angleDiff y + x.val.arg))
参数：x y : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.path_apply`：path_apply (x y : Circle) (a : unitInterval) : path x
 y a = exp (Path.segment x.val.arg (x.angleDiff y + x.val.arg) a)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma coe_path (x y : Circle) : (path x y : _ → _) =
    exp ∘ ⇑(Path.segment x.val.arg (x.angleDiff y + x.val.arg)) := by
  ext t
  rw [path_apply, comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Circle.path_self** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：path_self (x : Circle) : path x x = Path.refl x
参数：x : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Path.map_coe`：map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) : (
γ.map h : I -> Y) = f ∘ γ
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma path_self (x : Circle) : path x x = Path.refl x := by
  ext a
  simp [path, angleDiff]
/-
**Circle.path_injective_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：path_injective_of_ne (hne : x != y) : Injective (path x y)
参数：hne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.coe_path`：coe_path (x y : Circle) : (path x y : _ -> _) = exp ∘ ⇑
(Path.segment x.val.arg (x.angleDiff y + x.val.arg))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.InjOn.injective_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : α → β} {g : β → γ} (s : Set β),   Set.InjOn g s → Set.range f ⊆ s → (Functi
on.Injective …
· 使用引理 `Circle.exp_injOn_Icc`：exp_injOn_Icc {a b : Real} (h : b - a < 2 * π) : I
njOn exp (Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Path.range_segment`：range_segment (a b : E) : Set.range (Path.segment a 
b) = [a -[Real] b]
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Path.segment_injective_of_ne`：segment_injective_of_ne {a b : E} (hne : a
 != b) : Function.Injective (Path.segment a b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 33 条，此处仅展示前 30 条）
-/
lemma path_injective_of_ne (hne : x ≠ y) : Injective (path x y) := by
  rw [coe_path]
  refine (exp_injOn_Icc (a := x.val.arg) (b := angleDiff x y + x.val.arg)
    <| by simp [angleDiff_lt_two_pi]).injective_iff _ ?_ |>.mpr
    <| Path.segment_injective_of_ne <| by simp [angleDiff_pos hne |>.ne']
  rw [Path.range_segment, segment_eq_Icc (by simp)]
/-
**Circle.range_path** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：range_path (x y : Circle) : range (path x y) = exp '' Icc x.val.arg (angle
Diff x y + x.val.arg)
参数：x y : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.coe_path`：coe_path (x y : Circle) : (path x y : _ -> _) = exp ∘ ⇑
(Path.segment x.val.arg (x.angleDiff y + x.val.arg))
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Path.range_segment`：range_segment (a b : E) : Set.range (Path.segment a 
b) = [a -[Real] b]
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
lemma range_path (x y : Circle) :
    range (path x y) = exp '' Icc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, range_comp, Path.range_segment, segment_eq_Icc (by simp)]
/-
**Circle.path_image_Ico_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：path_image_Ico_of_ne (h : x != y) : path x y '' Ico 0 1 = exp '' Ico x.val
.arg (angleDiff x y + x.val.arg)
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.coe_path`：coe_path (x y : Circle) : (path x y : _ -> _) = exp ∘ ⇑
(Path.segment x.val.arg (x.angleDiff y + x.val.arg))
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `segment_image_Ico`：segment_image_Ico {x y : Real} (h : x < y) : (Path.se
gment x y) '' Ico 0 1 = Ico x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Circle.angleDiff_pos`：angleDiff_pos (h : x != y) : 0 < angleDiff x y
-/
lemma path_image_Ico_of_ne (h : x ≠ y) :
    path x y '' Ico 0 1 = exp '' Ico x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, image_comp, segment_image_Ico (by simp [angleDiff_pos h])]
/-
**Circle.path_image_Ioc_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：path_image_Ioc_of_ne (h : x != y) : path x y '' Ioc 0 1 = exp '' Ioc x.val
.arg (angleDiff x y + x.val.arg)
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.coe_path`：coe_path (x y : Circle) : (path x y : _ -> _) = exp ∘ ⇑
(Path.segment x.val.arg (x.angleDiff y + x.val.arg))
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `segment_image_Ioc`：segment_image_Ioc {x y : Real} (h : x < y) : (Path.se
gment x y) '' Ioc 0 1 = Ioc x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Circle.angleDiff_pos`：angleDiff_pos (h : x != y) : 0 < angleDiff x y
-/
lemma path_image_Ioc_of_ne (h : x ≠ y) :
    path x y '' Ioc 0 1 = exp '' Ioc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, image_comp, segment_image_Ioc (by simp [angleDiff_pos h])]
/-
**Circle.range_path_union_range_path** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：range_path_union_range_path (h : x != y) : range (path x y) union range (p
ath y x) = univ
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.range_path`：range_path (x y : Circle) : range (path x y) = exp ''
 Icc x.val.arg (angleDiff x y + x.val.arg)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.Icc_union_Icc_angleDiff_add_arg`：Icc_union_Icc_angleDiff_add_arg 
(h : x != y) : Icc x.val.arg (angleDiff x y + x.val.arg) union Icc y.val.arg (an
gleDiff y x + y.val.arg) = I…
· 使用定理 `Function.Periodic.image_Icc`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid 
α] [Archimedean α…
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用引理 `Circle.exp_surjective`：exp_surjective : Surjective exp
-/
lemma range_path_union_range_path (h : x ≠ y) : range (path x y) ∪ range (path y x) = univ := by
  rw [range_path, range_path, ← image_union, Icc_union_Icc_angleDiff_add_arg h,
    periodic_exp.image_Icc two_pi_pos]
  exact exp_surjective.range_eq
/-
**Circle.path_image_Ioc_union** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：path_image_Ioc_union (h : x != y) : path x y '' Ioc 0 1 union path y x '' 
Ioc 0 1 = univ
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.path_image_Ioc_of_ne`：path_image_Ioc_of_ne (h : x != y) : path x 
y '' Ioc 0 1 = exp '' Ioc x.val.arg (angleDiff x y + x.val.arg)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.Ioc_union_Ioc_angleDiff_add_arg`：Ioc_union_Ioc_angleDiff_add_arg 
(h : x != y) : Ioc x.val.arg (angleDiff x y + x.val.arg) union Ioc y.val.arg (an
gleDiff y x + y.val.arg) = I…
· 使用定理 `Function.Periodic.image_Ioc`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid 
α] [Archimedean α…
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用引理 `Circle.exp_surjective`：exp_surjective : Surjective exp
-/
lemma path_image_Ioc_union (h : x ≠ y) : path x y '' Ioc 0 1 ∪ path y x '' Ioc 0 1 = univ := by
  rw [path_image_Ioc_of_ne h, path_image_Ioc_of_ne h.symm, ← image_union,
    Ioc_union_Ioc_angleDiff_add_arg h, periodic_exp.image_Ioc two_pi_pos]
  exact exp_surjective.range_eq
/-
**Circle.disjoint_path_image_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：disjoint_path_image_Ioc (h : x != y) : Disjoint (path x y '' Ioc 0 1) (pat
h y x '' Ioc 0 1)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.path_image_Ioc_of_ne`：path_image_Ioc_of_ne (h : x != y) : path x 
y '' Ioc 0 1 = exp '' Ioc x.val.arg (angleDiff x y + x.val.arg)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.disjoint_image_image`：disjoint_image_image {f : β -> α} {g : γ -> α}
 {s : Set β} {t : Set γ} (h : forall b in s, forall c in t, f b != g c) : Disjoi
nt (f '' s) (g…
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Circle.exp_injOn_Ioc`：exp_injOn_Ioc {a b : Real} (h : b - a <= 2 * π) : 
InjOn exp (Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Circle.Ioc_union_Ioc_angleDiff_add_arg`：Ioc_union_Ioc_angleDiff_add_arg 
(h : x != y) : Ioc x.val.arg (angleDiff x y + x.val.arg) union Ioc y.val.arg (an
gleDiff y x + y.val.arg) = I…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
-/
lemma disjoint_path_image_Ioc (h : x ≠ y) :
    Disjoint (path x y '' Ioc 0 1) (path y x '' Ioc 0 1) := by
  have hdisj : Disjoint (Ioc x.val.arg (angleDiff x y + x.val.arg))
      (Ioc y.val.arg (angleDiff y x + y.val.arg)) := by grind [angleDiff]
  rw [path_image_Ioc_of_ne h, path_image_Ioc_of_ne h.symm]
  refine Set.disjoint_image_image fun a ha b hb ↦ ?_
  refine exp_injOn_Ioc (a := min x.val.arg y.val.arg) (b := min x.val.arg y.val.arg + 2 * π)
    (by simp) |>.ne ?_ ?_ <| hdisj.ne_of_mem ha hb
  all_goals
    rw [← Ioc_union_Ioc_angleDiff_add_arg h]
    tauto
/-
**Circle.compl_path_image_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：compl_path_image_Ioc (h : x != y) : (path x y '' Ioc 0 1)ᶜ = path y x '' I
oc 0 1
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用引理 `Circle.path_image_Ioc_union`：path_image_Ioc_union (h : x != y) : path x 
y '' Ioc 0 1 union path y x '' Ioc 0 1 = univ
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用引理 `Circle.disjoint_path_image_Ioc`：disjoint_path_image_Ioc (h : x != y) : D
isjoint (path x y '' Ioc 0 1) (path y x '' Ioc 0 1)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma compl_path_image_Ioc (h : x ≠ y) : (path x y '' Ioc 0 1)ᶜ = path y x '' Ioc 0 1 :=
  (compl_subset_iff_union.mpr <| path_image_Ioc_union h).antisymm
    <| (disjoint_path_image_Ioc h.symm).subset_compl_right
/-
**Circle.compl_range_path** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：compl_range_path (h : x != y) : (range (path x y))ᶜ = path y x '' Ioo 0 1
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.range_path`：range_path (x y : Circle) : range (path x y) = exp ''
 Icc x.val.arg (angleDiff x y + x.val.arg)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_insert_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → insert b (Set.Ioc b a) = Set.Icc b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用引理 `Circle.path_image_Ioc_of_ne`：path_image_Ioc_of_ne (h : x != y) : path x 
y '' Ioc 0 1 = exp '' Ioc x.val.arg (angleDiff x y + x.val.arg)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用引理 `Circle.compl_path_image_Ioc`：compl_path_image_Ioc (h : x != y) : (path x
 y '' Ioc 0 1)ᶜ = path y x '' Ioc 0 1
· 使用定理 `Set.Ioo_insert_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}
, b < a → insert a (Set.Ioo b a) = Set.Ioc b a
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z
· 使用定理 `Set.insert_inter_of_notMem`：insert_inter_of_notMem (h : a ∉ t) : insert 
a s inter t = s inter t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Ne.trans_eq`：∀ {α : Sort u_1} {a b c : α}, a ≠ b → b = c → a ≠ c
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Circle.path_injective_of_ne`：path_injective_of_ne (hne : x != y) : Injec
tive (path x y)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 31 条，此处仅展示前 30 条）
-/
lemma compl_range_path (h : x ≠ y) : (range (path x y))ᶜ = path y x '' Ioo 0 1 := by
  rw [range_path, ← Ioc_insert_left (by simp), image_insert_eq,
    ← path_image_Ioc_of_ne h, ← union_singleton, compl_union, compl_path_image_Ioc h,
    ← Ioo_insert_right (by simp), image_insert_eq, (y.path x).target, exp_arg,
    insert_inter_of_notMem (by simp), inter_eq_left]
  rintro z ⟨t, ht, rfl⟩
  exact (path_injective_of_ne h.symm).ne ht.2.ne |>.trans_eq (y.path x).target
/-
**Circle.range_path_ssubset_univ** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：range_path_ssubset_univ (x y : Circle) : range (path x y) ⊂ univ
参数：x y : Circle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ssubset_univ_iff_nonempty_compl`：ssubset_univ_iff_nonempty_compl : s
 ⊂ univ ↔ sᶜ.Nonempty
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Circle.path_self`：path_self (x : Circle) : path x x = Path.refl x
· 使用定理 `Path.refl_range`：refl_range {a : X} : range (Path.refl a) = {a}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Circle.compl_range_path`：compl_range_path (h : x != y) : (range (path x 
y))ᶜ = path y x '' Ioo 0 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 72 条，此处仅展示前 30 条）
-/
lemma range_path_ssubset_univ (x y : Circle) : range (path x y) ⊂ univ := by
  rw [ssubset_univ_iff_nonempty_compl]
  obtain rfl | hne := eq_or_ne x y
  · use -x, by simp [neg_ne_self]
  rw [compl_range_path hne]
  use y.path x ⟨2⁻¹, by simp only [mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]; linarith⟩
  refine mem_image_of_mem _ ⟨by simp [← unitInterval.coe_pos], unitInterval.coe_lt_one.mp ?_⟩
  linarith
/-
**Circle.range_path_inter_range_path** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：range_path_inter_range_path (h : x != y) : range (path x y) inter range (p
ath y x) = {x, y}
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `unitInterval.univ_eq_Icc`：univ_eq_Icc : (univ : Set I) = Icc (0 : I) (1 
: I)
· 使用定理 `Set.Ioc_insert_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → insert b (Set.Ioc b a) = Set.Icc b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.Ioo_insert_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}
, b < a → insert a (Set.Ioo b a) = Set.Ioc b a
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用引理 `Circle.disjoint_path_image_Ioc`：disjoint_path_image_Ioc (h : x != y) : D
isjoint (path x y '' Ioc 0 1) (path y x '' Ioc 0 1)
-/
lemma range_path_inter_range_path (h : x ≠ y) : range (path x y) ∩ range (path y x) = {x, y} := by
  rw [← image_univ, ← image_univ, unitInterval.univ_eq_Icc, ← Ioc_insert_left (by simp),
    ← Ioo_insert_right (by simp)]
  simp_rw [image_insert_eq]
  have h : Disjoint ((x.path y) '' Ioo 0 1) ((y.path x) '' Ioo 0 1) := by
    refine (disjoint_path_image_Ioc h).mono ?_ ?_ <;> exact image_mono Ioo_subset_Ioc_self
  grind
/-
**Circle.isPathConnected_compl_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：isPathConnected_compl_singleton (x : Circle) : IsPathConnected {x}ᶜ
参数：x : Circle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Circle.neg_ne_self`：neg_ne_self (x : Circle) : -x != x
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.path_self`：path_self (x : Circle) : path x x = Path.refl x
· 使用定理 `Path.refl_range`：refl_range {a : X} : range (Path.refl a) = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `Circle.range_path_inter_range_path`：range_path_inter_range_path (h : x !
= y) : range (path x y) inter range (path y x) = {x, y}
-/
lemma isPathConnected_compl_singleton (x : Circle) : IsPathConnected {x}ᶜ := by
  refine ⟨-x, neg_ne_self x, fun y (hyx : y ≠ x) ↦ ?_⟩
  obtain hxP | hxP := (em (x ∈ range (path (-x) y))).symm
  · exact ⟨(path (-x) y), fun t ↦ by grind⟩
  refine ⟨(path y (-x)).symm, ?_⟩
  have hne : -x ≠ y := by
    rintro rfl
    simp [(neg_ne_self x).symm] at hxP
  have hP₂ : x ∉ range (path y (-x)) := by
    rintro hP₂
    have h : x ∈ range _ ∩ _ := ⟨hxP, hP₂⟩
    rw [range_path_inter_range_path hne] at h
    simp [(neg_ne_self x).symm, hyx.symm] at h
  grind
/-
**Circle.not_isPreconnected_compl_pair** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：not_isPreconnected_compl_pair (hxy : x != y) : ¬ IsPreconnected {x, y}ᶜ
参数：hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Path.source_mem_range`：source_mem_range (γ : Path x y) : x in range ⇑γ
· 使用引理 `Path.target_mem_range`：target_mem_range (γ : Path x y) : y in range ⇑γ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Circle.range_path_ssubset_univ`：range_path_ssubset_univ (x y : Circle) :
 range (path x y) ⊂ univ
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Path.continuous`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y), Continuous ⇑γ
· 使用引理 `Circle.range_path_union_range_path`：range_path_union_range_path (h : x !
= y) : range (path x y) union range (path y x) = univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用引理 `Circle.range_path_inter_range_path`：range_path_inter_range_path (h : x !
= y) : range (path x y) inter range (path y x) = {x, y}
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
-/
lemma not_isPreconnected_compl_pair (hxy : x ≠ y) : ¬ IsPreconnected {x, y}ᶜ := by
  simp only [isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or, exists_and_left]
  refine ⟨range (path x y), ?_, range (path y x), (isCompact_range (path x y).continuous).isClosed,
    (isCompact_range (path y x).continuous).isClosed, ?_, ?_, ?_⟩
  · rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path x y).source_mem_range, (path x y).target_mem_range, and_self])]
    exact (range_path_ssubset_univ x y).ne
  · rw [range_path_union_range_path hxy]
    exact subset_univ _
  · rw [range_path_inter_range_path hxy]
    exact compl_inter_self {x, y}
  rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path y x).source_mem_range, (path y x).target_mem_range, and_self])]
  exact (range_path_ssubset_univ y x).ne

end Circle

namespace Real.Angle

/-- `Circle.exp`, applied to a `Real.Angle`. -/
/-
**Real.Angle.toCircle** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：toCircle (θ : Angle) : Circle
参数：θ : Angle。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)

--- 原说明 ---
`Circle.exp`, applied to a `Real.Angle`.
-/
noncomputable def toCircle (θ : Angle) : Circle := Circle.periodic_exp.lift θ
/-
**Real.Angle.toCircle_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：∀ (x : ℝ), (↑x).toCircle = Circle.exp x
参数：x : ℝ；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCircle_coe (x : ℝ) : toCircle x = .exp x := rfl
/-
**Real.Angle.coe_toCircle** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angle`。
形式化陈述：coe_toCircle (θ : Angle) : (θ.toCircle : Complex) = θ.cos + θ.sin * I
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_toCircle (θ : Angle) : (θ.toCircle : ℂ) = θ.cos + θ.sin * I := by
  induction θ using Angle.induction_on
  simp [exp_mul_I]
/-
**Real.Angle.toCircle_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：Real.Angle.toCircle 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_zero`：coe_zero : ↑(0 : Real) = (0 : Angle)
· 使用定理 `Real.Angle.toCircle_coe`：∀ (x : ℝ), (↑x).toCircle = Circle.exp x
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
-/
@[simp] lemma toCircle_zero : toCircle 0 = 1 := by rw [← coe_zero, toCircle_coe, Circle.exp_zero]
/-
**Real.Angle.toCircle_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：∀ (θ : Real.Angle), (-θ).toCircle = θ.toCircle⁻¹
参数：θ : Real.Angle；-θ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.exp_neg`：∀ (x : ℝ), Circle.exp (-x) = (Circle.exp x)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toCircle_neg (θ : Angle) : toCircle (-θ) = (toCircle θ)⁻¹ := by
  induction θ using Angle.induction_on
  simp_rw [← coe_neg, toCircle_coe, Circle.exp_neg]
/-
**Real.Angle.toCircle_add** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：∀ (θ₁ θ₂ : Real.Angle), (θ₁ + θ₂).toCircle = θ₁.toCircle * θ₂.toCircle
参数：θ₁ θ₂ : Real.Angle；θ₁ + θ₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Circle.exp_add`：exp_add (x y : Real) : exp (x + y) = exp x * exp y
-/
@[simp] lemma toCircle_add (θ₁ θ₂ : Angle) : toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂ := by
  induction θ₁ using Angle.induction_on
  induction θ₂ using Angle.induction_on
  exact Circle.exp_add _ _
/-
**Real.Angle.arg_toCircle** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：∀ (θ : Real.Angle), ↑(↑θ.toCircle).arg = θ
参数：θ : Real.Angle；↑θ.toCircle。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toCircle_coe`：∀ (x : ℝ), (↑x).toCircle = Circle.exp x
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `Complex.arg_cos_add_sin_mul_I_coe_angle`：arg_cos_add_sin_mul_I_coe_angle
 (θ : Real.Angle) : (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle)
 = θ
-/
@[simp] lemma arg_toCircle (θ : Angle) : (arg θ.toCircle : Angle) = θ := by
  induction θ using Angle.induction_on
  rw [toCircle_coe, Circle.coe_exp, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ←
    Angle.cos_coe, ← Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]

end Real.Angle

namespace AddCircle

variable {T : ℝ}

/-! ### Map from `AddCircle` to `Circle` -/

/-
**AddCircle.scaled_exp_map_periodic** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：scaled_exp_map_periodic : Function.Periodic (fun x => Circle.exp (2 * π / 
T * x)) T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `Circle.periodic_exp`：periodic_exp : Periodic exp (2 * π)

--- 原说明 ---
### Map from `AddCircle` to `Circle`
-/
theorem scaled_exp_map_periodic : Function.Periodic (fun x => Circle.exp (2 * π / T * x)) T := by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, Circle.periodic_exp]

/-- The canonical map `fun x => exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
/-
**AddCircle.toCircle** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：toCircle : AddCircle T -> Circle
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.scaled_exp_map_periodic`：scaled_exp_map_periodic : Function.Pe
riodic (fun x => Circle.exp (2 * π / T * x)) T

--- 原说明 ---
The canonical map `fun x => exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circ
le in `ℂ`.
If `T = 0` we understand this as the constant function 1.
-/
noncomputable def toCircle : AddCircle T → Circle :=
  (@scaled_exp_map_periodic T).lift
/-
**AddCircle.toCircle_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：toCircle_apply_mk (x : Real) : @toCircle T x = Circle.exp (2 * π / T * x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCircle_apply_mk (x : ℝ) : @toCircle T x = Circle.exp (2 * π / T * x) :=
  rfl
/-
**AddCircle.toCircle_add** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：toCircle_add (x y : AddCircle T) : toCircle (x + y) = toCircle x * toCircl
e y
参数：x y : AddCircle T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Circle.exp_add`：exp_add (x y : Real) : exp (x + y) = exp x * exp y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toCircle_add (x y : AddCircle T) : toCircle (x + y) = toCircle x * toCircle y := by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  simp_rw [← coe_add, toCircle_apply_mk, mul_add, Circle.exp_add]
/-
**AddCircle.toCircle_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientAddGroup.mk_zero`：∀ {G : Type u_1} [inst : AddGroup G] (N : AddS
ubgroup G) [nN : N.Normal], ↑0 = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddCircle.toCircle_apply_mk`：toCircle_apply_mk (x : Real) : @toCircle T 
x = Circle.exp (2 * π / T * x)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
-/
@[simp] lemma toCircle_zero : toCircle (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero, toCircle_apply_mk, mul_zero, Circle.exp_zero]
/-
**AddCircle.toCircle_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：toCircle_neg (x : AddCircle T) : toCircle (-x) = (toCircle x)⁻¹
参数：x : AddCircle T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `AddCircle.toCircle_zero`：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toCircle_neg (x : AddCircle T) : toCircle (-x) = (toCircle x)⁻¹ :=
  (mul_left_inj (toCircle x)).mp <| by simp [← toCircle_add]
/-
**AddCircle.toCircle_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：toCircle_nsmul (x : AddCircle T) (n : Nat) : toCircle (n • x) = toCircle x
 ^ n
参数：x : AddCircle T；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `AddCircle.toCircle_zero`：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `AddCircle.toCircle_add`：toCircle_add (x y : AddCircle T) : toCircle (x +
 y) = toCircle x * toCircle y
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem toCircle_nsmul (x : AddCircle T) (n : ℕ) : toCircle (n • x) = toCircle x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, toCircle_add, ih, pow_succ]
/-
**AddCircle.toCircle_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：toCircle_zsmul (x : AddCircle T) (n : Int) : toCircle (n • x) = toCircle x
 ^ n
参数：x : AddCircle T；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `AddCircle.toCircle_nsmul`：toCircle_nsmul (x : AddCircle T) (n : Nat) : t
oCircle (n • x) = toCircle x ^ n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用定理 `AddCircle.toCircle_neg`：toCircle_neg (x : AddCircle T) : toCircle (-x) =
 (toCircle x)⁻¹
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
theorem toCircle_zsmul (x : AddCircle T) (n : ℤ) : toCircle (n • x) = toCircle x ^ n := by
  cases n <;> simp [toCircle_nsmul, toCircle_neg]

@[fun_prop, continuity]
/-
**AddCircle.continuous_toCircle** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：continuous_toCircle : Continuous (@toCircle T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem continuous_toCircle : Continuous (@toCircle T) :=
  continuous_coinduced_dom.mpr (Circle.exp.continuous.comp <| by fun_prop)
/-
**AddCircle.injective_toCircle** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：injective_toCircle (hT : T != 0) : Function.Injective (@toCircle T)
参数：hT : T != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Circle.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ exists m : 
Int, x = y + m * (2 * π)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientAddGroup.eq`：∀ {α : Type u_1} [inst : AddGroup α] {s : AddSubgro
up α} {a b : α}, ↑a = ↑b ↔ -a + b ∈ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 84 条，此处仅展示前 30 条）
-/
theorem injective_toCircle (hT : T ≠ 0) : Function.Injective (@toCircle T) := by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  linarith

/-- The homeomorphism between `AddCircle (2 * π)` and `Circle`. -/
/-
**AddCircle.homeomorphCircle'** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：homeomorphCircle'_apply_mk (x : Real) : homeomorphCircle' x = Circle.exp x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.arg_toCircle`：∀ (θ : Real.Angle), ↑(↑θ.toCircle).arg = θ
· 使用定理 `Circle.exp_arg`：exp_arg (z : Circle) : exp (arg z) = z

--- 原说明 ---
The homeomorphism between `AddCircle (2 * π)` and `Circle`.
-/
@[simps] noncomputable def homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle where
  toFun := Angle.toCircle
  invFun := fun x ↦ arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_arg_coe_angle x.coe_ne_zero).comp continuousAt_subtype_val
/-
**AddCircle.homeomorphCircle'_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ (x : ℝ), AddCircle.homeomorphCircle' ↑x = Circle.exp x
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddCircle.homeomorphCircle'`：homeomorphCircle'_apply_mk (x : Real) : hom
eomorphCircle' x = Circle.exp x
-/
theorem homeomorphCircle'_apply_mk (x : ℝ) : homeomorphCircle' x = Circle.exp x := rfl

/-- The homeomorphism between `AddCircle` and `Circle`. -/
/-
**AddCircle.homeomorphCircle** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：homeomorphCircle (hT : T != 0) : AddCircle T ≃ₜ Circle
参数：hT : T != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `AddCircle.homeomorphCircle'`：homeomorphCircle'_apply_mk (x : Real) : hom
eomorphCircle' x = Circle.exp x

--- 原说明 ---
The homeomorphism between `AddCircle` and `Circle`.
-/
noncomputable def homeomorphCircle (hT : T ≠ 0) : AddCircle T ≃ₜ Circle :=
  (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'
/-
**AddCircle.homeomorphCircle_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：homeomorphCircle_apply (hT : T != 0) (x : AddCircle T) : homeomorphCircle 
hT x = toCircle x
参数：hT : T != 0；x : AddCircle T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `AddCircle.homeomorphCircle'`：homeomorphCircle'_apply_mk (x : Real) : hom
eomorphCircle' x = Circle.exp x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.homeomorphCircle.eq_1`：∀ {T : ℝ} (hT : T ≠ 0),   AddCircle.hom
eomorphCircle hT =     (AddCircle.homeomorphAddCircle T (2 * Real.pi) hT AddCirc
le.homeomorphCircle._…
· 使用定理 `Homeomorph.trans_apply`：trans_apply (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X) 
: h₁.trans h₂ x = h₂ (h₁ x)
· 使用定理 `AddCircle.homeomorphAddCircle_apply_mk`：homeomorphAddCircle_apply_mk (hp
 : p != 0) (hq : q != 0) (x : 𝕜) : homeomorphAddCircle p q hp hq (x : 𝕜) = (x * 
(p⁻¹ * q) : 𝕜)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddCircle.homeomorphCircle'_apply_mk`：∀ (x : ℝ), AddCircle.homeomorphCir
cle' ↑x = Circle.exp x
· 使用定理 `AddCircle.toCircle_apply_mk`：toCircle_apply_mk (x : Real) : @toCircle T 
x = Circle.exp (2 * π / T * x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 45 条，此处仅展示前 30 条）
-/
theorem homeomorphCircle_apply (hT : T ≠ 0) (x : AddCircle T) :
    homeomorphCircle hT x = toCircle x := by
  cases x using QuotientAddGroup.induction_on
  rw [homeomorphCircle, Homeomorph.trans_apply,
    homeomorphAddCircle_apply_mk, homeomorphCircle'_apply_mk, toCircle_apply_mk]
  ring_nf

end AddCircle

open AddCircle

/-
**Circle.isAddQuotientCoveringMap_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Circle.isAddQuotientCoveringMap_exp : IsAddQuotientCoveringMap exp (AddSub
group.zmultiples (2 * π))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
· 使用定理 `AddCircle.scaled_exp_map_periodic`：scaled_exp_map_periodic : Function.Pe
riodic (fun x => Circle.exp (2 * π / T * x)) T
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddCircle.homeomorphCircle_apply`：homeomorphCircle_apply (hT : T != 0) (
x : AddCircle T) : homeomorphCircle hT x = toCircle x
· 使用定理 `Function.Periodic.lift.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {f f_
1 : α → β} (e_f : f = f_1) {c : α} [inst : AddGroup α] (h : Function.Periodic f 
c)   (x x_1 : α ⧸ AddSu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsAddQuotientCoveringMap.homeomorph_comp`：∀ {E : Type u_1} {X : Type u_2
} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Typ
e u_3}   [inst_2 : AddGroup G]…
· 使用定理 `AddCircle.isAddQuotientCoveringMap_coe`：isAddQuotientCoveringMap_coe : I
sAddQuotientCoveringMap ((↑) : 𝕜 -> AddCircle p) (zmultiples p)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
-/
theorem Circle.isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap exp (AddSubgroup.zmultiples (2 * π)) := by
  convert! (isAddQuotientCoveringMap_coe _).homeomorph_comp (homeomorphCircle _)
  on_goal 2 => simp
  ext; simp [homeomorphCircle_apply, toCircle]
/-
**Circle.isCoveringMap_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Circle.isCoveringMap_exp : IsCoveringMap exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddQuotientCoveringMap.isCoveringMap`：∀ {E : Type u_1} {X : Type u_2} 
[inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] (f : E → X) (G : Type 
u_3)   [inst_2 : AddGroup G]…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Circle.isAddQuotientCoveringMap_exp`：Circle.isAddQuotientCoveringMap_exp
 : IsAddQuotientCoveringMap exp (AddSubgroup.zmultiples (2 * π))
-/
theorem Circle.isCoveringMap_exp : IsCoveringMap exp := isAddQuotientCoveringMap_exp.isCoveringMap
/-
**isLocalHomeomorph_circleExp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalHomeomorph_circleExp : IsLocalHomeomorph Circle.exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
· 使用定理 `Circle.isCoveringMap_exp`：Circle.isCoveringMap_exp : IsCoveringMap exp
-/
lemma isLocalHomeomorph_circleExp : IsLocalHomeomorph Circle.exp :=
  Circle.isCoveringMap_exp.isLocalHomeomorph

/-- The centered arcs `centeredArc (π / 2 ^ (n + 1))` form a neighborhood basis at `1`.
This basis is useful because multiplying two sufficiently small arcs stays inside an earlier arc. -/
/-
**Circle.hasBasis_centeredArc_div_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Circle.hasBasis_centeredArc_div_two_pow : (nhds (1 : Circle)).HasBasis (fu
n _ => True) (fun n => centeredArc (π / 2 ^ (n + 1)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `IsLocalHomeomorph.map_nhds_eq`：map_nhds_eq (hf : IsLocalHomeomorph f) (x
 : X) : (𝓝 x).map f = 𝓝 (f x)
· 使用引理 `isLocalHomeomorph_circleExp`：isLocalHomeomorph_circleExp : IsLocalHomeom
orph Circle.exp
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用引理 `Metric.mk_uniformity_basis_of_tendsto`：mk_uniformity_basis_of_tendsto {β
 : Type*} {p : β -> Prop} {f : β -> Real} {l : Filter β} [l.NeBot] (hf₀ : forall
 i, p i -> 0 < f i) (hf₁ : …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The centered arcs `centeredArc (π / 2 ^ (n + 1))` form a neighborhood basis at `
1`.
This basis is useful because multiplying two sufficiently small arcs stays insid
e an earlier arc.
-/
theorem Circle.hasBasis_centeredArc_div_two_pow :
    (nhds (1 : Circle)).HasBasis (fun _ ↦ True) (fun n ↦ centeredArc (π / 2 ^ (n + 1))) := by
  rw [← Circle.exp_zero, ← isLocalHomeomorph_circleExp.map_nhds_eq 0]
  simp_rw [centeredArc, abs_lt, Set.Ioo_def, ← Real.ball_zero_eq_Ioo]
  apply Filter.HasBasis.map
  refine nhds_basis_uniformity <| Metric.mk_uniformity_basis_of_tendsto (l := Filter.atTop)
    (fun _ _ ↦ by positivity) (by simp) ?_
  simp_rw [div_eq_mul_inv, pow_succ, mul_inv_rev, ← mul_assoc]
  rw [← mul_zero (π * 2⁻¹)]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    |>.const_mul _
/-
**Circle.isOpen_centeredArc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Circle.isOpen_centeredArc (r : Real) : IsOpen (centeredArc r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsLocalHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph 
f → IsOpenMap f
· 使用引理 `isLocalHomeomorph_circleExp`：isLocalHomeomorph_circleExp : IsLocalHomeom
orph Circle.exp
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem Circle.isOpen_centeredArc (r : ℝ) : IsOpen (centeredArc r) := by
  have hset : {x : ℝ | |x| < r} = Ioo (-r) r := by
    ext x
    simp [abs_lt]
  simpa [centeredArc, hset] using
    isLocalHomeomorph_circleExp.isOpenMap (Ioo (-r) r) isOpen_Ioo

/-- If all positive powers of a point on the circle lie in the right half centered arc,
then the point is `1`. -/
/-
**Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two {z : Circle} (hz : 
forall n > 0, z ^ n in centeredArc (π / 2)) : z = 1
参数：hz : forall n > 0, z ^ n in centeredArc (π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `Circle.mem_centeredArc_div`：mem_centeredArc_div {z : Circle} {s : Real} 
{n : Nat} (hs : s <= π) (h1 : z in centeredArc (π / n)) (h2 : z ^ n in centeredA
rc s) : z in cen…
· 使用定理 `div_le_self`：div_le_self (ha : 0 <= a) (hb : 1 <= b) : a / b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_nonneg`：pi_nonneg : 0 <= π
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ker_nhds`：ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x}
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If all positive powers of a point on the circle lie in the right half centered a
rc,
then the point is `1`.
-/
theorem Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two {z : Circle}
    (hz : ∀ n > 0, z ^ n ∈ centeredArc (π / 2)) : z = 1 := by
  have hz1 : z ∈ centeredArc (π / 2) := by simpa using hz 1
  have h (n : ℕ) : z ∈ centeredArc (π / 2 ^ (n + 1)) := by
    induction n with
    | zero => simpa using hz1
    | succ n ih =>
        simpa [div_div, ← pow_succ'] using mem_centeredArc_div
          (div_le_self pi_nonneg one_le_two) (by simpa) (hz (2 ^ (n + 1)) (by positivity))
  simpa [h] using Set.ext_iff.mp hasBasis_centeredArc_div_two_pow.ker z

/- TODO: this generalizes to a large class of groups, but requires an open mapping theorem for
topological groups to show the `n`th power map is open (see https://www.mathematik.tu-darmstadt.de/media/mathematik/forschung/preprint/preprints/2480.pdf
and https://www.math.uwaterloo.ca/~cgodsil/pdfs/topology/topgr.pdf), and discreteness of the
kernel (see https://gemini.google.com/share/6e9ab4abcb95). -/
/-
**Circle.isQuotientCoveringMap_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Circle.isQuotientCoveringMap_zpow (n : Int) [NeZero n] : IsQuotientCoverin
gMap (· ^ n : Circle -> _) (zpowGroupHom (α
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
`：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topologi
calSpace X] [inst_2 : Group E]   [IsTopologicalGroup E] [inst_…
· 使用定理 `Circle.instIsTopologicalGroup`：IsTopologicalGroup Circle
· 使用定理 `Topology.IsQuotientMap.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Typ
e u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologic
alSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddCircle.homeomorphCircle_apply`：homeomorphCircle_apply (hT : T != 0) (
x : AddCircle T) : homeomorphCircle hT x = toCircle x
· 使用定理 `AddCircle.toCircle_zsmul`：toCircle_zsmul (x : AddCircle T) (n : Int) : t
oCircle (n • x) = toCircle x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
· 使用定理 `IsUnit.isQuotientMap_zsmul`：isQuotientMap_zsmul {M β} [Ring M] [AddCommG
roup α] [Module M α] [ContinuousConstSMul M α] [AddGroup β] (f : α ->+ β) [Topol
ogicalSpace β] (…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
TODO: this generalizes to a large class of groups, but requires an open mapping 
theorem for
topological groups to show the `n`th power map is open (see https://www.mathemat
ik.tu-darmstadt.de/media/mathematik/forschung/preprint/preprints/2480.pdf
and https://www.math.uwaterloo.ca/~cgodsil/pdfs/topology/topgr.pdf), and discret
eness of the
kernel (see https://gemini.google.com/share/6e9ab4abcb95).
-/
theorem Circle.isQuotientCoveringMap_zpow (n : ℤ) [NeZero n] :
    IsQuotientCoveringMap (· ^ n : Circle → _) (zpowGroupHom (α := Circle) n).ker := by
  have hn : IsUnit (n : ℝ) := by simpa using NeZero.ne n
  let e := AddCircle.homeomorphCircle one_ne_zero
  refine Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f := zpowGroupHom (α := Circle) n) ?_ (Set.Finite.isDiscrete <| .of_preimage ?_ e.surjective)
  · refine .of_comp e.continuous (continuous_zpow n) ?_
    convert!
      e.isQuotientMap.comp <|
        IsUnit.isQuotientMap_zsmul (M := ℝ) (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
          isQuotientMap_quotient_mk' n hn
    ext; simp [zpowGroupHom, e, homeomorphCircle_apply, toCircle_zsmul]
  · convert! finite_torsion_of_isSMulRegular_int (1 : ℝ) n fun _ ↦ by simp [NeZero.ne]
    ext
    simp [e, homeomorphCircle_apply, ← toCircle_zsmul, ← (injective_toCircle one_ne_zero).eq_iff]
/-
**Circle.isQuotientCoveringMap_npow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Circle.isQuotientCoveringMap_npow (n : Nat) [NeZero n] : IsQuotientCoverin
gMap (· ^ n : Circle -> _) (powMonoidHom (α
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.isQuotientCoveringMap_zpow`：Circle.isQuotientCoveringMap_zpow (n 
: Int) [NeZero n] : IsQuotientCoveringMap (· ^ n : Circle -> _) (zpowGroupHom (α
· 使用定理 `Int.instNeZeroCastOfNat`：∀ {n : ℕ} [NeZero n], NeZero ↑n
-/
theorem Circle.isQuotientCoveringMap_npow (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (· ^ n : Circle → _) (powMonoidHom (α := Circle) n).ker :=
  isQuotientCoveringMap_zpow n
