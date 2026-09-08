/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# seminormFromBounded

In this file, we prove [BGR, Proposition 1.2.1/2][bosch-guntzer-remmert] : given a nonzero
additive group seminorm on a commutative ring `R` such that for some `c : ℝ` and every `x y : R`,
the inequality `f (x * y) ≤ c * f x * f y)` is satisfied, we create a ring seminorm on `R`.

In the file comments, we will use the expression `f is multiplicatively bounded` to indicate that
this condition holds.


## Main Definitions

* `seminormFromBounded'` : the real-valued function sending `x ∈ R` to the supremum of
  `f(x*y)/f(y)`, where `y` runs over the elements of `R`.
* `seminormFromBounded` : the function `seminormFromBounded'` as a `RingSeminorm` on `R`.
* `normFromBounded` :`seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is
  nonnegative, multiplicatively bounded and subadditive, that it preserves `0` and negation, and
  that `f` has trivial kernel.


## Main Results

* `seminormFromBounded_isNonarchimedean` : if `f : R → ℝ` is a nonnegative, multiplicatively
  bounded, nonarchimedean function, then `seminormFromBounded' f` is nonarchimedean.
* `seminormFromBounded_of_mul_is_mul` : if `f : R → ℝ` is a nonnegative, multiplicatively bounded
  function and `x : R` is multiplicative for `f`, then `x` is multiplicative for
  `seminormFromBounded' f`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

seminormFromBounded, RingSeminorm, Nonarchimedean
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal

variable {R : Type _} [CommRing R] (f : R → ℝ) {c : ℝ}

section seminormFromBounded

/-- The real-valued function sending `x ∈ R` to the supremum of  `f(x*y)/f(y)`, where `y` runs over
the elements of `R`. -/
/-
**seminormFromBounded'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：seminormFromBounded' : R -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real-valued function sending `x ∈ R` to the supremum of  `f(x*y)/f(y)`, wher
e `y` runs over
the elements of `R`.
-/
def seminormFromBounded' : R → ℝ := fun x ↦ iSup fun y : R ↦ f (x * y) / f y

variable {f}

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then `f 1 ≠ 0`. -/
/-
**map_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_one_ne_zero (f_ne_zero : f != 0) (f_nonneg : 0 <= f) (f_mul : forall x
 y : R, f (x * y) <= c * f x * f y) : f 1 != 0
参数：f_ne_zero : f != 0；f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c *
 f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, the
n `f 1 ≠ 0`.
-/
theorem map_one_ne_zero (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) : f 1 ≠ 0 := by
  intro h1
  specialize f_mul 1
  simp_rw [h1, one_mul, mul_zero, zero_mul] at f_mul
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f_ne_zero
  exact hz <| (f_mul z).antisymm (f_nonneg z)

/-- If `f : R → ℝ` is a nonnegative multiplicatively bounded function and `x : R` is a unit with
  `f x ≠ 0`, then for every `n : ℕ`, we have `f (x ^ n) ≠ 0`. -/
/-
**map_pow_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_pow_ne_zero (f_nonneg : 0 <= f) {x : R} (hx : IsUnit x) (hfx : f x != 
0) (n : Nat) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : f (x ^ n) !=
 0
参数：f_nonneg : 0 <= f；hx : IsUnit x；hfx : f x != 0；n : Nat；f_mul : forall x y : R
, f (x * y) <= c * f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one_ne_zero`：map_one_ne_zero (f_ne_zero : f != 0) (f_nonneg : 0 <= f
) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : f 1 != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b

--- 原说明 ---
If `f : R → ℝ` is a nonnegative multiplicatively bounded function and `x : R` is
 a unit with
  `f x ≠ 0`, then for every `n : ℕ`, we have `f (x ^ n) ≠ 0`.
-/
theorem map_pow_ne_zero (f_nonneg : 0 ≤ f) {x : R} (hx : IsUnit x) (hfx : f x ≠ 0) (n : ℕ)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) : f (x ^ n) ≠ 0 := by
  have h1 : f 1 ≠ 0 := map_one_ne_zero (Function.ne_iff.mpr ⟨x, hfx⟩) f_nonneg f_mul
  intro hxn
  have : f 1 ≤ 0 := by simpa [← mul_pow, hxn] using f_mul (x ^ n) (hx.unit⁻¹ ^ n)
  exact h1 <| this.antisymm (f_nonneg 1)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then given `x y : R` with
  `f x = 0`, we have `f (x * y) = 0`. -/
/-
**map_mul_zero_of_map_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_zero_of_map_zero (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x
 * y) <= c * f x * f y) {x : R} (hx : f x = 0) (y : R) : f (x * y) = 0
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；hx : f x
 = 0；y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then given `
x y : R` with
  `f x = 0`, we have `f (x * y) = 0`.
-/
theorem map_mul_zero_of_map_zero (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R} (hx : f x = 0)
    (y : R) : f (x * y) = 0 := by
  replace f_mul : f (x * y) ≤ 0 := by simpa [hx] using f_mul x y
  exact le_antisymm f_mul (f_nonneg _)

/-- `seminormFromBounded' f` preserves `0`. -/
/-
**seminormFromBounded_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_zero (f_zero : f 0 = 0) : seminormFromBounded' f (0 : 
R) = 0
参数：f_zero : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`seminormFromBounded' f` preserves `0`.
-/
theorem seminormFromBounded_zero (f_zero : f 0 = 0) : seminormFromBounded' f (0 : R) = 0 := by
  simp_rw [seminormFromBounded', zero_mul, f_zero, zero_div, ciSup_const]
/-
**seminormFromBounded_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_aux (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x 
* y) <= c * f x * f y) (x : R) : 0 <= c * f x
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
（共 75 条，此处仅展示前 30 条）
-/
theorem seminormFromBounded_aux (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) : 0 ≤ c * f x := by
  rcases (f_nonneg x).eq_or_lt' with hx | hx
  · simp [hx]
  · change 0 < f x at hx
    have hc : 0 ≤ c := by
      specialize f_mul x 1
      rw [mul_one, show c * f x * f 1 = c * f 1 * f x by ring, le_mul_iff_one_le_left hx] at f_mul
      replace f_nonneg : 0 ≤ f 1 := f_nonneg 1
      rcases f_nonneg.eq_or_lt' with h1 | h1
      · linarith [show (1 : ℝ) ≤ 0 by simpa [h1] using f_mul]
      · rw [← div_le_iff₀ h1] at f_mul
        linarith [one_div_pos.mpr h1]
    positivity

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  the image of `y ↦ f (x * y) / f y` is bounded above. -/
/-
**seminormFromBounded_bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_bddAbove_range (f_nonneg : 0 <= f) (f_mul : forall x y
 : R, f (x * y) <= c * f x * f y) (x : R) : BddAbove (Set.range fun y => f (x * 
y) / f y)
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `seminormFromBounded_aux`：seminormFromBounded_aux (f_nonneg : 0 <= f) (f_
mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : 0 <= c * f x
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for eve
ry `x : R`,
  the image of `y ↦ f (x * y) / f y` is bounded above.
-/
theorem seminormFromBounded_bddAbove_range (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    BddAbove (Set.range fun y ↦ f (x * y) / f y) := by
  use c * f x
  rintro r ⟨y, rfl⟩
  rcases (f_nonneg y).eq_or_lt' with hy0 | hy0
  · simpa [hy0] using seminormFromBounded_aux f_nonneg f_mul x
  · simpa [div_le_iff₀ hy0] using f_mul x y

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `seminormFromBounded' f x` is bounded above by some multiple of `f x`. -/
/-
**seminormFromBounded_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_le (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x *
 y) <= c * f x * f y) (x : R) : seminormFromBounded' f x <= c * f x
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `seminormFromBounded_aux`：seminormFromBounded_aux (f_nonneg : 0 <= f) (f_
mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : 0 <= c * f x
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for eve
ry `x : R`,
  `seminormFromBounded' f x` is bounded above by some multiple of `f x`.
-/
theorem seminormFromBounded_le (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x ≤ c * f x := by
  refine ciSup_le (fun y ↦ ?_)
  rcases (f_nonneg y).eq_or_lt' with hy | hy
  · simpa [hy] using seminormFromBounded_aux f_nonneg f_mul x
  · rw [div_le_iff₀ hy]
    apply f_mul

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `f x ≤ f 1 * seminormFromBounded' f x`. -/
/-
**seminormFromBounded_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_ge (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x *
 y) <= c * f x * f y) (x : R) : f x <= f 1 * seminormFromBounded' f x
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `seminormFromBounded_bddAbove_range`：seminormFromBounded_bddAbove_range (
f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) 
: BddAbove (Set.range fu…

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for eve
ry `x : R`,
  `f x ≤ f 1 * seminormFromBounded' f x`.
-/
theorem seminormFromBounded_ge (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    f x ≤ f 1 * seminormFromBounded' f x := by
  by_cases h1 : f 1 = 0
  · specialize f_mul x 1
    rw [mul_one, h1, mul_zero] at f_mul
    have hx0 : f x = 0 := f_mul.antisymm (f_nonneg _)
    rw [hx0, h1, zero_mul]
  · rw [mul_comm, ← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) h1)]
    conv_lhs => rw [← mul_one x]
    exact le_ciSup (seminormFromBounded_bddAbove_range f_nonneg f_mul x) (1 : R)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonnegative. -/
/-
**seminormFromBounded_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_nonneg (f_nonneg : 0 <= f) (f_mul : forall x y : R, f 
(x * y) <= c * f x * f y) : 0 <= seminormFromBounded' f
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup_of_le`：le_csSup_of_le (hs : BddAbove s) (hb : b in s) (h : a <=
 b) : a <= sSup s
· 使用定理 `seminormFromBounded_bddAbove_range`：seminormFromBounded_bddAbove_range (
f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) 
: BddAbove (Set.range fu…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonnegative.
-/
theorem seminormFromBounded_nonneg (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    0 ≤ seminormFromBounded' f := fun x ↦
  le_csSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) ⟨1, rfl⟩
    (div_nonneg (f_nonneg _) (f_nonneg _))

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f x = 0` if and only if `f x = 0`. -/
/-
**seminormFromBounded_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_eq_zero_iff (f_nonneg : 0 <= f) (f_mul : forall x y : 
R, f (x * y) <= c * f x * f y) (x : R) : seminormFromBounded' f x = 0 ↔ f x = 0
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `seminormFromBounded_ge`：seminormFromBounded_ge (f_nonneg : 0 <= f) (f_mu
l : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : f x <= f 1 * seminormF
romBounded' …
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `seminormFromBounded_le`：seminormFromBounded_le (f_nonneg : 0 <= f) (f_mu
l : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : seminormFromBounded' f
 x <= c * f …
· 使用定理 `seminormFromBounded_nonneg`：seminormFromBounded_nonneg (f_nonneg : 0 <= 
f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : 0 <= seminormFromBound
ed' f

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f x = 0` if and only if `f x = 0`.
-/
theorem seminormFromBounded_eq_zero_iff (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x = 0 ↔ f x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hf := seminormFromBounded_ge f_nonneg f_mul x
    rw [h, mul_zero] at hf
    exact hf.antisymm (f_nonneg _)
  · have hf : seminormFromBounded' f x ≤ c * f x :=
      seminormFromBounded_le f_nonneg f_mul x
    rw [h, mul_zero] at hf
    exact hf.antisymm (seminormFromBounded_nonneg f_nonneg f_mul x)

/-- If `f` is invariant under negation of `x`, then so is `seminormFromBounded'`. -/
/-
**seminormFromBounded_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_neg (f_neg : forall x : R, f (-x) = f x) (x : R) : sem
inormFromBounded' f (-x) = seminormFromBounded' f x
参数：f_neg : forall x : R, f (-x) = f x；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)

--- 原说明 ---
If `f` is invariant under negation of `x`, then so is `seminormFromBounded'`.
-/
theorem seminormFromBounded_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) :
    seminormFromBounded' f (-x) = seminormFromBounded' f x := by
  suffices ⨆ y, f (-x * y) / f y = ⨆ y, f (x * y) / f y by simpa only [seminormFromBounded']
  congr
  ext y
  rw [neg_mul, f_neg]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is submultiplicative. -/
/-
**seminormFromBounded_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_mul (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x 
* y) <= c * f x * f y) (x y : R) : seminormFromBounded' f (x * y) <= seminormFro
mBounded' f x * seminormFromBounded' f y
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul_zero_of_map_zero`：map_mul_zero_of_map_zero (f_nonneg : 0 <= f) (
f_mul : forall x y : R, f (x * y) <= c * f x * f y) {x : R} (hx : f x = 0) (y : 
R) : f (x * y)…
· 使用定理 `seminormFromBounded_eq_zero_iff`：seminormFromBounded_eq_zero_iff (f_nonn
eg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : semi
normFromBounded' f x …
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `seminormFromBounded_nonneg`：seminormFromBounded_nonneg (f_nonneg : 0 <= 
f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : 0 <= seminormFromBound
ed' f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `seminormFromBounded_bddAbove_range`：seminormFromBounded_bddAbove_range (
f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) 
: BddAbove (Set.range fu…
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is submultiplicative.
-/
theorem seminormFromBounded_mul (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x y : R) :
    seminormFromBounded' f (x * y) ≤ seminormFromBounded' f x * seminormFromBounded' f y := by
  apply ciSup_le
  by_cases hy : seminormFromBounded' f y = 0
  · rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul] at hy
    intro z
    rw [mul_comm x y, mul_assoc, map_mul_zero_of_map_zero f_nonneg f_mul hy (x * z), zero_div]
    exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul x)
      (seminormFromBounded_nonneg f_nonneg f_mul y)
  · intro z
    rw [← div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]
    apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z
    rw [div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy),
      div_mul_eq_mul_div]
    by_cases hz : f z = 0
    · have hxyz : f (z * (x * y)) = 0 := map_mul_zero_of_map_zero f_nonneg f_mul hz _
      simp_rw [mul_comm, hxyz, zero_div]
      exact div_nonneg (mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _))
        (f_nonneg _)
    · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))]
      by_cases hxz : f (x * z) = 0
      · rw [mul_comm x y, mul_assoc, mul_comm y, map_mul_zero_of_map_zero f_nonneg f_mul hxz y]
        exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _)
      · rw [← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hxz)]
        apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) (x * z)
        rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hxz), mul_comm x y, mul_assoc]

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 = 1`. -/
/-
**seminormFromBounded_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_one (f_ne_zero : f != 0) (f_nonneg : 0 <= f) (f_mul : 
forall x y : R, f (x * y) <= c * f x * f y) : seminormFromBounded' f 1 = 1
参数：f_ne_zero : f != 0；f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c *
 f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one_ne_zero`：map_one_ne_zero (f_ne_zero : f != 0) (f_nonneg : 0 <= f
) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : f 1 != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f

--- 原说明 ---
If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, the
n
  `seminormFromBounded' f 1 = 1`.
-/
theorem seminormFromBounded_one (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 = 1 := by
  simp_rw [seminormFromBounded', one_mul]
  apply le_antisymm
  · refine ciSup_le (fun x ↦ ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero]; exact zero_le_one
    · rw [div_self hx]
  · rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
    have h_bdd : BddAbove (Set.range fun y ↦ f y / f y) := by
      use (1 : ℝ)
      rintro r ⟨y, rfl⟩
      by_cases hy : f y = 0
      · simp only [hy, div_zero, zero_le_one]
      · simp only [div_self hy, le_refl]
    exact le_ciSup h_bdd (1 : R)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 ≤ 1`. -/
/-
**seminormFromBounded_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_one_le (f_nonneg : 0 <= f) (f_mul : forall x y : R, f 
(x * y) <= c * f x * f y) : seminormFromBounded' f 1 <= 1
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `seminormFromBounded_one`：seminormFromBounded_one (f_ne_zero : f != 0) (f
_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : seminor
mFromBounded'…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 ≤ 1`.
-/
theorem seminormFromBounded_one_le (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 ≤ 1 := by
  by_cases! f_ne_zero : f ≠ 0
  · exact le_of_eq (seminormFromBounded_one f_ne_zero f_nonneg f_mul)
  · simp_rw [seminormFromBounded', one_mul]
    refine ciSup_le (fun _ ↦ ?_)
    simp only [f_ne_zero, Pi.zero_apply, div_zero, zero_le_one]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function, then
  `seminormFromBounded' f` is subadditive. -/
/-
**seminormFromBounded_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_add (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x 
* y) <= c * f x * f y) (f_add : forall a b, f (a + b) <= f a + f b) (x y : R) : 
seminormFromBounded' f (x + y) <= seminormFromBounded' f x + seminormFromBounded
' f y
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；f_add : 
forall a b, f (a + b) <= f a + f b；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `seminormFromBounded_bddAbove_range`：seminormFromBounded_bddAbove_range (
f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) 
: BddAbove (Set.range fu…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function,
 then
  `seminormFromBounded' f` is subadditive.
-/
theorem seminormFromBounded_add (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (x y : R) :
    seminormFromBounded' f (x + y) ≤ seminormFromBounded' f x + seminormFromBounded' f y := by
  refine ciSup_le (fun z ↦ ?_)
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z + f (y * z) / f z by
    exact le_trans hf (add_le_add
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z (le_refl _))
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z (le_refl _)))
  by_cases hz : f z = 0
  · simp only [hz, div_zero, zero_add, le_refl]
  · rw [← add_div, div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul]
    exact f_add _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- `seminormFromBounded'` is a ring seminorm on `R`. -/
/-
**seminormFromBounded** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：seminormFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 <= f) (f_mul : forall
 x y : R, f (x * y) <= c * f x * f y) (f_add : forall a b, f (a + b) <= f a + f 
b) (f_neg : forall x : R, f (-x) = f x) : RingSeminorm R where toFun
参数：f_zero : f 0 = 0；f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f
 x * f y；f_add : forall a b, f (a + b) <= f a + f b；f_neg : forall x : R, f (-x)
 = f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `seminormFromBounded_zero`：seminormFromBounded_zero (f_zero : f 0 = 0) : 
seminormFromBounded' f (0 : R) = 0
· 使用定理 `seminormFromBounded_add`：seminormFromBounded_add (f_nonneg : 0 <= f) (f_
mul : forall x y : R, f (x * y) <= c * f x * f y) (f_add : forall a b, f (a + b)
 <= f a + f b…
· 使用定理 `seminormFromBounded_neg`：seminormFromBounded_neg (f_neg : forall x : R, 
f (-x) = f x) (x : R) : seminormFromBounded' f (-x) = seminormFromBounded' f x
· 使用定理 `seminormFromBounded_mul`：seminormFromBounded_mul (f_nonneg : 0 <= f) (f_
mul : forall x y : R, f (x * y) <= c * f x * f y) (x y : R) : seminormFromBounde
d' f (x * y) …

--- 原说明 ---
`seminormFromBounded'` is a ring seminorm on `R`.
-/
def seminormFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) : RingSeminorm R where
  toFun     := seminormFromBounded' f
  map_zero' := seminormFromBounded_zero f_zero
  add_le'   := seminormFromBounded_add f_nonneg f_mul f_add
  mul_le'   := seminormFromBounded_mul f_nonneg f_mul
  neg'      := seminormFromBounded_neg f_neg

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, nonarchimedean function, then
  `seminormFromBounded' f` is nonarchimedean. -/
/-
**seminormFromBounded_isNonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_isNonarchimedean (f_nonneg : 0 <= f) (f_mul : forall x
 y : R, f (x * y) <= c * f x * f y) (hna : IsNonarchimedean f) : IsNonarchimedea
n (seminormFromBounded' f)
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；hna : Is
Nonarchimedean f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `seminormFromBounded_bddAbove_range`：seminormFromBounded_bddAbove_range (
f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) 
: BddAbove (Set.range fu…

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded, nonarchimedean functi
on, then
  `seminormFromBounded' f` is nonarchimedean.
-/
theorem seminormFromBounded_isNonarchimedean (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (hna : IsNonarchimedean f) : IsNonarchimedean (seminormFromBounded' f) := by
  refine fun x y ↦ ciSup_le (fun z ↦ ?_)
  rw [le_max_iff]
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z ∨ f ((x + y) * z) / f z ≤ f (y * z) / f z by
    rcases hf with hfx | hfy
    · exact Or.inl <| le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z hfx
    · exact Or.inr <| le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z hfy
  by_cases hz : f z = 0
  · simp only [hz, div_zero, le_refl, or_self_iff]
  · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz),
      div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff]
    exact hna _ _

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `seminormFromBounded' f x = f x`. -/
/-
**seminormFromBounded_of_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_of_mul_apply (f_nonneg : 0 <= f) (f_mul : forall x y :
 R, f (x * y) <= c * f x * f y) {x : R} (hx : forall y : R, f (x * y) = f x * f 
y) : seminormFromBounded' f x = f x
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；hx : for
all y : R, f (x * y) = f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one_ne_zero`：map_one_ne_zero (f_ne_zero : f != 0) (f_nonneg : 0 <= f
) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : f 1 != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` i
s
  multiplicative for `f`, then `seminormFromBounded' f x = f x`.
-/
theorem seminormFromBounded_of_mul_apply (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded', hx, ← mul_div_assoc']
  apply le_antisymm
  · refine ciSup_le (fun x ↦ ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero, mul_zero]; exact f_nonneg _
    · rw [div_self hx, mul_one]
  · by_cases! f_ne_zero : f ≠ 0
    · conv_lhs => rw [← mul_one (f x)]
      rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
      have h_bdd : BddAbove (Set.range fun y ↦ f x * (f y / f y)) := by
        use f x
        rintro r ⟨y, rfl⟩
        by_cases hy0 : f y = 0
        · simp only [hy0, div_zero, mul_zero]; exact f_nonneg _
        · simp only [div_self hy0, mul_one, le_refl]
      exact le_ciSup h_bdd (1 : R)
    · simp_rw [f_ne_zero, Pi.zero_apply, zero_div, zero_mul, ciSup_const]; rfl

/-- If `f : R → ℝ` is a nonnegative function and `x : R` is submultiplicative for `f`, then
  `seminormFromBounded' f x = f x`. -/
/-
**seminormFromBounded_of_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_of_mul_le (f_nonneg : 0 <= f) {x : R} (hx : forall y :
 R, f (x * y) <= f x * f y) (h_one : f 1 <= 1) : seminormFromBounded' f x = f x
参数：f_nonneg : 0 <= f；hx : forall y : R, f (x * y) <= f x * f y；h_one : f 1 <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `le_mul_iff_one_le_right`：le_mul_iff_one_le_right [PosMulMono α] [PosMulR
eflectLE α] (a0 : 0 < a) : a <= a * b ↔ 1 <= b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f

--- 原说明 ---
If `f : R → ℝ` is a nonnegative function and `x : R` is submultiplicative for `f
`, then
  `seminormFromBounded' f x = f x`.
-/
theorem seminormFromBounded_of_mul_le (f_nonneg : 0 ≤ f) {x : R}
    (hx : ∀ y : R, f (x * y) ≤ f x * f y) (h_one : f 1 ≤ 1) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded']
  apply le_antisymm
  · refine ciSup_le (fun y ↦ ?_)
    by_cases hy : f y = 0
    · rw [hy, div_zero]; exact f_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy)]; exact hx _
  · have h_bdd : BddAbove (Set.range fun y ↦ f (x * y) / f y) := by
      use f x
      rintro r ⟨y, rfl⟩
      by_cases hy0 : f y = 0
      · simp only [hy0, div_zero]
        exact f_nonneg _
      · rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc,
          div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one]
        exact hx y
    convert! le_ciSup h_bdd (1 : R)
    by_cases h0 : f x = 0
    · rw [mul_one, h0, zero_div]
    · have heq : f 1 = 1 := by
        apply h_one.antisymm
        specialize hx 1
        rw [mul_one, le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (Ne.symm h0))] at hx
        exact hx
      rw [heq, mul_one, div_one]

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonzero. -/
/-
**seminormFromBounded_nonzero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_nonzero (f_ne_zero : f != 0) (f_nonneg : 0 <= f) (f_mu
l : forall x y : R, f (x * y) <= c * f x * f y) : seminormFromBounded' f != 0
参数：f_ne_zero : f != 0；f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c *
 f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `seminormFromBounded_eq_zero_iff`：seminormFromBounded_eq_zero_iff (f_nonn
eg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : semi
normFromBounded' f x …

--- 原说明 ---
If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, the
n
  `seminormFromBounded' f` is nonzero.
-/
theorem seminormFromBounded_nonzero (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp f_ne_zero
  rw [Function.ne_iff]
  use x
  rw [ne_eq, Pi.zero_apply, seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then the kernel of
  `seminormFromBounded' f` equals the kernel of `f`. -/
/-
**seminormFromBounded_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_ker (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x 
* y) <= c * f x * f y) : seminormFromBounded' f ⁻¹' {0} = f ⁻¹' {0}
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `seminormFromBounded_eq_zero_iff`：seminormFromBounded_eq_zero_iff (f_nonn
eg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : semi
normFromBounded' f x …

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then the ker
nel of
  `seminormFromBounded' f` equals the kernel of `f`.
-/
theorem seminormFromBounded_ker (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ⁻¹' {0} = f ⁻¹' {0} := by
  ext x
  exact seminormFromBounded_eq_zero_iff f_nonneg f_mul x

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function that preserves
  zero and negation, then `seminormFromBounded' f` is a norm if and only if `f⁻¹' {0} = {0}`. -/
/-
**seminormFromBounded_is_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : 0 <= f) (f_
mul : forall x y : R, f (x * y) <= c * f x * f y) (f_add : forall a b, f (a + b)
 <= f a + f b) (f_neg : forall x : R, f (-x) = f x) : (forall x : R, (seminormFr
omBounded f_zero f_nonneg f_mul f_add f_neg).toFun x = 0 -> x = 0) ↔ f ⁻¹' {0} =
 {0}
参数：f_zero : f 0 = 0；f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f
 x * f y；f_add : forall a b, f (a + b) <= f a + f b；f_neg : forall x : R, f (-x)
 = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `seminormFromBounded_ker`：seminormFromBounded_ker (f_nonneg : 0 <= f) (f_
mul : forall x y : R, f (x * y) <= c * f x * f y) : seminormFromBounded' f ⁻¹' {
0} = f ⁻¹' {0…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `seminormFromBounded_zero`：seminormFromBounded_zero (f_zero : f 0 = 0) : 
seminormFromBounded' f (0 : R) = 0
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `seminormFromBounded_eq_zero_iff`：seminormFromBounded_eq_zero_iff (f_nonn
eg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : semi
normFromBounded' f x …

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function 
that preserves
  zero and negation, then `seminormFromBounded' f` is a norm if and only if `f⁻¹
' {0} = {0}`.
-/
theorem seminormFromBounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) :
    (∀ x : R, (seminormFromBounded f_zero f_nonneg f_mul f_add f_neg).toFun x = 0 → x = 0) ↔
      f ⁻¹' {0} = {0} := by
  refine ⟨fun h0 ↦ ?_, fun h_ker x hx ↦ ?_⟩
  · rw [← seminormFromBounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ h0 x h, fun h ↦ by rw [h]; exact seminormFromBounded_zero f_zero⟩
  · rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff,
      ← seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

/-- `seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is nonnegative,
  multiplicatively bounded and subadditive, that it preserves `0` and negation, and that `f` has
  trivial kernel. -/
/-
**normFromBounded** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 <= f) (f_mul : forall x y
 : R, f (x * y) <= c * f x * f y) (f_add : forall a b, f (a + b) <= f a + f b) (
f_neg : forall x : R, f (-x) = f x) (f_ker : f ⁻¹' {0} = {0}) : RingNorm R
参数：f_zero : f 0 = 0；f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f
 x * f y；f_add : forall a b, f (a + b) <= f a + f b；f_neg : forall x : R, f (-x)
 = f x；f_ker : f ⁻¹' {0} = {0}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is nonnegativ
e,
  multiplicatively bounded and subadditive, that it preserves `0` and negation, 
and that `f` has
  trivial kernel.
-/
def normFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x)
    (f_ker : f ⁻¹' {0} = {0}) : RingNorm R :=
  { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `x` is multiplicative for `seminormFromBounded' f`. -/
/-
**seminormFromBounded_of_mul_is_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seminormFromBounded_of_mul_is_mul (f_nonneg : 0 <= f) (f_mul : forall x y 
: R, f (x * y) <= c * f x * f y) {x : R} (hx : forall y : R, f (x * y) = f x * f
 y) (y : R) : seminormFromBounded' f (x * y) = seminormFromBounded' f x * semino
rmFromBounded' f y
参数：f_nonneg : 0 <= f；f_mul : forall x y : R, f (x * y) <= c * f x * f y；hx : for
all y : R, f (x * y) = f x * f y；y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `seminormFromBounded_of_mul_apply`：seminormFromBounded_of_mul_apply (f_no
nneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) {x : R} (hx 
: forall y : R, f (x *…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Real.mul_iSup_of_nonneg`：Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨆ i, f i) = ⨆ i, r * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` i
s
  multiplicative for `f`, then `x` is multiplicative for `seminormFromBounded' f
`.
-/
theorem seminormFromBounded_of_mul_is_mul (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromBounded' f (x * y) = seminormFromBounded' f x * seminormFromBounded' f y := by
  rw [seminormFromBounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

end seminormFromBounded

