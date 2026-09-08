/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Data.ENNReal.Inv

/-! # Hölder triples

This file defines a new class: `ENNReal.HolderTriple` which takes arguments `p q r : ℝ≥0∞`,
with `r` marked as a `semiOutParam`, and states that `p⁻¹ + q⁻¹ = r⁻¹`. This is exactly the
condition for which **Hölder's inequality** is valid (see `MeasureTheory.MemLp.smul`).
This allows us to declare a heterogeneous scalar multiplication (`HSMul`) instance on
`MeasureTheory.Lp` spaces.

In this file we provide many convenience lemmas in the presence of a `HolderTriple` instance.
All these are easily provable from facts about `ℝ≥0∞`, but it's convenient not to be forced
to reprove them each time.

For convenience we also define `ENNReal.HolderConjugate` (with arguments `p q`) as an
abbreviation for `ENNReal.HolderTriple p q 1`.
-/

public section

namespace ENNReal

/-- A class stating that `p q r : ℝ≥0∞` satisfy `p⁻¹ + q⁻¹ = r⁻¹`.
This is exactly the condition for which **Hölder's inequality** is valid
(see `MeasureTheory.MemLp.smul`).

When `r := 1`, one generally says that `p q` are **Hölder conjugate**.

This class exists so that we can define a heterogeneous scalar multiplication
on `MeasureTheory.Lp`, and this is why `r` must be marked as a
`semiOutParam`. We don't mark it as an `outParam` because this would
prevent Lean from using `HolderTriple p q r` and `HolderTriple p q r'`
within a single proof, as may be occasionally convenient. -/
@[mk_iff]
/-
**ENNReal.HolderTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 `ENNReal`。
形式化陈述：ENNReal → ENNReal → semiOutParam ENNReal → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class stating that `p q r : ℝ≥0∞` satisfy `p⁻¹ + q⁻¹ = r⁻¹`.
This is exactly the condition for which **Hölder's inequality** is valid
(see `MeasureTheory.MemLp.smul`).

When `r := 1`, one generally says that `p q` are **Hölder conjugate**.

This class exists so that we can define a heterogeneous scalar multiplication
on `MeasureTheory.Lp`, and this is why `r` must be marked as a
`semiOutParam`. We don't mark it as an `outParam` because this would
prevent Lean from using `HolderTriple p q r` and `HolderTriple p q r'`
within a single proof, as may be occasionally convenient.
-/
class HolderTriple (p q : ℝ≥0∞) (r : semiOutParam ℝ≥0∞) : Prop where
  inv_add_inv_eq_inv (p q r) : p⁻¹ + q⁻¹ = r⁻¹

/-- An abbreviation for `ENNReal.HolderTriple p q 1`, this class states `p⁻¹ + q⁻¹ = 1`. -/
/-
**ENNReal.HolderConjugate** 是 Mathlib 中的一个缩写定义，位于命名空间 `ENNReal`。
形式化陈述：HolderConjugate (p q : Real>=0∞)
参数：p q : Real>=0∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `ENNReal.HolderTriple p q 1`, this class states `p⁻¹ + q⁻¹ =
 1`.
-/
abbrev HolderConjugate (p q : ℝ≥0∞) := HolderTriple p q 1
/-
**ENNReal.holderConjugate_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：holderConjugate_iff {p q : Real>=0∞} : HolderConjugate p q ↔ p⁻¹ + q⁻¹ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma holderConjugate_iff {p q : ℝ≥0∞} : HolderConjugate p q ↔ p⁻¹ + q⁻¹ = 1 := by
  simp [holderTriple_iff]

/-! ### Hölder triples -/

namespace HolderTriple

/-- This is not marked as an instance so that Lean doesn't always find this one
and a more canonical value of `r` can be used. -/
/-
**ENNReal.HolderTriple.of** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple`。
形式化陈述：of (p q : Real>=0∞) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where .symm inv_add_i
nv_eq_inv
参数：p q : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
This is not marked as an instance so that Lean doesn't always find this one
and a more canonical value of `r` can be used.
-/
lemma of (p q : ℝ≥0∞) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv_eq_inv := inv_inv _ |>.symm

/- This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid. -/
/-
**ENNReal.HolderTriple.symm** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.HolderTriple`。
形式化陈述：symm {p q r : Real>=0∞} [hpqr : HolderTriple p q r] : HolderTriple q p r w
here inv_add_inv_eq_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid.
-/
instance symm {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r] : HolderTriple q p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ hpqr.inv_add_inv_eq_inv
/-
**ENNReal.HolderTriple.instInfty** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.HolderTriple
`。
形式化陈述：instInfty (p : Real>=0∞) : HolderTriple p ∞ p where inv_add_inv_eq_inv
参数：p : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instInfty (p : ℝ≥0∞) : HolderTriple p ∞ p where
  inv_add_inv_eq_inv := by simp
/-
**ENNReal.HolderTriple.instZero** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.HolderTriple`
。
形式化陈述：instZero (p : Real>=0∞) : HolderTriple p 0 0 where inv_add_inv_eq_inv
参数：p : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instZero (p : ℝ≥0∞) : HolderTriple p 0 0 where
  inv_add_inv_eq_inv := by simp

variable (p q r : ℝ≥0∞) [HolderTriple p q r]
/-
**ENNReal.HolderTriple.inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple`。
形式化陈述：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
-/
lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := (inv_add_inv_eq_inv ..).symm
/-
**ENNReal.HolderTriple.unique** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple`。
形式化陈述：unique (r' : Real>=0∞) [hr' : HolderTriple p q r'] : r = r'
参数：r' : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用引理 `ENNReal.HolderTriple.inv_eq`：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
-/
lemma unique (r' : ℝ≥0∞) [hr' : HolderTriple p q r'] : r = r' := by
  rw [← inv_inj, inv_eq p q r, inv_eq p q r']
/-
**ENNReal.HolderTriple.one_div_add_one_div** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Ho
lderTriple`。
形式化陈述：one_div_add_one_div : 1 / p + 1 / q = 1 / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
-/
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by simpa using inv_add_inv_eq_inv ..
/-
**ENNReal.HolderTriple.one_div_eq** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTripl
e`。
形式化陈述：one_div_eq : 1 / r = 1 / p + 1 / q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.HolderTriple.one_div_add_one_div`：one_div_add_one_div : 1 / p + 
1 / q = 1 / r
-/
lemma one_div_eq : 1 / r = 1 / p + 1 / q :=
  one_div_add_one_div p q r |>.symm
/-
**ENNReal.HolderTriple.inv_inv_add_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Holder
Triple`。
形式化陈述：inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by
  simp [inv_add_inv_eq_inv p q r]

include q in
/-
**ENNReal.HolderTriple.le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple`。
形式化陈述：le : r <= p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.HolderTriple.inv_inv_add_inv`：inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = 
r
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma le : r ≤ p := by
  simp [← ENNReal.inv_le_inv, ← @inv_inv_add_inv p q r, inv_inv]

include q in
/-
**ENNReal.HolderTriple.inv_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.HolderTripl
e`。
形式化陈述：∀ (p q r : ENNReal) [p.HolderTriple q r], p⁻¹ ≤ r⁻¹
参数：p q r : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ENNReal.HolderTriple.le`：le : r <= p
-/
protected lemma inv_le_inv : p⁻¹ ≤ r⁻¹ := by
  simp [ENNReal.inv_le_inv, le p q r]

variable {r} in
/-
**ENNReal.HolderTriple.inv_sub_inv_eq_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Hol
derTriple`。
形式化陈述：inv_sub_inv_eq_inv (hr : r != 0) : r⁻¹ - q⁻¹ = p⁻¹
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.sub_eq_of_eq_add`：∀ {a b c : ENNReal}, b ≠ ⊤ → a = c + b → a - b
 = c
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ENNReal.HolderTriple.inv_le_inv`：∀ (p q r : ENNReal) [p.HolderTriple q r
], p⁻¹ ≤ r⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `ENNReal.HolderTriple.inv_eq`：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
-/
lemma inv_sub_inv_eq_inv (hr : r ≠ 0) : r⁻¹ - q⁻¹ = p⁻¹ := by
  apply ENNReal.sub_eq_of_eq_add (ne_of_lt ?_) (inv_eq p q r)
  calc
    q⁻¹ ≤ r⁻¹ := HolderTriple.inv_le_inv q p r
    _ < ∞ := by simpa using pos_iff_ne_zero.mpr hr

/-- assumes `q ≠ 0` instead of `r ≠ 0`. -/
/-
**ENNReal.HolderTriple.inv_sub_inv_eq_inv'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Ho
lderTriple`。
形式化陈述：inv_sub_inv_eq_inv' (hq : q != 0) : r⁻¹ - q⁻¹ = p⁻¹
参数：hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ENNReal.HolderTriple.inv_eq`：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.HolderTriple.inv_sub_inv_eq_inv`：inv_sub_inv_eq_inv (hr : r != 0
) : r⁻¹ - q⁻¹ = p⁻¹
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
assumes `q ≠ 0` instead of `r ≠ 0`.
-/
lemma inv_sub_inv_eq_inv' (hq : q ≠ 0) : r⁻¹ - q⁻¹ = p⁻¹ := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · suffices p = 0 by simpa [this]
    by_contra! hp
    have := calc
      0⁻¹ = p⁻¹ + q⁻¹ := inv_eq p q 0
      _ < ⊤ + ⊤ := by simp [hp, hq, pos_iff_ne_zero]
      _ = ⊤ := by simp
    simp_all
  · exact inv_sub_inv_eq_inv p q hr.ne'

variable {r} in
/-
**ENNReal.HolderTriple.unique_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Hold
erTriple`。
形式化陈述：unique_of_ne_zero (q' : Real>=0∞) (hr : r != 0) [HolderTriple p q' r] : q 
= q'
参数：q' : Real>=0∞；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用引理 `ENNReal.HolderTriple.inv_sub_inv_eq_inv`：inv_sub_inv_eq_inv (hr : r != 0
) : r⁻¹ - q⁻¹ = p⁻¹
-/
lemma unique_of_ne_zero (q' : ℝ≥0∞) (hr : r ≠ 0) [HolderTriple p q' r] : q = q' := by
  rw [← inv_inj, ← inv_sub_inv_eq_inv q p hr, ← inv_sub_inv_eq_inv q' p hr]
/-
**ENNReal.HolderTriple.holderConjugate_div_div** 是 Mathlib 中的一个引理，位于命名空间 `ENNRea
l.HolderTriple`。
形式化陈述：holderConjugate_div_div (hr₀ : r != 0) (hr : r != ∞) : HolderConjugate (p 
/ r) (q / r) where inv_add_inv_eq_inv
参数：hr₀ : r != 0；hr : r != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_div`：∀ {a b : ENNReal}, b ≠ ⊤ ∨ a ≠ ⊤ → b ≠ 0 ∨ a ≠ 0 → (a /
 b)⁻¹ = b / a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma holderConjugate_div_div (hr₀ : r ≠ 0) (hr : r ≠ ∞) : HolderConjugate (p / r) (q / r) where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀), ENNReal.inv_div (.inl hr) (.inl hr₀), div_eq_mul_inv,
      div_eq_mul_inv, ← mul_add, inv_add_inv_eq_inv p q r, ENNReal.mul_inv_cancel hr₀ hr, inv_one]

end HolderTriple

/-! ### Hölder conjugates -/

namespace HolderConjugate

/- This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid. -/
/-
**ENNReal.HolderConjugate.symm** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.HolderConjugat
e`。
形式化陈述：symm {p q : Real>=0∞} [hpq : HolderConjugate p q] : HolderConjugate q p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid.
-/
instance symm {p q : ℝ≥0∞} [hpq : HolderConjugate p q] : HolderConjugate q p :=
  inferInstance
/-
**ENNReal.HolderConjugate.instTwoTwo** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.HolderCo
njugate`。
形式化陈述：instTwoTwo : HolderConjugate 2 2 where inv_add_inv_eq_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instTwoTwo : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by
    rw [← two_mul, ENNReal.mul_inv_cancel]
    all_goals norm_num

-- I'm not sure this is necessary, but maybe it's nice to have around given the `abbrev`.
/-
**ENNReal.HolderConjugate.instOneInfty** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.Holder
Conjugate`。
形式化陈述：instOneInfty : HolderConjugate 1 ∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOneInfty : HolderConjugate 1 ∞ := inferInstance

variable (p q : ℝ≥0∞) [HolderConjugate p q]

include q in
/-
**ENNReal.HolderConjugate.one_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConjug
ate`。
形式化陈述：one_le : 1 <= p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderTriple.le`：le : r <= p
-/
lemma one_le : 1 ≤ p := HolderTriple.le p q 1

include q in
/-
**ENNReal.HolderConjugate.pos** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConjugate
`。
形式化陈述：pos : 0 < p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.HolderConjugate.one_le`：one_le : 1 <= p
-/
lemma pos : 0 < p := zero_lt_one.trans_le (one_le p q)

include q in
/-
**ENNReal.HolderConjugate.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.HolderConju
gate`。
形式化陈述：∀ (p q : ENNReal) [p.HolderConjugate q], p ≠ 0
参数：p q : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ENNReal.HolderConjugate.pos`：pos : 0 < p
-/
lemma ne_zero : p ≠ 0 := pos p q |>.ne'
/-
**ENNReal.HolderConjugate.inv_add_inv_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.
HolderConjugate`。
形式化陈述：inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := @inv_one ℝ≥0∞ _ ▸ HolderTriple.inv_add_inv_eq_inv p q 1
/-
**ENNReal.HolderConjugate.one_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderC
onjugate`。
形式化陈述：one_sub_inv : 1 - p⁻¹ = q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderTriple.inv_sub_inv_eq_inv`：inv_sub_inv_eq_inv (hr : r != 0
) : r⁻¹ - q⁻¹ = p⁻¹
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ :=
  @inv_one ℝ≥0∞ _ ▸ HolderTriple.inv_sub_inv_eq_inv q p one_ne_zero
/-
**ENNReal.HolderConjugate.unique** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConjug
ate`。
形式化陈述：unique (q' : Real>=0∞) [hq' : HolderConjugate p q'] : q = q'
参数：q' : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderTriple.unique_of_ne_zero`：unique_of_ne_zero (q' : Real>=0∞
) (hr : r != 0) [HolderTriple p q' r] : q = q'
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
lemma unique (q' : ℝ≥0∞) [hq' : HolderConjugate p q'] : q = q' :=
  HolderTriple.unique_of_ne_zero p q q' one_ne_zero
/-
**ENNReal.HolderConjugate.eq_top_iff_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.H
olderConjugate`。
形式化陈述：eq_top_iff_eq_one : p = ∞ ↔ q = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `ENNReal.HolderConjugate.one_sub_inv`：one_sub_inv : 1 - p⁻¹ = q⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
-/
lemma eq_top_iff_eq_one : p = ∞ ↔ q = 1 := by
  constructor
  · rintro rfl
    rw [← inv_inv q, ← one_sub_inv ∞ q]
    simp
  · rintro rfl
    rw [← inv_inv p, ← one_sub_inv 1 p]
    simp
/-
**ENNReal.HolderConjugate.ne_top_iff_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.H
olderConjugate`。
形式化陈述：ne_top_iff_ne_one : p != ∞ ↔ q != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `ENNReal.HolderConjugate.eq_top_iff_eq_one`：eq_top_iff_eq_one : p = ∞ ↔ q
 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ne_top_iff_ne_one : p ≠ ∞ ↔ q ≠ 1 := by
  rw [not_iff_not, eq_top_iff_eq_one p q]
/-
**ENNReal.HolderConjugate.lt_top_iff_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.H
olderConjugate`。
形式化陈述：lt_top_iff_one_lt : p < ∞ ↔ 1 < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `ENNReal.HolderConjugate.ne_top_iff_ne_one`：ne_top_iff_ne_one : p != ∞ ↔ 
q != 1
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ENNReal.HolderConjugate.one_le`：one_le : 1 <= p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_top_iff_one_lt : p < ∞ ↔ 1 < q := by
  rw [lt_top_iff_ne_top, ne_top_iff_ne_one _ q, ne_comm, lt_iff_le_and_ne]
  simp [one_le q p]
/-
**ENNReal.HolderConjugate.sub_one_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Hol
derConjugate`。
形式化陈述：sub_one_mul_inv (hp : p != ⊤) : (p - 1) * p⁻¹ = q⁻¹
参数：hp : p != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ENNReal.HolderConjugate.pos`：pos : 0 < p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.sub_mul`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) 
* c = a * c - b * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `ENNReal.HolderConjugate.one_sub_inv`：one_sub_inv : 1 - p⁻¹ = q⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_one_mul_inv (hp : p ≠ ⊤) : (p - 1) * p⁻¹ = q⁻¹ := by
  have := pos p q |>.ne'
  rw [ENNReal.sub_mul (by simp_all), ENNReal.mul_inv_cancel this (by lia)]
  simp [one_sub_inv p q]

end HolderConjugate

end ENNReal

