/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith

/-!
# Absolute value in `ZMod n`
-/

@[expose] public section

namespace ZMod
variable {n : ℕ} {a b : ZMod n}

/-- Returns the integer in the same equivalence class as `x` that is closest to `0`.

The result will be in the interval `(-n/2, n/2]`. -/
/-
**ZMod.valMinAbs** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：{n : ℕ} → ZMod n → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the integer in the same equivalence class as `x` that is closest to `0`.

The result will be in the interval `(-n/2, n/2]`.
-/
def valMinAbs : ∀ {n : ℕ}, ZMod n → ℤ
  | 0, x => x
  | n@(_ + 1), x => if x.val ≤ n / 2 then x.val else (x.val : ℤ) - n
/-
**ZMod.valMinAbs_def_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (x : ZMod 0), x.valMinAbs = x
参数：x : ZMod 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma valMinAbs_def_zero (x : ZMod 0) : valMinAbs x = x := rfl
/-
**ZMod.valMinAbs_def_pos** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs = if x.val ≤ n / 2 then ↑x.
val else ↑x.val - ↑n
参数：x : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma valMinAbs_def_pos : ∀ {n : ℕ} [NeZero n] (x : ZMod n),
    valMinAbs x = if x.val ≤ n / 2 then (x.val : ℤ) else x.val - n
  | 0, _, x => by cases NeZero.ne 0 rfl
  | n + 1, _, x => rfl

@[simp, norm_cast]
/-
**ZMod.coe_valMinAbs** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
参数：x : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_id`：∀ {n : ℤ}, ↑n = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma coe_valMinAbs : ∀ {n : ℕ} (x : ZMod n), (x.valMinAbs : ZMod n) = x
  | 0, _ => Int.cast_id
  | k@(n + 1), x => by
    rw [valMinAbs_def_pos]
    split_ifs
    · rw [Int.cast_natCast, natCast_zmod_val]
    · rw [Int.cast_sub, Int.cast_natCast, natCast_zmod_val, Int.cast_natCast, natCast_self,
        sub_zero]
/-
**ZMod.injective_valMinAbs** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：injective_valMinAbs : (valMinAbs : ZMod n -> Int).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.injective_iff_hasLeftInverse`：injective_iff_hasLeftInverse : In
jective f ↔ HasLeftInverse f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
-/
lemma injective_valMinAbs : (valMinAbs : ZMod n → ℤ).Injective :=
  Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩

@[simp]
/-
**ZMod.valMinAbs_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_inj : a.valMinAbs = b.valMinAbs ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ZMod.injective_valMinAbs`：injective_valMinAbs : (valMinAbs : ZMod n -> I
nt).Injective
-/
theorem valMinAbs_inj : a.valMinAbs = b.valMinAbs ↔ a = b :=
  ZMod.injective_valMinAbs.eq_iff
/-
**ZMod.valMinAbs_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_nonneg_iff [NeZero n] (x : ZMod n) : 0 <= x.valMinAbs ↔ x.val <=
 n / 2
参数：x : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRigh
tStrictMono α] {a b : α}, a - b < 0 ↔ a < b
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
-/
lemma valMinAbs_nonneg_iff [NeZero n] (x : ZMod n) : 0 ≤ x.valMinAbs ↔ x.val ≤ n / 2 := by
  rw [valMinAbs_def_pos]; split_ifs with h
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_ge h

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.valMinAbs_mul_two_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_mul_two_eq_iff (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = 
n
参数：a : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `mul_nonneg_iff_left_nonneg_of_pos`：mul_nonneg_iff_left_nonneg_of_pos [Po
sMulStrictMono R] [MulPosStrictMono R] (hb : 0 < b) : 0 <= a * b ↔ 0 <= a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用引理 `ZMod.valMinAbs_nonneg_iff`：valMinAbs_nonneg_iff [NeZero n] (x : ZMod n) 
: 0 <= x.valMinAbs ↔ x.val <= n / 2
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
（共 37 条，此处仅展示前 30 条）
-/
lemma valMinAbs_mul_two_eq_iff (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = n := by
  rcases n with - | n
  · simp
  by_cases h : a.val ≤ n.succ / 2
  · dsimp [valMinAbs]
    rw [if_pos h, ← Int.natCast_inj, Nat.cast_mul, Nat.cast_two, mul_comm, Int.natCast_add,
      Nat.cast_one]
  apply iff_of_false _ (mt _ h)
  · intro he
    rw [← a.valMinAbs_nonneg_iff, ← mul_nonneg_iff_left_nonneg_of_pos, he] at h
    exacts [h (Nat.cast_nonneg _), zero_lt_two]
  · rw [mul_comm]
    exact fun h => (Nat.le_div_iff_mul_le zero_lt_two).2 h.le
/-
**ZMod.valMinAbs_mem_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.valMinAbs * 2 in Set.Ioc (-n
 : Int) n
参数：x : ZMod n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
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
（共 71 条，此处仅展示前 30 条）
-/
lemma valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.valMinAbs * 2 ∈ Set.Ioc (-n : ℤ) n := by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  · exact ⟨(neg_lt_zero.2 <| mod_cast NeZero.pos n).trans_le (by positivity), h⟩
  · refine ⟨?_, le_trans (mul_nonpos_of_nonpos_of_nonneg ?_ zero_le_two) <| Nat.cast_nonneg _⟩
    · linarith only [h]
    · grind
/-
**ZMod.valMinAbs_spec** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_spec [NeZero n] (x : ZMod n) (y : Int) : x.valMinAbs = y ↔ x = y
 ∧ y * 2 in Set.Ioc (-n : Int) n where mp
参数：x : ZMod n；y : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
· 使用引理 `ZMod.valMinAbs_mem_Ioc`：valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.va
lMinAbs * 2 in Set.Ioc (-n : Int) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `Int.eq_zero_of_abs_lt_dvd`：eq_zero_of_abs_lt_dvd {m x : Int} (h1 : m ∣ x
) (h2 : |x| < m) : x = 0
· 使用定理 `ZMod.intCast_zmod_eq_zero_iff_dvd`：intCast_zmod_eq_zero_iff_dvd (a : Int
) (b : Nat) : (a : ZMod b) = 0 ↔ (b : Int) ∣ a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 69 条，此处仅展示前 30 条）
-/
lemma valMinAbs_spec [NeZero n] (x : ZMod n) (y : ℤ) :
    x.valMinAbs = y ↔ x = y ∧ y * 2 ∈ Set.Ioc (-n : ℤ) n where
  mp := by rintro rfl; exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩
  mpr h := by
    rw [← sub_eq_zero]
    apply @Int.eq_zero_of_abs_lt_dvd n
    · rw [← intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
    rw [← mul_lt_mul_iff_left₀ (@zero_lt_two ℤ _ _ _ _ _)]
    nth_rw 1 [← abs_eq_self.2 (@zero_le_two ℤ _ _ _ _)]
    rw [← abs_mul, sub_mul, abs_lt]
    constructor <;> linarith only [x.valMinAbs_mem_Ioc.1, x.valMinAbs_mem_Ioc.2, h.2.1, h.2.2]
/-
**ZMod.natAbs_valMinAbs_le** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs <= n / 2
参数：x : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.le_div_two_iff_mul_two_le`：le_div_two_iff_mul_two_le {n m : Nat} : m
 <= n / 2 ↔ (m : Int) * 2 <= n
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ZMod.valMinAbs_mem_Ioc`：valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.va
lMinAbs * 2 in Set.Ioc (-n : Int) n
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs ≤ n / 2 := by
  rw [Nat.le_div_two_iff_mul_two_le]
  rcases x.valMinAbs.natAbs_eq with h | h
  · rw [← h]
    exact x.valMinAbs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.valMinAbs_mem_Ioc.1.le

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.eq_neg_of_valMinAbs_eq_neg_valMinAbs** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：eq_neg_of_valMinAbs_eq_neg_valMinAbs (h : a.valMinAbs = -b.valMinAbs) : a 
= -b
参数：h : a.valMinAbs = -b.valMinAbs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem eq_neg_of_valMinAbs_eq_neg_valMinAbs (h : a.valMinAbs = -b.valMinAbs) : a = -b := by
  rcases eq_zero_or_neZero n with rfl | hn <;> simp_all [valMinAbs_spec]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.valMinAbs_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ), ZMod.valMinAbs 0 = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
-/
lemma valMinAbs_zero : ∀ n, (0 : ZMod n).valMinAbs = 0
  | 0 => by simp only [valMinAbs_def_zero]
  | n + 1 => by simp only [valMinAbs_def_pos, if_true, Int.ofNat_zero, zero_le, val_zero]

@[simp]
/-
**ZMod.valMinAbs_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_eq_zero (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0
参数：x : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用引理 `ZMod.injective_valMinAbs`：injective_valMinAbs : (valMinAbs : ZMod n -> I
nt).Injective
· 使用定理 `ZMod.valMinAbs_zero`：∀ (n : ℕ), ZMod.valMinAbs 0 = 0
-/
lemma valMinAbs_eq_zero (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0 :=
  injective_valMinAbs.eq_iff' <| valMinAbs_zero _
/-
**ZMod.natCast_natAbs_valMinAbs** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：natCast_natAbs_valMinAbs [NeZero n] (a : ZMod n) : (a.valMinAbs.natAbs : Z
Mod n) = if a.val <= (n : Nat) / 2 then a else -a
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `ZMod.val_le`：val_le {n : Nat} [NeZero n] (a : ZMod n) : a.val <= n
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.ofNat_natAbs_of_nonpos`：∀ {a : ℤ}, a ≤ 0 → ↑a.natAbs = -a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma natCast_natAbs_valMinAbs [NeZero n] (a : ZMod n) :
    (a.valMinAbs.natAbs : ZMod n) = if a.val ≤ (n : ℕ) / 2 then a else -a := by
  have : (a.val : ℤ) - n ≤ 0 := by
    rw [sub_nonpos, Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  split_ifs
  · rw [Int.natAbs_natCast, natCast_zmod_val]
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_natCast, Int.cast_natCast, natCast_self, sub_zero, natCast_zmod_val]
/-
**ZMod.valMinAbs_neg_of_ne_half** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_neg_of_ne_half (ha : 2 * a.val != n) : (-a).valMinAbs = -a.valMi
nAbs
参数：ha : 2 * a.val != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ZMod.valMinAbs_spec`：valMinAbs_spec [NeZero n] (x : ZMod n) (y : Int) : 
x.valMinAbs = y ↔ x = y ∧ y * 2 in Set.Ioc (-n : Int) n where mp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ZMod.valMinAbs_mem_Ioc`：valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.va
lMinAbs * 2 in Set.Ioc (-n : Int) n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ZMod.valMinAbs_mul_two_eq_iff`：valMinAbs_mul_two_eq_iff (a : ZMod n) : a
.valMinAbs * 2 = n ↔ 2 * a.val = n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 73 条，此处仅展示前 30 条）
-/
lemma valMinAbs_neg_of_ne_half (ha : 2 * a.val ≠ n) : (-a).valMinAbs = -a.valMinAbs := by
  rcases eq_zero_or_neZero n with rfl | h
  · rfl
  refine (valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_neg, coe_valMinAbs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
  · linarith only [a.valMinAbs_mem_Ioc.1]

@[simp]
/-
**ZMod.natAbs_valMinAbs_neg** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：natAbs_valMinAbs_neg (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.na
tAbs
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.neg_eq_self_iff`：neg_eq_self_iff {n : Nat} (a : ZMod n) : -a = a ↔ 
a = 0 ∨ 2 * a.val = n
· 使用引理 `ZMod.valMinAbs_neg_of_ne_half`：valMinAbs_neg_of_ne_half (ha : 2 * a.val 
!= n) : (-a).valMinAbs = -a.valMinAbs
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
-/
lemma natAbs_valMinAbs_neg (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.natAbs := by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]
/-
**ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natAbs_valMinAbs_eq_natAbs_valMinAbs : a.valMinAbs.natAbs = b.valMinAbs.na
tAbs ↔ a = b ∨ a = -b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_eq_natAbs_iff`：∀ {a b : ℤ}, a.natAbs = b.natAbs ↔ a = b ∨ a =
 -b
· 使用定理 `ZMod.valMinAbs_inj`：valMinAbs_inj : a.valMinAbs = b.valMinAbs ↔ a = b
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `ZMod.eq_neg_of_valMinAbs_eq_neg_valMinAbs`：eq_neg_of_valMinAbs_eq_neg_va
lMinAbs (h : a.valMinAbs = -b.valMinAbs) : a = -b
· 使用引理 `ZMod.natAbs_valMinAbs_neg`：natAbs_valMinAbs_neg (a : ZMod n) : (-a).valM
inAbs.natAbs = a.valMinAbs.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem natAbs_valMinAbs_eq_natAbs_valMinAbs :
    a.valMinAbs.natAbs = b.valMinAbs.natAbs ↔ a = b ∨ a = -b := by
  constructor
  · rw [Int.natAbs_eq_natAbs_iff, valMinAbs_inj]
    exact Or.imp_right eq_neg_of_valMinAbs_eq_neg_valMinAbs
  · rintro (rfl | rfl)
    · rfl
    · rw [natAbs_valMinAbs_neg]
/-
**ZMod.abs_valMinAbs_eq_abs_valMinAbs** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：abs_valMinAbs_eq_abs_valMinAbs : |a.valMinAbs| = |b.valMinAbs| ↔ a = b ∨ a
 = -b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs`：natAbs_valMinAbs_eq_natAbs_va
lMinAbs : a.valMinAbs.natAbs = b.valMinAbs.natAbs ↔ a = b ∨ a = -b
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abs_valMinAbs_eq_abs_valMinAbs :
    |a.valMinAbs| = |b.valMinAbs| ↔ a = b ∨ a = -b := by
  rw [← natAbs_valMinAbs_eq_natAbs_valMinAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  norm_cast
/-
**ZMod.val_eq_ite_valMinAbs** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：val_eq_ite_valMinAbs [NeZero n] (a : ZMod n) : (a.val : Int) = a.valMinAbs
 + if a.val <= n / 2 then 0 else n
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma val_eq_ite_valMinAbs [NeZero n] (a : ZMod n) :
    (a.val : ℤ) = a.valMinAbs + if a.val ≤ n / 2 then 0 else n := by
  rw [valMinAbs_def_pos]
  split_ifs <;> simp [add_zero, sub_add_cancel]
/-
**ZMod.prime_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：prime_ne_zero (p q : Nat) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p
 != q) : (q : ZMod p) != 0
参数：p q : Nat；hpq : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
-/
lemma prime_ne_zero (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rwa [← Nat.cast_zero, Ne, natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd,
    ← hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]

variable {n a : ℕ}
/-
**ZMod.valMinAbs_natAbs_eq_min** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_natAbs_eq_min [hpos : NeZero n] (a : ZMod n) : a.valMinAbs.natAb
s = min a.val (n - a.val)
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma valMinAbs_natAbs_eq_min [hpos : NeZero n] (a : ZMod n) :
    a.valMinAbs.natAbs = min a.val (n - a.val) := by
  rw [valMinAbs_def_pos]
  have := a.val_lt
  omega

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.valMinAbs_natCast_of_le_half** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_natCast_of_le_half (ha : a <= n / 2) : (a : ZMod n).valMinAbs = 
a
参数：ha : a <= n / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Nat.div_lt_self'`：div_lt_self' (a b : Nat) : (a + 1) / (b + 2) < a + 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma valMinAbs_natCast_of_le_half (ha : a ≤ n / 2) : (a : ZMod n).valMinAbs = a := by
  cases n
  · simp
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]
/-
**ZMod.valMinAbs_natCast_of_half_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_natCast_of_half_lt (ha : n / 2 < a) (ha' : a < n) : (a : ZMod n)
.valMinAbs = a - n
参数：ha : n / 2 < a；ha' : a < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.valMinAbs_def_pos`：∀ {n : ℕ} [NeZero n] (x : ZMod n), x.valMinAbs =
 if x.val ≤ n / 2 then ↑x.val else ↑x.val - ↑n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma valMinAbs_natCast_of_half_lt (ha : n / 2 < a) (ha' : a < n) :
    (a : ZMod n).valMinAbs = a - n := by
  cases n
  · cases not_lt_bot ha'
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt ha', ha.not_ge]

@[simp]
/-
**ZMod.valMinAbs_natCast_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：valMinAbs_natCast_eq_self [NeZero n] : (a : ZMod n).valMinAbs = a ↔ a <= n
 / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用引理 `ZMod.natAbs_valMinAbs_le`：natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : 
x.valMinAbs.natAbs <= n / 2
· 使用引理 `ZMod.valMinAbs_natCast_of_le_half`：valMinAbs_natCast_of_le_half (ha : a 
<= n / 2) : (a : ZMod n).valMinAbs = a
-/
lemma valMinAbs_natCast_eq_self [NeZero n] : (a : ZMod n).valMinAbs = a ↔ a ≤ n / 2 := by
  refine ⟨fun ha => ?_, valMinAbs_natCast_of_le_half⟩
  rw [← Int.natAbs_natCast a, ← ha]
  exact natAbs_valMinAbs_le (n := n) a
/-
**ZMod.natAbs_valMinAbs_add_le** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：natAbs_valMinAbs_add_le (a b : ZMod n) : (a + b).valMinAbs.natAbs <= (a.va
lMinAbs + b.valMinAbs).natAbs
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ZMod.natAbs_min_of_le_div_two`：natAbs_min_of_le_div_two (n : Nat) (x y :
 Int) (he : (x : ZMod n) = y) (hl : x.natAbs <= n / 2) : x.natAbs <= y.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ZMod.natAbs_valMinAbs_le`：natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : 
x.valMinAbs.natAbs <= n / 2
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma natAbs_valMinAbs_add_le (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ (a.valMinAbs + b.valMinAbs).natAbs := by
  rcases n with - | n
  · rfl
  apply natAbs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_valMinAbs]
  · apply natAbs_valMinAbs_le

end ZMod

