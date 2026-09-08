/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Num.Lemmas

/-!
# Properties of the `ZNum` representation of integers

This file was split from `Mathlib/Data/Num/Lemmas.lean` to keep the former under 1500 lines.
-/

public section

open Int

attribute [local simp] add_assoc

namespace ZNum

variable {α : Type*}

open PosNum

@[simp, norm_cast]
/-
**ZNum.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum) : α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum) : α) = 0 :=
  rfl

@[simp]
/-
**ZNum.cast_zero'** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_zero' [Zero α] [One α] [Add α] [Neg α] : (ZNum.zero : α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_zero' [Zero α] [One α] [Add α] [Neg α] : (ZNum.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
/-
**ZNum.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : ZNum) : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : ZNum) : α) = 1 :=
  rfl

@[simp]
/-
**ZNum.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (pos n : α) = n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (pos n : α) = n :=
  rfl

@[simp]
/-
**ZNum.cast_neg** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n :=
  rfl

@[simp, norm_cast]
/-
**ZNum.cast_zneg** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ {α : Type u_1} [inst : SubtractionMonoid α] [inst_1 : One α] (n : ZNum),
 ↑(-n) = -↑n
参数：n : ZNum；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem cast_zneg [SubtractionMonoid α] [One α] : ∀ n, ((-n : ZNum) : α) = -n
  | 0 => neg_zero.symm
  | pos _p => rfl
  | neg _p => (neg_neg _).symm
/-
**ZNum.neg_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：neg_zero : (-0 : ZNum) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_zero : (-0 : ZNum) = 0 :=
  rfl
/-
**ZNum.zneg_pos** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_pos (n : PosNum) : -pos n = neg n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zneg_pos (n : PosNum) : -pos n = neg n :=
  rfl
/-
**ZNum.zneg_neg** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_neg (n : PosNum) : -neg n = pos n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zneg_neg (n : PosNum) : -neg n = pos n :=
  rfl
/-
**ZNum.zneg_zneg** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_zneg (n : ZNum) : - -n = n
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zneg_zneg (n : ZNum) : - -n = n := by cases n <;> rfl
/-
**ZNum.zneg_bit1** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_bit1 (n : ZNum) : -n.bit1 = (-n).bitm1
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zneg_bit1 (n : ZNum) : -n.bit1 = (-n).bitm1 := by cases n <;> rfl
/-
**ZNum.zneg_bitm1** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_bitm1 (n : ZNum) : -n.bitm1 = (-n).bit1
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zneg_bitm1 (n : ZNum) : -n.bitm1 = (-n).bit1 := by cases n <;> rfl
/-
**ZNum.zneg_succ** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_succ (n : ZNum) : -n.succ = (-n).pred
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZNum.succ.eq_3`：∀ (a : PosNum), (ZNum.neg a).succ = a.pred'.toZNumNeg
· 使用定理 `Num.zneg_toZNumNeg`：zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum
-/
theorem zneg_succ (n : ZNum) : -n.succ = (-n).pred := by
  cases n <;> try { rfl }; rw [succ, Num.zneg_toZNumNeg]; rfl
/-
**ZNum.zneg_pred** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zneg_pred (n : ZNum) : -n.pred = (-n).succ
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.zneg_zneg`：zneg_zneg (n : ZNum) : - -n = n
· 使用定理 `ZNum.zneg_succ`：zneg_succ (n : ZNum) : -n.succ = (-n).pred
-/
theorem zneg_pred (n : ZNum) : -n.pred = (-n).succ := by
  rw [← zneg_zneg (succ (-n)), zneg_succ, zneg_zneg]

@[simp]
/-
**ZNum.abs_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ZNum), ↑n.abs = (↑n).natAbs
参数：n : ZNum；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
-/
theorem abs_to_nat : ∀ n, (abs n : ℕ) = Int.natAbs n
  | 0 => rfl
  | pos p => congr_arg Int.natAbs p.to_nat_to_int
  | neg p => show Int.natAbs ((p : ℕ) : ℤ) = Int.natAbs (-p) by rw [p.to_nat_to_int, Int.natAbs_neg]

@[simp]
/-
**ZNum.abs_toZNum** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : Num), n.toZNum.abs = n
参数：n : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_toZNum : ∀ n : Num, abs n.toZNum = n
  | 0 => rfl
  | Num.pos _p => rfl

@[simp, norm_cast]
/-
**ZNum.cast_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum), ↑↑n = ↑n
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZNum.cast_zero`：cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum)
 : α) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `ZNum.cast_pos`：cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(pos n : α) = n
· 使用定理 `PosNum.cast_to_int`：cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n :
 Int) : α) = n
· 使用定理 `ZNum.cast_neg`：cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(neg n : α) = -n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
theorem cast_to_int [AddGroupWithOne α] : ∀ n : ZNum, ((n : ℤ) : α) = n
  | 0 => by rw [cast_zero, cast_zero, Int.cast_zero]
  | pos p => by rw [cast_pos, cast_pos, PosNum.cast_to_int]
  | neg p => by rw [cast_neg, cast_neg, Int.cast_neg, PosNum.cast_to_int]
/-
**ZNum.bit0_of_bit0** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ZNum), n + n = n.bit0
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.bit0_of_bit0`：∀ (n : PosNum), n + n = n.bit0
-/
theorem bit0_of_bit0 : ∀ n : ZNum, n + n = n.bit0
  | 0 => rfl
  | pos a => congr_arg pos a.bit0_of_bit0
  | neg a => congr_arg neg a.bit0_of_bit0
/-
**ZNum.bit1_of_bit1** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ZNum), n + n + 1 = n.bit1
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.bit1_of_bit1`：bit1_of_bit1 (n : PosNum) : (n + n) + 1 = bit1 n
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.one_sub'`：one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZNumNeg
· 使用定理 `PosNum.bit0_of_bit0`：∀ (n : PosNum), n + n = n.bit0
-/
theorem bit1_of_bit1 : ∀ n : ZNum, n + n + 1 = n.bit1
  | 0 => rfl
  | pos a => congr_arg pos a.bit1_of_bit1
  | neg a => show PosNum.sub' 1 (a + a) = _ by rw [PosNum.one_sub', a.bit0_of_bit0]; rfl

@[simp, norm_cast]
/-
**ZNum.cast_bit0** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum), ↑n.bit0 = ↑n + ↑n
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZNum.bit0.eq_2`：∀ (a : PosNum), (ZNum.pos a).bit0 = ZNum.pos a.bit0
· 使用定理 `ZNum.cast_pos`：cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(pos n : α) = n
· 使用定理 `ZNum.bit0.eq_3`：∀ (a : PosNum), (ZNum.neg a).bit0 = ZNum.neg a.bit0
· 使用定理 `ZNum.cast_neg`：cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(neg n : α) = -n
· 使用定理 `PosNum.cast_bit0`：cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) 
= (n : α) + n
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
-/
theorem cast_bit0 [AddGroupWithOne α] : ∀ n : ZNum, (n.bit0 : α) = (n : α) + n
  | 0 => (add_zero _).symm
  | pos p => by rw [ZNum.bit0, cast_pos, cast_pos]; rfl
  | neg p => by
    rw [ZNum.bit0, cast_neg, cast_neg, PosNum.cast_bit0, neg_add_rev]

@[simp, norm_cast]
/-
**ZNum.cast_bit1** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_bit1 [AddGroupWithOne α] : forall n : ZNum, (n.bit1 : α) = ((n : α) +
 n) + 1 | 0 => by simp [ZNum.bit1] | pos p => by rw [ZNum.bit1, cast_pos, cast_p
os]; rfl | neg p => by rw [ZNum.bit1]; rw [cast_neg]; rw [cast_neg] rcases e : p
red' p with - | a <;> have ep : p = _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ZNum.bit1.eq_2`：∀ (a : PosNum), (ZNum.pos a).bit1 = ZNum.pos a.bit1
· 使用定理 `ZNum.cast_pos`：cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(pos n : α) = n
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `ZNum.bit1.eq_3`：∀ (a : PosNum), (ZNum.neg a).bit1 = ZNum.neg (Num.casesO
n a.pred' 1 PosNum.bit1)
· 使用定理 `ZNum.cast_neg`：cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(neg n : α) = -n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.succ'_pred'`：∀ (n : PosNum), n.pred'.succ' = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `PosNum.cast_to_int`：cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n :
 Int) : α) = n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `PosNum.cast_succ`：cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n 
: α) = n + 1
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem cast_bit1 [AddGroupWithOne α] : ∀ n : ZNum, (n.bit1 : α) = ((n : α) + n) + 1
  | 0 => by simp [ZNum.bit1]
  | pos p => by rw [ZNum.bit1, cast_pos, cast_pos]; rfl
  | neg p => by
    rw [ZNum.bit1, cast_neg, cast_neg]
    rcases e : pred' p with - | a <;>
      have ep : p = _ := (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
    · conv at ep => change p = 1
      subst p
      simp
    · dsimp only [Num.succ'] at ep
      subst p
      have : (↑(-↑a : ℤ) : α) = -1 + ↑(-↑a + 1 : ℤ) := by simp [add_comm (-↑a : ℤ) 1]
      simpa using this

@[simp]
/-
**ZNum.cast_bitm1** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_bitm1 [AddGroupWithOne α] (n : ZNum) : (n.bitm1 : α) = (n : α) + n - 
1
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.zneg_zneg`：zneg_zneg (n : ZNum) : - -n = n
· 使用定理 `ZNum.zneg_bit1`：zneg_bit1 (n : ZNum) : -n.bit1 = (-n).bitm1
· 使用定理 `ZNum.cast_zneg`：∀ {α : Type u_1} [inst : SubtractionMonoid α] [inst_1 : 
One α] (n : ZNum), ↑(-n) = -↑n
· 使用定理 `ZNum.cast_bit1`：cast_bit1 [AddGroupWithOne α] : forall n : ZNum, (n.bit1
 : α) = ((n : α) + n) + 1 | 0 => by simp [ZNum.bit1] | pos p => by rw [ZNum.bit1
, ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `ZNum.cast_to_int`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum)
, ↑↑n = ↑n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem cast_bitm1 [AddGroupWithOne α] (n : ZNum) : (n.bitm1 : α) = (n : α) + n - 1 := by
  conv =>
    lhs
    rw [← zneg_zneg n]
  rw [← zneg_bit1, cast_zneg, cast_bit1]
  have : ((-1 + n + n : ℤ) : α) = (n + n + -1 : ℤ) := by simp [add_comm]
  simpa [sub_eq_add_neg] using this
/-
**ZNum.add_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：add_zero (n : ZNum) : n + 0 = n
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_zero (n : ZNum) : n + 0 = n := by cases n <;> rfl
/-
**ZNum.zero_add** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：zero_add (n : ZNum) : 0 + n = n
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zero_add (n : ZNum) : 0 + n = n := by cases n <;> rfl
/-
**ZNum.add_one** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ZNum), n + 1 = n.succ
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.add_one`：add_one (n : PosNum) : n + 1 = succ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_one : ∀ n : ZNum, n + 1 = succ n
  | 0 => rfl
  | pos p => congr_arg pos p.add_one
  | neg p => by cases p <;> rfl

end ZNum

namespace PosNum

variable {α : Type*}

/-
**PosNum.cast_to_znum** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_to_znum : forall n : PosNum, (n : ZNum) = ZNum.pos n | 1 => rfl | bit
0 p => by have
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_to_znum : ∀ n : PosNum, (n : ZNum) = ZNum.pos n
  | 1 => rfl
  | bit0 p => by
      have := congr_arg ZNum.bit0 (cast_to_znum p)
      rwa [← ZNum.bit0_of_bit0] at this
  | bit1 p => by
      have := congr_arg ZNum.bit1 (cast_to_znum p)
      rwa [← ZNum.bit1_of_bit1] at this
/-
**PosNum.cast_sub'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_sub' [AddGroupWithOne α] : forall m n : PosNum, (sub' m n : α) = m - 
n | a, 1 => by rw [sub'_one]; rw [Num.cast_toZNum]; rw [← Num.cast_to_nat]; rw [
pred'_to_nat]; rw [← Nat.sub_one] simp | 1, b => by rw [one_sub']; rw [Num.cast_
toZNumNeg]; rw [← neg_sub]; rw [neg_inj]; rw [← Num.cast_to_nat]; rw [pred'_to_n
at]; rw [← Nat.sub_one] simp | bit0 a, bit0 b => by rw [sub']; rw [ZNum.cast_bit
0]; rw [cast_sub' a b] have : ((a + -b + (a + -b) : Int) : α) = a + a + (-b + -b
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum
-/
theorem cast_sub' [AddGroupWithOne α] : ∀ m n : PosNum, (sub' m n : α) = m - n
  | a, 1 => by
    rw [sub'_one, Num.cast_toZNum, ← Num.cast_to_nat, pred'_to_nat, ← Nat.sub_one]
    simp
  | 1, b => by
    rw [one_sub', Num.cast_toZNumNeg, ← neg_sub, neg_inj, ← Num.cast_to_nat, pred'_to_nat,
        ← Nat.sub_one]
    simp
  | bit0 a, bit0 b => by
    rw [sub', ZNum.cast_bit0, cast_sub' a b]
    have : ((a + -b + (a + -b) : ℤ) : α) = a + a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit0 a, bit1 b => by
    rw [sub', ZNum.cast_bitm1, cast_sub' a b]
    have : ((-b + (a + (-b + -1)) : ℤ) : α) = (a + -1 + (-b + -b) : ℤ) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit0 b => by
    rw [sub', ZNum.cast_bit1, cast_sub' a b]
    have : ((-b + (a + (-b + 1)) : ℤ) : α) = (a + 1 + (-b + -b) : ℤ) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit1 b => by
    rw [sub', ZNum.cast_bit0, cast_sub' a b]
    have : ((-b + (a + -b) : ℤ) : α) = a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this
/-
**PosNum.to_nat_eq_succ_pred** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：to_nat_eq_succ_pred (n : PosNum) : (n : Nat) = n.pred' + 1
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `PosNum.succ'_pred'`：∀ (n : PosNum), n.pred'.succ' = n
-/
theorem to_nat_eq_succ_pred (n : PosNum) : (n : ℕ) = n.pred' + 1 := by
  rw [← Num.succ'_to_nat, n.succ'_pred']
/-
**PosNum.to_int_eq_succ_pred** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：to_int_eq_succ_pred (n : PosNum) : (n : Int) = (n.pred' : Nat) + 1
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `PosNum.to_nat_eq_succ_pred`：to_nat_eq_succ_pred (n : PosNum) : (n : Nat)
 = n.pred' + 1
-/
theorem to_int_eq_succ_pred (n : PosNum) : (n : ℤ) = (n.pred' : ℕ) + 1 := by
  rw [← n.to_nat_to_int, to_nat_eq_succ_pred]; rfl

end PosNum

namespace Num

variable {α : Type*}

@[simp]
/-
**Num.cast_sub'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {α : Type u_1} [inst : AddGroupWithOne α] (m n : Num), ↑(m.sub' n) = ↑m 
- ↑n
参数：m n : Num；m.sub' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `PosNum.cast_sub'`：cast_sub' [AddGroupWithOne α] : forall m n : PosNum, (
sub' m n : α) = m - n | a, 1 => by rw [sub'_one]; rw [Num.cast_toZNum]; rw [← Nu
m.cast…
-/
theorem cast_sub' [AddGroupWithOne α] : ∀ m n : Num, (sub' m n : α) = m - n
  | 0, 0 => (sub_zero _).symm
  | pos _a, 0 => (sub_zero _).symm
  | 0, pos _b => (zero_sub _).symm
  | pos _a, pos _b => PosNum.cast_sub' _ _
/-
**Num.toZNum_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n.succ.toZNum = n.toZNum.succ
参数：n : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toZNum_succ : ∀ n : Num, n.succ.toZNum = n.toZNum.succ
  | 0 => rfl
  | pos _n => rfl
/-
**Num.toZNumNeg_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n.succ.toZNumNeg = n.toZNumNeg.pred
参数：n : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toZNumNeg_succ : ∀ n : Num, n.succ.toZNumNeg = n.toZNumNeg.pred
  | 0 => rfl
  | pos _n => rfl

@[simp]
/-
**Num.pred_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ZNum), n.pred.succ = n
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.pred'_succ'`：∀ (n : Num), n.succ'.pred' = n
· 使用定理 `ZNum.pred.eq_2`：∀ (a : PosNum), (ZNum.pos a).pred = a.pred'.toZNum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.toZNum_succ`：∀ (n : Num), n.succ.toZNum = n.toZNum.succ
· 使用定理 `Num.succ.eq_1`：∀ (n : Num), n.succ = Num.pos n.succ'
· 使用定理 `PosNum.succ'_pred'`：∀ (n : PosNum), n.pred'.succ' = n
· 使用定理 `Num.toZNum.eq_2`：∀ (p : PosNum), (Num.pos p).toZNum = ZNum.pos p
-/
theorem pred_succ : ∀ n : ZNum, n.pred.succ = n
  | 0 => rfl
  | ZNum.neg p => show toZNumNeg (pos p).succ'.pred' = _ by rw [PosNum.pred'_succ']; rfl
  | ZNum.pos p => by rw [ZNum.pred, ← toZNum_succ, Num.succ, PosNum.succ'_pred', toZNum]
/-
**Num.succ_ofInt'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ℤ), ZNum.ofInt' (n + 1) = ZNum.ofInt' n + 1
参数：n : ℤ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.ofNat'_succ`：∀ {n : ℕ}, Num.ofNat' (n + 1) = Num.ofNat' n + 1
· 使用定理 `Num.add_one`：∀ (n : Num), n + 1 = n.succ
· 使用定理 `Num.toZNum_succ`：∀ (n : Num), n.succ.toZNum = n.toZNum.succ
· 使用定理 `ZNum.add_one`：∀ (n : ZNum), n + 1 = n.succ
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `Num.toZNumNeg_succ`：∀ (n : Num), n.succ.toZNumNeg = n.toZNumNeg.pred
· 使用定理 `Num.pred_succ`：∀ (n : ZNum), n.pred.succ = n
-/
theorem succ_ofInt' : ∀ n, ZNum.ofInt' (n + 1) = ZNum.ofInt' n + 1
  | (n : ℕ) => by
    change ZNum.ofInt' (n + 1 : ℕ) = ZNum.ofInt' (n : ℕ) + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [Num.ofNat'_succ, Num.add_one, toZNum_succ, ZNum.add_one]
  | -[0+1] => by
    change ZNum.ofInt' 0 = ZNum.ofInt' (-[0+1]) + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [ofNat'_succ, ofNat'_zero]; rfl
  | -[(n + 1)+1] => by
    change ZNum.ofInt' -[n+1] = ZNum.ofInt' -[(n + 1)+1] + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [@Num.ofNat'_succ (n + 1), Num.add_one, toZNumNeg_succ,
      @ofNat'_succ n, Num.add_one, ZNum.add_one, pred_succ]
/-
**Num.ofInt'_toZNum** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ℕ), (↑n).toZNum = ZNum.ofInt' ↑n
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofInt'_toZNum : ∀ n : ℕ, toZNum n = ZNum.ofInt' n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.cast_succ, Num.add_one, toZNum_succ, ofInt'_toZNum n, Nat.cast_succ, succ_ofInt',
      ZNum.add_one]
/-
**Num.mem_ofZNum'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {m : Num} {n : ZNum}, m ∈ Num.ofZNum' n ↔ n = m.toZNum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_ofZNum' : ∀ {m : Num} {n : ZNum}, m ∈ ofZNum' n ↔ n = toZNum m
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | pos _, 0 => ⟨nofun, nofun⟩
  | m, ZNum.pos p =>
    Option.some_inj.trans <| by cases m <;> constructor <;> intro h <;> try cases h <;> rfl
  | m, ZNum.neg p => ⟨nofun, fun h => by cases m <;> cases h⟩
/-
**Num.ofZNum'_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ZNum), castNum <$> Num.ofZNum' n = (↑n).toNat?
参数：n : ZNum；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosNum.succ'_pred'`：∀ (n : PosNum), n.pred'.succ' = n
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofZNum'_toNat : ∀ n : ZNum, (↑) <$> ofZNum' n = Int.toNat? n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat? p by rw [← PosNum.to_nat_to_int p]; rfl
  | ZNum.neg p =>
    (congr_arg fun x => Int.toNat? (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by rw [← succ'_to_nat]; simp
/-
**Num.ofZNum_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ZNum), ↑(Num.ofZNum n) = (↑n).toNat
参数：n : ZNum；Num.ofZNum n；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosNum.succ'_pred'`：∀ (n : PosNum), n.pred'.succ' = n
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofZNum_toNat : ∀ n : ZNum, (ofZNum n : ℕ) = Int.toNat n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat p by rw [← PosNum.to_nat_to_int p]; rfl
  | ZNum.neg p =>
    (congr_arg fun x => Int.toNat (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by rw [← succ'_to_nat]; simp

@[simp]
/-
**Num.cast_ofZNum** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_ofZNum [AddMonoidWithOne α] (n : ZNum) : (ofZNum n : α) = Int.toNat n
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
· 使用定理 `Num.ofZNum_toNat`：∀ (n : ZNum), ↑(Num.ofZNum n) = (↑n).toNat
-/
theorem cast_ofZNum [AddMonoidWithOne α] (n : ZNum) : (ofZNum n : α) = Int.toNat n := by
  rw [← cast_to_nat, ofZNum_toNat]

@[simp, norm_cast]
/-
**Num.sub_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：sub_to_nat (m n) : ((m - n : Num) : Nat) = m - n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.ofZNum_toNat`：∀ (n : ZNum), ↑(Num.ofZNum n) = (↑n).toNat
· 使用定理 `Num.cast_sub'`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (m n : Num), 
↑(m.sub' n) = ↑m - ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.to_nat_to_int`：to_nat_to_int (n : Num) : ((n : Nat) : Int) = n
· 使用定理 `Int.toNat_sub`：∀ (m n : ℕ), (↑m - ↑n).toNat = m - n
-/
theorem sub_to_nat (m n) : ((m - n : Num) : ℕ) = m - n :=
  show (ofZNum _ : ℕ) = _ by
    rw [ofZNum_toNat, cast_sub', ← to_nat_to_int, ← to_nat_to_int, Int.toNat_sub]

end Num

namespace ZNum

variable {α : Type*}

@[simp, norm_cast]
/-
**ZNum.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_add [AddGroupWithOne α] : forall m n, ((m + n : ZNum) : α) = m + n | 
0, a => by cases a <;> exact (_root_.zero_add _).symm | b, 0 => by cases b <;> e
xact (_root_.add_zero _).symm | pos _, pos _ => PosNum.cast_add _ _ | pos a, neg
 b => by simpa only [sub_eq_add_neg] using! PosNum.cast_sub' (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `PosNum.cast_add`：cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum)
 : α) = m + n
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `PosNum.cast_sub'`：cast_sub' [AddGroupWithOne α] : forall m n : PosNum, (
sub' m n : α) = m - n | a, 1 => by rw [sub'_one]; rw [Num.cast_toZNum]; rw [← Nu
m.cast…
· 使用定理 `PosNum.cast_to_int`：cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n :
 Int) : α) = n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem cast_add [AddGroupWithOne α] : ∀ m n, ((m + n : ZNum) : α) = m + n
  | 0, a => by cases a <;> exact (_root_.zero_add _).symm
  | b, 0 => by cases b <;> exact (_root_.add_zero _).symm
  | pos _, pos _ => PosNum.cast_add _ _
  | pos a, neg b => by simpa only [sub_eq_add_neg] using! PosNum.cast_sub' (α := α) _ _
  | neg a, pos b =>
    have : (↑b + -↑a : α) = -↑a + ↑b := by
      rw [← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_neg, ← Int.cast_add (-a)]
      simp [add_comm]
    (PosNum.cast_sub' _ _).trans <| (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add, neg_eq_iff_eq_neg, neg_add_rev, neg_neg, neg_neg,
          ← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_add, ← Int.cast_add, add_comm]

@[simp]
/-
**ZNum.cast_succ** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_succ [AddGroupWithOne α] (n) : ((succ n : ZNum) : α) = n + 1
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.add_one`：∀ (n : ZNum), n + 1 = n.succ
· 使用定理 `ZNum.cast_add`：cast_add [AddGroupWithOne α] : forall m n, ((m + n : ZNum
) : α) = m + n | 0, a => by cases a <;> exact (_root_.zero_add _).symm | b, 0 =>
 by…
· 使用定理 `ZNum.cast_one`：cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : ZNum) :
 α) = 1
-/
theorem cast_succ [AddGroupWithOne α] (n) : ((succ n : ZNum) : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]

@[simp, norm_cast]
/-
**ZNum.mul_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (m n : ZNum), ↑(m * n) = ↑m * ↑n
参数：m n : ZNum；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PosNum.cast_mul`：cast_mul [NonAssocSemiring α] (m n) : ((m * n : PosNum)
 : α) = m * n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
-/
theorem mul_to_int : ∀ m n, ((m * n : ZNum) : ℤ) = m * n
  | 0, a => by cases a <;> exact (zero_mul _).symm
  | b, 0 => by cases b <;> exact (mul_zero _).symm
  | pos a, pos b => PosNum.cast_mul a b
  | pos a, neg b => show -↑(a * b) = ↑a * -↑b by rw [PosNum.cast_mul, neg_mul_eq_mul_neg]
  | neg a, pos b => show -↑(a * b) = -↑a * ↑b by rw [PosNum.cast_mul, neg_mul_eq_neg_mul]
  | neg a, neg b => show ↑(a * b) = -↑a * -↑b by rw [PosNum.cast_mul, neg_mul_neg]
/-
**ZNum.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_mul [NonAssocRing α] (m n) : ((m * n : ZNum) : α) = m * n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.cast_to_int`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum)
, ↑↑n = ↑n
· 使用定理 `ZNum.mul_to_int`：∀ (m n : ZNum), ↑(m * n) = ↑m * ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
-/
theorem cast_mul [NonAssocRing α] (m n) : ((m * n : ZNum) : α) = m * n := by
  rw [← cast_to_int, mul_to_int, Int.cast_mul, cast_to_int, cast_to_int]
/-
**ZNum.ofInt'_neg** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ℤ), ZNum.ofInt' (-n) = -ZNum.ofInt' n
参数：n : ℤ；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.zneg_toZNumNeg`：zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `Num.zneg_toZNum`：zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg
-/
theorem ofInt'_neg : ∀ n : ℤ, ofInt' (-n) = -ofInt' n
  | -[n+1] => show ofInt' (n + 1 : ℕ) = _ by simp only [ofInt', Num.zneg_toZNumNeg]
  | 0 => show Num.toZNum (Num.ofNat' 0) = -Num.toZNum (Num.ofNat' 0) by rw [Num.ofNat'_zero]; rfl
  | (n + 1 : ℕ) => show Num.toZNumNeg _ = -Num.toZNum _ by rw [Num.zneg_toZNum]
/-
**ZNum.of_to_int'** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ZNum), ZNum.ofInt' ↑n = n
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ZNum.cast_pos`：cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(pos n : α) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `Num.ofInt'_toZNum`：∀ (n : ℕ), (↑n).toZNum = ZNum.ofInt' ↑n
· 使用定理 `PosNum.of_to_nat`：of_to_nat : forall n : PosNum, ((n : Nat) : Num) = Num
.pos n
· 使用定理 `ZNum.cast_neg`：cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(neg n : α) = -n
· 使用定理 `ZNum.ofInt'_neg`：∀ (n : ℤ), ZNum.ofInt' (-n) = -ZNum.ofInt' n
-/
theorem of_to_int' : ∀ n : ZNum, ZNum.ofInt' n = n
  | 0 => by
    dsimp [ofInt', cast_zero]
    simp only [Num.ofNat'_zero, Num.toZNum]
  | pos a => by rw [cast_pos, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl
  | neg a => by
    rw [cast_neg, ofInt'_neg, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl
/-
**ZNum.to_int_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：to_int_inj {m n : ZNum} : (m : Int) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `ZNum.of_to_int'`：∀ (n : ZNum), ZNum.ofInt' ↑n = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem to_int_inj {m n : ZNum} : (m : ℤ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩
/-
**ZNum.cmp_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cmp_to_int : forall m n, (Ordering.casesOn (cmp m n) ((m : Int) < n) (m = 
n) ((n : Int) < m) : Prop) | 0, 0 => rfl | pos a, pos b => by simpa using! PosNu
m.cmp_to_nat a b | neg a, neg b => by have
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZNum.pos.injEq`：∀ (a a_1 : PosNum), (ZNum.pos a = ZNum.pos a_1) = (a = a
_1)
· 使用定理 `PosNum.cmp_to_nat`：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) 
((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop) | 1, 1 => rfl | bit0 a, 1 => let
 h : (1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `PosNum.cast_pos`：cast_pos [Semiring α] [PartialOrder α] [IsStrictOrdered
Ring α] (n : PosNum) : 0 < (n : α)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
-/
theorem cmp_to_int : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℤ) < n) (m = n) ((n : ℤ) < m) : Prop)
  | 0, 0 => rfl
  | pos a, pos b => by simpa using! PosNum.cmp_to_nat a b
  | neg a, neg b => by
    have := PosNum.cmp_to_nat b a; revert this; dsimp [cmp]
    cases PosNum.cmp b a <;> [simp; simp +contextual; simp]
  | pos _, 0 => PosNum.cast_pos _
  | pos _, neg _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, neg _ => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg _, 0 => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg _, pos _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, pos _ => PosNum.cast_pos _

@[norm_cast]
/-
**ZNum.lt_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：lt_to_int {m n : ZNum} : (m : Int) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZNum.cmp_to_int`：cmp_to_int : forall m n, (Ordering.casesOn (cmp m n) ((
m : Int) < n) (m = n) ((n : Int) < m) : Prop) | 0, 0 => rfl | pos a, pos b => by
 simp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem lt_to_int {m n : ZNum} : (m : ℤ) < n ↔ m < n :=
  show (m : ℤ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by simp only at h; simp [h]
    | Ordering.eq, h => by simp only at h; simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]
/-
**ZNum.le_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：le_to_int {m n : ZNum} : (m : Int) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZNum.lt_to_int`：lt_to_int {m n : ZNum} : (m : Int) < n ↔ m < n
-/
theorem le_to_int {m n : ZNum} : (m : ℤ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_int

@[simp, norm_cast]
/-
**ZNum.cast_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_lt [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} : (
m : α) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.cast_to_int`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum)
, ↑↑n = ↑n
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `ZNum.lt_to_int`：lt_to_int {m n : ZNum} : (m : Int) < n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_lt, lt_to_int]

@[simp, norm_cast]
/-
**ZNum.cast_le** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_le [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : ZNum} : (m
 : α) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZNum.cast_lt`：cast_lt [Ring α] [PartialOrder α] [IsStrictOrderedRing α] 
{m n : ZNum} : (m : α) < n ↔ m < n
-/
theorem cast_le [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]
/-
**ZNum.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_inj [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} : 
(m : α) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.cast_to_int`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum)
, ↑↑n = ↑n
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `ZNum.to_int_inj`：to_int_inj {m n : ZNum} : (m : Int) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_inj [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) = n ↔ m = n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_inj (α := α), to_int_inj]

/-- This tactic tries to turn an (in)equality about `ZNum`s to one about `Int`s by rewriting.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer_rw
  exact le_add_of_nonneg_right (mul_self_nonneg _)
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_int_inj] | rw [← lt_to_int] | rw [← le_to_int]
     repeat first | rw [cast_add] | rw [mul_to_int] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `ZNum`s by transferring them to the `Int` world and
then trying to call `simp`.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer
  exact mul_self_nonneg _
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

/-
**ZNum.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：linearOrder : LinearOrder ZNum where lt_iff_le_not_ge
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder : LinearOrder ZNum where
  lt_iff_le_not_ge := by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le_refl := by transfer
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    transfer_rw
    apply le_antisymm
  le_total := by
    intro a b
    transfer_rw
    apply le_total
  -- This is relying on an automatically generated instance name, generated in a `deriving` handler.
  -- See https://github.com/leanprover/lean4/issues/2343
  toDecidableEq := instDecidableEqZNum
  toDecidableLE := ZNum.decidableLE
  toDecidableLT := ZNum.decidableLT
/-
**ZNum.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：addMonoid : AddMonoid ZNum where add_assoc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ZNum.zero_add`：zero_add (n : ZNum) : 0 + n = n
· 使用定理 `ZNum.add_zero`：add_zero (n : ZNum) : n + 0 = n
-/
instance addMonoid : AddMonoid ZNum where
  add_assoc := by transfer
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
/-
**ZNum.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：addCommGroup : AddCommGroup ZNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup ZNum :=
  { ZNum.addMonoid with
    add_comm := by transfer
    zsmul := zsmulRec
    neg_add_cancel := by transfer }
/-
**ZNum.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：addMonoidWithOne : AddMonoidWithOne ZNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne : AddMonoidWithOne ZNum :=
  { ZNum.addMonoid with
    natCast := fun n => ZNum.ofInt' n
    natCast_zero := show (Num.ofNat' 0).toZNum = 0 by rw [Num.ofNat'_zero]; rfl
    natCast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZNum = (Num.ofNat' n).toZNum + 1 by
        rw [Num.ofNat'_succ, Num.add_one, Num.toZNum_succ, ZNum.add_one] }

-- The next theorems are declared outside of the instance to prevent timeouts.

set_option backward.privateInPublic true in
/-
**ZNum.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_comm : ∀ (a b : ZNum), a * b = b * a := by transfer

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ZNum.commRing** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：commRing : CommRing ZNum
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.add_comm`：∀ {G : Type u} [self : AddCommGroup G] (a b : G),
 a + b = b + a
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `_private.Mathlib.Data.Num.ZNum.0.ZNum.mul_comm`：∀ (a b : ZNum), a * b = 
b * a
-/
instance commRing : CommRing ZNum :=
  { ZNum.addCommGroup, ZNum.addMonoidWithOne with
    mul_assoc a b c := by transfer
    zero_mul := by transfer
    mul_zero := by transfer
    one_mul := by transfer
    mul_one := by transfer
    left_distrib := by
      transfer
      simp [mul_add]
    right_distrib := by
      transfer
      simp [mul_add, _root_.mul_comm]
    mul_comm := mul_comm }
/-
**ZNum.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：nontrivial : Nontrivial ZNum
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance nontrivial : Nontrivial ZNum :=
  { exists_pair_ne := ⟨0, 1, by decide⟩ }
/-
**ZNum.zeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：zeroLEOneClass : ZeroLEOneClass ZNum
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance zeroLEOneClass : ZeroLEOneClass ZNum :=
  { zero_le_one := by decide }
/-
**ZNum.isOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：isOrderedAddMonoid : IsOrderedAddMonoid ZNum where add_le_add_left a b h c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.le_to_int`：le_to_int {m n : ZNum} : (m : Int) <= n ↔ m <= n
· 使用定理 `ZNum.cast_add`：cast_add [AddGroupWithOne α] : forall m n, ((m + n : ZNum
) : α) = m + n | 0, a => by cases a <;> exact (_root_.zero_add _).symm | b, 0 =>
 by…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance isOrderedAddMonoid : IsOrderedAddMonoid ZNum where
  add_le_add_left a b h c := by revert h; transfer_rw; intro h; gcongr
/-
**ZNum.isStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：isStrictOrderedRing : IsStrictOrderedRing ZNum
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStrictOrderedRing.of_mul_pos`：IsStrictOrderedRing.of_mul_pos [Ring R] 
[PartialOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] [Nontrivial R] (mul_p
os : forall a b : R,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.lt_to_int`：lt_to_int {m n : ZNum} : (m : Int) < n ↔ m < n
· 使用定理 `ZNum.mul_to_int`：∀ (m n : ZNum), ↑(m * n) = ↑m * ↑n
· 使用定理 `ZNum.cast_zero`：cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum)
 : α) = 0
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
instance isStrictOrderedRing : IsStrictOrderedRing ZNum :=
  .of_mul_pos fun a b ↦ by
    transfer_rw
    apply mul_pos

@[simp, norm_cast]
/-
**ZNum.cast_sub** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：cast_sub [AddCommGroupWithOne α] (m n) : ((m - n : ZNum) : α) = m - n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `ZNum.cast_add`：cast_add [AddGroupWithOne α] : forall m n, ((m + n : ZNum
) : α) = m + n | 0, a => by cases a <;> exact (_root_.zero_add _).symm | b, 0 =>
 by…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZNum.cast_zneg`：∀ {α : Type u_1} [inst : SubtractionMonoid α] [inst_1 : 
One α] (n : ZNum), ↑(-n) = -↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_sub [AddCommGroupWithOne α] (m n) : ((m - n : ZNum) : α) = m - n := by
  simp [sub_eq_neg_add]

@[norm_cast]
/-
**ZNum.neg_of_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ℤ), ↑(-n) = -↑n
参数：n : ℤ；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.zneg_zneg`：zneg_zneg (n : ZNum) : - -n = n
-/
theorem neg_of_int : ∀ n, ((-n : ℤ) : ZNum) = -n
  | (_ + 1 : ℕ) => rfl
  | 0 => by rw [Int.cast_neg]
  | -[_+1] => (zneg_zneg _).symm

@[simp]
/-
**ZNum.ofInt'_eq** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ℤ), ZNum.ofInt' n = ↑n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Num.add_one`：∀ (n : Num), n + 1 = n.succ
· 使用定理 `Num.zneg_toZNumNeg`：zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum
· 使用定理 `Num.toZNum_succ`：∀ (n : Num), n.succ.toZNum = n.toZNum.succ
· 使用定理 `ZNum.add_one`：∀ (n : ZNum), n + 1 = n.succ
-/
theorem ofInt'_eq : ∀ n : ℤ, ZNum.ofInt' n = n
  | (n : ℕ) => rfl
  | -[n+1] => by
    change Num.toZNumNeg (n + 1 : ℕ) = -(n + 1 : ℕ)
    rw [← neg_inj, neg_neg, Nat.cast_succ, Num.add_one, Num.zneg_toZNumNeg, Num.toZNum_succ,
      Nat.cast_succ, ZNum.add_one]
    rfl

@[simp]
/-
**ZNum.of_nat_toZNum** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：of_nat_toZNum (n : Nat) : Num.toZNum n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_nat_toZNum (n : ℕ) : Num.toZNum n = n :=
  rfl

-- The priority should be `high`er than `cast_to_int`.
@[simp high, norm_cast]
/-
**ZNum.of_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：of_to_int (n : ZNum) : ((n : Int) : ZNum) = n
参数：n : ZNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.ofInt'_eq`：∀ (n : ℤ), ZNum.ofInt' n = ↑n
· 使用定理 `ZNum.of_to_int'`：∀ (n : ZNum), ZNum.ofInt' ↑n = n
-/
theorem of_to_int (n : ZNum) : ((n : ℤ) : ZNum) = n := by rw [← ofInt'_eq, of_to_int']
/-
**ZNum.to_of_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：to_of_int (n : Int) : ((n : ZNum) : Int) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ZNum.cast_add`：cast_add [AddGroupWithOne α] : forall m n, ((m + n : ZNum
) : α) = m + n | 0, a => by cases a <;> exact (_root_.zero_add _).symm | b, 0 =>
 by…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `ZNum.cast_sub`：cast_sub [AddCommGroupWithOne α] (m n) : ((m - n : ZNum) 
: α) = m - n
-/
theorem to_of_int (n : ℤ) : ((n : ZNum) : ℤ) = n :=
  Int.inductionOn' n 0 (by simp) (by simp) (by simp)

@[simp]
/-
**ZNum.of_nat_toZNumNeg** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：of_nat_toZNumNeg (n : Nat) : Num.toZNumNeg n = -n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.of_nat_toZNum`：of_nat_toZNum (n : Nat) : Num.toZNum n = n
· 使用定理 `Num.zneg_toZNum`：zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg
-/
theorem of_nat_toZNumNeg (n : ℕ) : Num.toZNumNeg n = -n := by rw [← of_nat_toZNum, Num.zneg_toZNum]

@[simp, norm_cast]
/-
**ZNum.of_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：of_intCast [AddGroupWithOne α] (n : Int) : ((n : ZNum) : α) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.cast_to_int`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ZNum)
, ↑↑n = ↑n
· 使用定理 `ZNum.to_of_int`：to_of_int (n : Int) : ((n : ZNum) : Int) = n
-/
theorem of_intCast [AddGroupWithOne α] (n : ℤ) : ((n : ZNum) : α) = n := by
  rw [← cast_to_int, to_of_int]

@[simp, norm_cast]
/-
**ZNum.of_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：of_natCast [AddGroupWithOne α] (n : Nat) : ((n : ZNum) : α) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZNum.of_intCast`：of_intCast [AddGroupWithOne α] (n : Int) : ((n : ZNum) 
: α) = n
-/
theorem of_natCast [AddGroupWithOne α] (n : ℕ) : ((n : ZNum) : α) = n := by
  rw [← Int.cast_natCast, of_intCast, Int.cast_natCast]

@[simp, norm_cast]
/-
**ZNum.dvd_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：dvd_to_int (m n : ZNum) : (m : Int) ∣ n ↔ m ∣ n
参数：m n : ZNum。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.of_to_int`：of_to_int (n : ZNum) : ((n : Int) : ZNum) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ZNum.mul_to_int`：∀ (m n : ZNum), ↑(m * n) = ↑m * ↑n
-/
theorem dvd_to_int (m n : ZNum) : (m : ℤ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_int n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e]⟩⟩

end ZNum

namespace PosNum

/-
**PosNum.divMod_to_nat_aux** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：divMod_to_nat_aux {n d : PosNum} {q r : Num} (h₁ : (r : Nat) + d * ((q : N
at) + q) = n) (h₂ : (r : Nat) < 2 * d) : ((divModAux d q r).2 + d * (divModAux d
 q r).1 : Nat) = ↑n ∧ ((divModAux d q r).2 : Nat) < d
参数：h₁ : (r : Nat) + d * ((q : Nat) + q) = n；h₂ : (r : Nat) < 2 * d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Num.mem_ofZNum'`：∀ {m : Num} {n : ZNum}, m ∈ Num.ofZNum' n ↔ n = m.toZNu
m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.to_int_inj`：to_int_inj {m n : ZNum} : (m : Int) = n ↔ m = n
· 使用定理 `Num.cast_toZNum`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst
_2 : Add α] [inst_3 : Neg α] (n : Num), ↑n.toZNum = ↑n
· 使用定理 `Num.cast_sub'`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (m n : Num), 
↑(m.sub' n) = ↑m - ↑n
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Num.cast_bit0`：cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) =
 2 * (n : α)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Num.to_of_nat`：∀ (n : ℕ), ↑↑n = n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Num.cast_bit1`：cast_bit1 [NonAssocSemiring α] (n : Num) : (n.bit1 : α) =
 2 * (n : α) + 1
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
（共 42 条，此处仅展示前 30 条）
-/
theorem divMod_to_nat_aux {n d : PosNum} {q r : Num} (h₁ : (r : ℕ) + d * ((q : ℕ) + q) = n)
    (h₂ : (r : ℕ) < 2 * d) :
    ((divModAux d q r).2 + d * (divModAux d q r).1 : ℕ) = ↑n ∧ ((divModAux d q r).2 : ℕ) < d := by
  unfold divModAux
  have : ∀ {r₂}, Num.ofZNum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : ℕ) = r₂ + d := by
    intro r₂
    apply Num.mem_ofZNum'.trans
    rw [← ZNum.to_int_inj, Num.cast_toZNum, Num.cast_sub', sub_eq_iff_eq_add, ← Int.natCast_inj]
    simp
  rcases e : Num.ofZNum' (Num.sub' r (Num.pos d)) with - | r₂
  · rw [Num.cast_bit0, two_mul]
    refine ⟨h₁, lt_of_not_ge fun h => ?_⟩
    obtain ⟨r₂, e'⟩ := Nat.le.dest h
    rw [← Num.to_of_nat r₂, add_comm] at e'
    cases e.symm.trans (this.2 e'.symm)
  · have := this.1 e
    simp only [Num.cast_bit1]
    constructor
    · rwa [two_mul, add_comm _ 1, mul_add, mul_one, ← add_assoc, ← this]
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂
/-
**PosNum.divMod_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：divMod_to_nat (d n : PosNum) : (n / d : Nat) = (divMod d n).1 ∧ (n % d : N
at) = (divMod d n).2
参数：d n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_mod_unique`：∀ {b a d c : ℕ}, 0 < b → (a / b = d ∧ a % b = c ↔ c 
+ b * d = a ∧ c < b)
· 使用定理 `PosNum.cast_pos`：cast_pos [Semiring α] [PartialOrder α] [IsStrictOrdered
Ring α] (n : PosNum) : 0 < (n : α)
· 使用定理 `PosNum.divMod_to_nat_aux`：divMod_to_nat_aux {n d : PosNum} {q r : Num} (
h₁ : (r : Nat) + d * ((q : Nat) + q) = n) (h₂ : (r : Nat) < 2 * d) : ((divModAux
 d q r).2 + d …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PosNum.divMod.eq_def`：∀ (d x : PosNum),   d.divMod x =     match x with 
    | n.bit0 =>       match d.divMod n with       | (q, r₁) => d.divModAux q r₁.
bit0     |…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Num.cast_bit1`：cast_bit1 [NonAssocSemiring α] (n : Num) : (n.bit1 : α) =
 2 * (n : α) + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Num.cast_bit0`：cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) =
 2 * (n : α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem divMod_to_nat (d n : PosNum) :
    (n / d : ℕ) = (divMod d n).1 ∧ (n % d : ℕ) = (divMod d n).2 := by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  induction n with
  | one =>
    exact divMod_to_nat_aux (by simp) (Nat.mul_le_mul_left 2 (PosNum.cast_pos d : (0 : ℕ) < d))
  | bit1 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux <;> simp only [Num.cast_bit1, cast_bit1]
    · rw [← two_mul, ← two_mul, add_right_comm, mul_left_comm, ← mul_add, IH.1]
    · lia
  | bit0 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux
    · simp only [Num.cast_bit0, cast_bit0]
      rw [← two_mul, ← two_mul, mul_left_comm, ← mul_add, ← IH.1]
    · simpa using IH.2

@[simp]
/-
**PosNum.div'_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n d : PosNum), ↑(n.div' d) = ↑n / ↑d
参数：n d : PosNum；n.div' d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PosNum.divMod_to_nat`：divMod_to_nat (d n : PosNum) : (n / d : Nat) = (di
vMod d n).1 ∧ (n % d : Nat) = (divMod d n).2
-/
theorem div'_to_nat (n d) : (div' n d : ℕ) = n / d :=
  (divMod_to_nat _ _).1.symm

@[simp]
/-
**PosNum.mod'_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n d : PosNum), ↑(n.mod' d) = ↑n % ↑d
参数：n d : PosNum；n.mod' d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PosNum.divMod_to_nat`：divMod_to_nat (d n : PosNum) : (n / d : Nat) = (di
vMod d n).1 ∧ (n % d : Nat) = (divMod d n).2
-/
theorem mod'_to_nat (n d) : (mod' n d : ℕ) = n % d :=
  (divMod_to_nat _ _).2.symm

end PosNum

namespace Num

@[simp]
/-
**Num.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n / 0 = 0
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem div_zero (n : Num) : n / 0 = 0 :=
  show n.div 0 = 0 by
    cases n
    · rfl
    · simp [Num.div]

@[simp, norm_cast]
/-
**Num.div_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n d : Num), ↑(n / d) = ↑n / ↑d
参数：n d : Num；n / d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.div_zero`：∀ (n : Num), n / 0 = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `PosNum.div'_to_nat`：∀ (n d : PosNum), ↑(n.div' d) = ↑n / ↑d
-/
theorem div_to_nat : ∀ n d, ((n / d : Num) : ℕ) = n / d
  | 0, 0 => by simp
  | 0, pos _ => (Nat.zero_div _).symm
  | pos _, 0 => (Nat.div_zero _).symm
  | pos _, pos _ => PosNum.div'_to_nat _ _

@[simp]
/-
**Num.mod_zero** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n % 0 = n
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mod_zero (n : Num) : n % 0 = n :=
  show n.mod 0 = n by
    cases n
    · rfl
    · simp [Num.mod]

@[simp, norm_cast]
/-
**Num.mod_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n d : Num), ↑(n % d) = ↑n % ↑d
参数：n d : Num；n % d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.mod_zero`：∀ (n : Num), n % 0 = n
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_mod`：∀ (b : ℕ), 0 % b = 0
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `PosNum.mod'_to_nat`：∀ (n d : PosNum), ↑(n.mod' d) = ↑n % ↑d
-/
theorem mod_to_nat : ∀ n d, ((n % d : Num) : ℕ) = n % d
  | 0, 0 => by simp
  | 0, pos _ => (Nat.zero_mod _).symm
  | pos _, 0 => (Nat.mod_zero _).symm
  | pos _, pos _ => PosNum.mod'_to_nat _ _
/-
**Num.gcd_to_nat_aux** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {n : ℕ} {a b : Num}, a ≤ b → (a * b).natSize ≤ n → ↑(Num.gcdAux n a b) =
 (↑a).gcd ↑b
参数：a * b；Num.gcdAux n a b；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_to_nat_aux :
    ∀ {n} {a b : Num}, a ≤ b → (a * b).natSize ≤ n → (gcdAux n a b : ℕ) = Nat.gcd a b
  | 0, 0, _, _ab, _h => (Nat.gcd_zero_left _).symm
  | 0, pos _, 0, ab, _h => (not_lt_of_ge ab).elim rfl
  | 0, pos _, pos _, _ab, h => (not_lt_of_ge h).elim <| PosNum.natSize_pos _
  | Nat.succ _, 0, _, _ab, _h => (Nat.gcd_zero_left _).symm
  | Nat.succ n, pos a, b, ab, h => by
    simp only [gcdAux, cast_pos]
    rw [Nat.gcd_rec, gcd_to_nat_aux, mod_to_nat]
    · rfl
    · rw [← le_to_nat, mod_to_nat]
      exact le_of_lt (Nat.mod_lt _ (PosNum.cast_pos _))
    rw [natSize_to_nat, mul_to_nat, Nat.size_le] at h ⊢
    rw [mod_to_nat, mul_comm]
    rw [pow_succ, ← Nat.mod_add_div b (pos a)] at h
    refine lt_of_mul_lt_mul_right (lt_of_le_of_lt ?_ h) (Nat.zero_le 2)
    rw [mul_two, mul_add]
    gcongr _ + _ * ?_
    grw [Nat.mod_lt, ← le_to_nat.2 ab]
    · simp
    · exact PosNum.cast_pos _

@[simp]
/-
**Num.gcd_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：gcd_to_nat : forall a b, (gcd a b : Nat) = Nat.gcd a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Num.natSize_to_nat`：natSize_to_nat (n) : natSize n = Nat.size n
· 使用定理 `Num.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : Num), 
↑(m * n) = ↑m * ↑n
· 使用定理 `Nat.size_le`：size_le {m n : Nat} : size m <= n ↔ m < 2 ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_lt_mul''`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b c d : α} [in
st_1 : Preorder α] [PosMulStrictMono α] [MulPosMono α],   a < b → c < d → 0 ≤ a 
→ …
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.lt_size_self`：lt_size_self (n : Nat) : n < 2 ^ size n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Num.gcd_to_nat_aux`：∀ {n : ℕ} {a b : Num}, a ≤ b → (a * b).natSize ≤ n →
 ↑(Num.gcdAux n a b) = (↑a).gcd ↑b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem gcd_to_nat : ∀ a b, (gcd a b : ℕ) = Nat.gcd a b := by
  have : ∀ a b : Num, (a * b).natSize ≤ a.natSize + b.natSize := by
    intros
    simp only [natSize_to_nat, cast_mul]
    rw [Nat.size_le, pow_add]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_le _) (Nat.zero_le _)
  intros
  unfold gcd
  split_ifs with h
  · exact gcd_to_nat_aux h (this _ _)
  · rw [Nat.gcd_comm]
    exact gcd_to_nat_aux (le_of_not_ge h) (this _ _)
/-
**Num.dvd_iff_mod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.dvd_to_nat`：dvd_to_nat (m n : Num) : (m : Nat) ∣ n ↔ m ∣ n
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Num.to_nat_inj`：to_nat_inj {m n : Num} : (m : Nat) = n ↔ m = n
· 使用定理 `Num.mod_to_nat`：∀ (n d : Num), ↑(n % d) = ↑n % ↑d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_nat, Nat.dvd_iff_mod_eq_zero, ← to_nat_inj, mod_to_nat]; rfl
/-
**Num.decidableDvd** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：DecidableRel fun x1 x2 => x1 ∣ x2
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Num.dvd_iff_mod_eq_zero`：dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m
 = 0
-/
instance decidableDvd : DecidableRel ((· ∣ ·) : Num → Num → Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero

end Num

/-
**PosNum.decidableDvd** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：DecidableRel fun x1 x2 => x1 ∣ x2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PosNum.decidableDvd : DecidableRel ((· ∣ ·) : PosNum → PosNum → Prop)
  | _a, _b => Num.decidableDvd _ _

namespace ZNum

@[simp]
/-
**ZNum.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n : ZNum), n / 0 = 0
参数：n : ZNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem div_zero (n : ZNum) : n / 0 = 0 :=
  show n.div 0 = 0 by cases n <;> rfl

@[simp, norm_cast]
/-
**ZNum.div_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n d : ZNum), ↑(n / d) = ↑n / ↑d
参数：n d : ZNum；n / d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZNum.div_zero`：∀ (n : ZNum), n / 0 = 0
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.zero_ediv`：∀ (b : ℤ), 0 / b = 0
· 使用定理 `Num.cast_toZNum`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst
_2 : Add α] [inst_3 : Neg α] (n : Num), ↑n.toZNum = ↑n
· 使用定理 `Num.to_nat_to_int`：to_nat_to_int (n : Num) : ((n : Nat) : Int) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosNum.div'_to_nat`：∀ (n d : PosNum), ↑(n.div' d) = ↑n / ↑d
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `Num.cast_toZNumNeg`：∀ {α : Type u_1} [inst : SubtractionMonoid α] [inst_
1 : One α] (n : Num), ↑n.toZNumNeg = -↑n
· 使用定理 `Int.ediv_neg`：∀ (a b : ℤ), a / -b = -(a / b)
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `PosNum.to_int_eq_succ_pred`：to_int_eq_succ_pred (n : PosNum) : (n : Int)
 = (n.pred' : Nat) + 1
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `Num.div_to_nat`：∀ (n d : Num), ↑(n / d) = ↑n / ↑d
· 使用定理 `PosNum.to_nat_eq_succ_pred`：to_nat_eq_succ_pred (n : PosNum) : (n : Nat)
 = n.pred' + 1
-/
theorem div_to_int : ∀ n d, ((n / d : ZNum) : ℤ) = n / d
  | 0, 0 => by simp [Int.ediv_zero]
  | 0, pos _ => (Int.zero_ediv _).symm
  | 0, neg _ => (Int.zero_ediv _).symm
  | pos _, 0 => (Int.ediv_zero _).symm
  | neg _, 0 => (Int.ediv_zero _).symm
  | pos n, pos d => (Num.cast_toZNum _).trans <| by rw [← Num.to_nat_to_int]; simp
  | pos n, neg d => (Num.cast_toZNumNeg _).trans <| by rw [← Num.to_nat_to_int]; simp
  | neg n, pos d =>
    show -_ = -_ / ↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat,
        Num.div_to_nat]
      change -[n.pred' / ↑d+1] = -[n.pred' / (d.pred' + 1)+1]
      rw [d.to_nat_eq_succ_pred]
  | neg n, neg d =>
    show ↑(PosNum.pred' n / Num.pos d).succ' = -_ / -↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat,
        Num.div_to_nat]
      change (Nat.succ (_ / d) : ℤ) = Nat.succ (n.pred' / (d.pred' + 1))
      rw [d.to_nat_eq_succ_pred]

@[simp, norm_cast]
/-
**ZNum.mod_to_int** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：∀ (n d : ZNum), ↑(n % d) = ↑n % ↑d
参数：n d : ZNum；n % d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.zero_emod`：∀ (b : ℤ), 0 % b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Num.cast_toZNum`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst
_2 : Add α] [inst_3 : Neg α] (n : Num), ↑n.toZNum = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.to_nat_to_int`：to_nat_to_int (n : Num) : ((n : Nat) : Int) = n
· 使用定理 `ZNum.cast_pos`：cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(pos n : α) = n
· 使用定理 `Num.mod_to_nat`：∀ (n d : Num), ↑(n % d) = ↑n % ↑d
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `ZNum.abs_to_nat`：∀ (n : ZNum), ↑n.abs = (↑n).natAbs
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Num.cast_sub'`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (m n : Num), 
↑(m.sub' n) = ↑m - ↑n
· 使用定理 `ZNum.cast_neg`：cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : 
(neg n : α) = -n
· 使用定理 `Num.succ_to_nat`：succ_to_nat (n) : (succ n : Nat) = n + 1
· 使用定理 `Int.subNatNat_eq_coe`：∀ {m n : ℕ}, Int.subNatNat m n = ↑m - ↑n
· 使用定理 `PosNum.to_int_eq_succ_pred`：to_int_eq_succ_pred (n : PosNum) : (n : Int)
 = (n.pred' : Nat) + 1
-/
theorem mod_to_int : ∀ n d, ((n % d : ZNum) : ℤ) = n % d
  | 0, _ => (Int.zero_emod _).symm
  | pos n, d =>
    (Num.cast_toZNum _).trans <| by
      rw [← Num.to_nat_to_int, cast_pos, Num.mod_to_nat, ← PosNum.to_nat_to_int, abs_to_nat]
      rfl
  | neg n, d =>
    (Num.cast_sub' _ _).trans <| by
      rw [← Num.to_nat_to_int, cast_neg, ← Num.to_nat_to_int, Num.succ_to_nat, Num.mod_to_nat,
          abs_to_nat, ← Int.subNatNat_eq_coe, n.to_int_eq_succ_pred]
      rfl

@[simp]
/-
**ZNum.gcd_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：gcd_to_nat (a b) : (gcd a b : Nat) = Int.gcd a b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Num.gcd_to_nat`：gcd_to_nat : forall a b, (gcd a b : Nat) = Nat.gcd a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZNum.abs_to_nat`：∀ (n : ZNum), ↑n.abs = (↑n).natAbs
-/
theorem gcd_to_nat (a b) : (gcd a b : ℕ) = Int.gcd a b :=
  (Num.gcd_to_nat _ _).trans <| by simp only [abs_to_nat]; rfl
/-
**ZNum.dvd_iff_mod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZNum`。
形式化陈述：dvd_iff_mod_eq_zero {m n : ZNum} : m ∣ n ↔ n % m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZNum.dvd_to_int`：dvd_to_int (m n : ZNum) : (m : Int) ∣ n ↔ m ∣ n
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `ZNum.to_int_inj`：to_int_inj {m n : ZNum} : (m : Int) = n ↔ m = n
· 使用定理 `ZNum.mod_to_int`：∀ (n d : ZNum), ↑(n % d) = ↑n % ↑d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_iff_mod_eq_zero {m n : ZNum} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_int, Int.dvd_iff_emod_eq_zero, ← to_int_inj, mod_to_int]; rfl
/-
**ZNum.decidableDvd** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：DecidableRel fun x1 x2 => x1 ∣ x2
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZNum.dvd_iff_mod_eq_zero`：dvd_iff_mod_eq_zero {m n : ZNum} : m ∣ n ↔ n %
 m = 0
-/
instance decidableDvd : DecidableRel ((· ∣ ·) : ZNum → ZNum → Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero

end ZNum

