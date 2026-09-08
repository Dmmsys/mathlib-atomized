/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Num.ZNum
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Primality for binary natural numbers

This file defines versions of `Nat.minFac` and `Nat.Prime` for `Num` and `PosNum`. As with other
`Num` definitions, they are not intended for general use (`Nat` should be used instead of `Num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `decide`, as well as in `#reduce`.

The default decidable instance for `Nat.Prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`Num` implements algorithms directly on binary natural numbers for this purpose.
-/

@[expose] public section


namespace PosNum

/-- Auxiliary function for computing the smallest prime factor of a `PosNum`. Unlike
`Nat.minFacAux`, we use a natural number `fuel` variable that is set to an upper bound on the
number of iterations. It is initialized to the number `n` we are determining primality for. Even
though this is exponential in the input (since it is a `Nat`, not a `Num`), it will get lazily
evaluated during kernel reduction, so we will only require about `sqrt n` unfoldings, for the
`sqrt n` iterations of the loop. -/
/-
**PosNum.minFacAux** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → ℕ → PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for computing the smallest prime factor of a `PosNum`. Unlike
`Nat.minFacAux`, we use a natural number `fuel` variable that is set to an upper
 bound on the
number of iterations. It is initialized to the number `n` we are determining pri
mality for. Even
though this is exponential in the input (since it is a `Nat`, not a `Num`), it w
ill get lazily
evaluated during kernel reduction, so we will only require about `sqrt n` unfold
ings, for the
`sqrt n` iterations of the loop.
-/
def minFacAux (n : PosNum) : ℕ → PosNum → PosNum
  | 0, _ => n
  | fuel + 1, k =>
    if n < k.bit1 * k.bit1 then n else if k.bit1 ∣ n then k.bit1 else minFacAux n fuel k.succ
/-
**PosNum.minFacAux_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：minFacAux_to_nat {fuel : Nat} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bi
t1) : (minFacAux n fuel k : Nat) = Nat.minFacAux n k.bit1
参数：h : Nat.sqrt n < fuel + k.bit1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.minFacAux.eq_1`：∀ (n x : PosNum), n.minFacAux 0 x = n
· 使用定理 `Nat.minFacAux.eq_1`：∀ (n x : ℕ), n.minFacAux x = if n < x * x then n els
e if x ∣ n then x else n.minFacAux (x + 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PosNum.minFacAux.eq_2`：∀ (n x : PosNum) (fuel : ℕ),   n.minFacAux fuel.s
ucc x = if n < x.bit1 * x.bit1 then n else if x.bit1 ∣ n then x.bit1 else n.minF
acAux fuel …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosNum.cast_succ`：cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n 
: α) = n + 1
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
-/
theorem minFacAux_to_nat {fuel : ℕ} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1) :
    (minFacAux n fuel k : ℕ) = Nat.minFacAux n k.bit1 := by
  induction fuel generalizing k <;> rw [minFacAux, Nat.minFacAux]
  case zero =>
    rw [Nat.zero_add, Nat.sqrt_lt] at h
    simp only [h, ite_true]
  case succ fuel ih =>
    simp_rw [← mul_to_nat]
    simp only [cast_lt, dvd_to_nat]
    split_ifs <;> try rfl
    rw [ih] <;> [congr; convert! Nat.lt_succ_of_lt h using 1] <;>
      simp only [cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
        add_left_comm, ← one_add_one_eq_two]

/-- Returns the smallest prime factor of `n ≠ 1`. -/
/-
**PosNum.minFac** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the smallest prime factor of `n ≠ 1`.
-/
def minFac : PosNum → PosNum
  | 1 => 1
  | bit0 _ => 2
  | bit1 n => minFacAux (bit1 n) n 1

@[simp]
/-
**PosNum.minFac_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：minFac_to_nat (n : PosNum) : (minFac n : Nat) = Nat.minFac n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PosNum.minFac.eq_3`：∀ (n : PosNum), n.bit1.minFac = n.bit1.minFacAux (↑n
) 1
· 使用定理 `Nat.minFac_eq`：minFac_eq (n : Nat) : minFac n = if 2 ∣ n then 2 else min
FacAux n 3
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `PosNum.minFacAux_to_nat`：minFacAux_to_nat {fuel : Nat} {n k : PosNum} (h
 : Nat.sqrt n < fuel + k.bit1) : (minFacAux n fuel k : Nat) = Nat.minFacAux n k.
bit1
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 35 条，此处仅展示前 30 条）
-/
theorem minFac_to_nat (n : PosNum) : (minFac n : ℕ) = Nat.minFac n := by
  obtain - | n := n
  · simp [minFac]
  · rw [minFac, Nat.minFac_eq, if_neg]
    swap
    · simp [← two_mul]
    rw [minFacAux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    rw [Nat.sqrt_lt]
    calc
      (n : ℕ) + (n : ℕ) + 1 ≤ (n : ℕ) + (n : ℕ) + (n : ℕ) := by simp
      _ = (n : ℕ) * (1 + 1 + 1) := by simp only [mul_add, mul_one]
      _ < _ := by simp [mul_lt_mul]
  · rw [minFac, Nat.minFac_eq, if_pos]
    · rfl
    simp [← two_mul]

/-- Primality predicate for a `PosNum`. -/
@[simp]
/-
**PosNum.Prime** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：Prime (n : PosNum) : Prop
参数：n : PosNum。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Primality predicate for a `PosNum`.
-/
def Prime (n : PosNum) : Prop :=
  Nat.Prime n
/-
**PosNum.decidablePrime** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
形式化陈述：decidablePrime : DecidablePred PosNum.Prime | 1 => Decidable.isFalse Nat.n
ot_prime_one | bit0 n => decidable_of_iff' (n = 1) (by refine Nat.prime_def_minF
ac.trans ((and_iff_right ?_).trans <| eq_comm.trans ?_) · exact add_le_add (Nat.
succ_le_of_lt (to_nat_pos _)) (Nat.succ_le_of_lt (to_nat_pos _)) rw [← minFac_to
_nat]; rw [to_nat_inj] exact ⟨bit0.inj, congr_arg _⟩) | bit1 n => decidable_of_i
ff' (minFacAux (bit1 n) n 1 = bit1 n) by refine Nat.prime_def_minFac.trans ((and
_iff_right ?_).trans ?_) ·
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
-/
instance decidablePrime : DecidablePred PosNum.Prime
  | 1 => Decidable.isFalse Nat.not_prime_one
  | bit0 n =>
    decidable_of_iff' (n = 1)
      (by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans <| eq_comm.trans ?_)
        · exact add_le_add (Nat.succ_le_of_lt (to_nat_pos _)) (Nat.succ_le_of_lt (to_nat_pos _))
        rw [← minFac_to_nat, to_nat_inj]
        exact ⟨bit0.inj, congr_arg _⟩)
  | bit1 n =>
    decidable_of_iff' (minFacAux (bit1 n) n 1 = bit1 n) <| by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans ?_)
        · simp only [cast_bit1]
          have := to_nat_pos n
          lia
        rw [← minFac_to_nat, to_nat_inj]; rfl

end PosNum

namespace Num

/-- Returns the smallest prime factor of `n ≠ 1`. -/
/-
**Num.minFac** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the smallest prime factor of `n ≠ 1`.
-/
def minFac : Num → PosNum
  | 0 => 2
  | pos n => n.minFac

@[simp]
/-
**Num.minFac_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), ↑n.minFac = (↑n).minFac
参数：n : Num；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.minFac_to_nat`：minFac_to_nat (n : PosNum) : (minFac n : Nat) = Na
t.minFac n
-/
theorem minFac_to_nat : ∀ n : Num, (minFac n : ℕ) = Nat.minFac n
  | 0 => rfl
  | pos _ => PosNum.minFac_to_nat _

/-- Primality predicate for a `Num`. -/
@[simp]
/-
**Num.Prime** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Prime (n : Num) : Prop
参数：n : Num。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Primality predicate for a `Num`.
-/
def Prime (n : Num) : Prop :=
  Nat.Prime n
/-
**Num.decidablePrime** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：DecidablePred Num.Prime
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_zero`：¬Nat.Prime 0
-/
instance decidablePrime : DecidablePred Num.Prime
  | 0 => Decidable.isFalse Nat.not_prime_zero
  | pos n => PosNum.decidablePrime n

end Num

