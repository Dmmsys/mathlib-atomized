/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Digits of a natural number

This provides lemma about the digits of natural numbers.
-/

public section

namespace Nat

variable {n : ℕ}

/-
**Nat.ofDigits_eq_sum_mapIdx_aux** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_eq_sum_mapIdx_aux (b : Nat) (l : List Nat) : (l.zipWith ((fun a i
 : Nat => a * b ^ (i + 1))) (List.range l.length)).sum = b * (l.zipWith (fun a i
 => a * b ^ i) (List.range l.length)).sum
参数：b : Nat；l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）
-/
theorem ofDigits_eq_sum_mapIdx_aux (b : ℕ) (l : List ℕ) :
    (l.zipWith ((fun a i : ℕ => a * b ^ (i + 1))) (List.range l.length)).sum =
      b * (l.zipWith (fun a i => a * b ^ i) (List.range l.length)).sum := by
  suffices
    l.zipWith (fun a i : ℕ => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i => b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; ring
/-
**Nat.ofDigits_eq_sum_mapIdx** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_eq_sum_mapIdx (b : Nat) (L : List Nat) : ofDigits b L = (L.mapIdx
 fun i a => a * b ^ i).sum
参数：b : Nat；L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mapIdx_eq_zipIdx_map`：∀ {α : Type u_1} {β : Type u_2} {l : List α} 
{f : ℕ → α → β},   List.mapIdx f l =     List.map       (fun x =>         match 
x with         …
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `List.zipIdx_eq_zip_range'`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.zipI
dx i = l.zip (List.range' i l.length)
· 使用定理 `List.map_zip_eq_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : α × β → γ} {l : List α} {l' : List β},   List.map f (l.zip l') = List.zipWi
th (Function.…
· 使用定理 `Nat.ofDigits_eq_foldr`：ofDigits_eq_foldr {α : Type*} [Semiring α] (b : α
) (L : List Nat) : ofDigits b L = List.foldr (fun x y => ↑x + b * y) 0 L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.range_eq_range'`：∀ {n : ℕ}, List.range n = List.range' 0 n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.zipWith_self`：∀ {α : Type u_1} {δ : Type u_2} {f : α → α → δ} {l : 
List α}, List.zipWith f l l = List.map (fun a => f a a) l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.range_succ_eq_map`：∀ {n : ℕ}, List.range (n + 1) = 0 :: List.map Na
t.succ (List.range n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `List.zipWith_map_right`：∀ {α : Type u_1} {β : Type u_2} {β' : Type u_3} 
{γ : Type u_4} {l₁ : List α} {l₂ : List β} {f : β → β'}   {g : α → β' → γ}, List
.zipWith g l…
· 使用定理 `Nat.ofDigits_eq_sum_mapIdx_aux`：ofDigits_eq_sum_mapIdx_aux (b : Nat) (l 
: List Nat) : (l.zipWith ((fun a i : Nat => a * b ^ (i + 1))) (List.range l.leng
th)).sum = b * (l.zi…
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
-/
theorem ofDigits_eq_sum_mapIdx (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum := by
  rw [List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', List.map_zip_eq_zipWith,
    ofDigits_eq_foldr, ← List.range_eq_range']
  induction L with
  | nil => simp
  | cons hd tl hl =>
    simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using!
      Or.inl hl

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/

/-
**Nat.length_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：length_digits (b n : Nat) (hb : 1 < b) (hn : n != 0) : (b.digits n).length
 = b.log n + 1
参数：b n : Nat；hb : 1 < b；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_eq_cons_digits_div`：digits_eq_cons_digits_div {b n : Nat} (h 
: 1 < b) (w : n != 0) : digits b n = (n % b) :: digits b (n / b)
· 使用定理 `List.length.eq_2`：∀ {α : Type u_1} (head : α) (tail : List α), (head :: 
tail).length = tail.length + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.log_div_base`：log_div_base (b n : Nat) : log b (n / b) = log b n - 1
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.log_pos`：log_pos {b n : Nat} (hb : 1 < b) (hbn : b <= n) : 0 < log b
 n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0

--- 原说明 ---
### Properties

This section contains various lemmas of properties relating to `digits` and `ofD
igits`.
-/
theorem length_digits (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) :
    (b.digits n).length = b.log n + 1 := by
  induction n using Nat.strong_induction_on with | _ n IH
  rw [digits_eq_cons_digits_div hb hn, List.length]
  by_cases h : n / b = 0
  · simp [h]
    aesop
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    rw [IH _ this h, log_div_base, tsub_add_cancel_of_le]
    refine Nat.succ_le_of_lt (log_pos hb ?_)
    contrapose! h
    exact div_eq_of_lt h

@[deprecated (since := "2026-03-18")] alias digits_len := length_digits
/-
**Nat.digits_length_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_length_le_iff {b k : Nat} (hb : 1 < b) (n : Nat) : (b.digits n).len
gth <= k ↔ n < b ^ k
参数：hb : 1 < b；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Nat.length_digits`：length_digits (b n : Nat) (hb : 1 < b) (hn : n != 0) 
: (b.digits n).length = b.log n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.log_lt_iff_lt_pow`：log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : log b y < x ↔ y < b ^ x
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
-/
theorem digits_length_le_iff {b k : ℕ} (hb : 1 < b) (n : ℕ) :
    (b.digits n).length ≤ k ↔ n < b ^ k := by
  by_cases h : n = 0
  · have : 0 < b ^ k := by positivity
    simpa [h]
  rw [length_digits b n hb h, ← log_lt_iff_lt_pow hb h]
  exact add_one_le_iff
/-
**Nat.lt_digits_length_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_digits_length_iff {b k : Nat} (hb : 1 < b) (n : Nat) : k < (b.digits n)
.length ↔ b ^ k <= n
参数：hb : 1 < b；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_length_le_iff`：digits_length_le_iff {b k : Nat} (hb : 1 < b) 
(n : Nat) : (b.digits n).length <= k ↔ n < b ^ k
-/
theorem lt_digits_length_iff {b k : ℕ} (hb : 1 < b) (n : ℕ) :
    k < (b.digits n).length ↔ b ^ k ≤ n := by
  contrapose!
  exact digits_length_le_iff hb n
/-
**Nat.getLast_digit_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：getLast_digit_ne_zero (b : Nat) {m : Nat} (hm : m != 0) : (digits b m).get
Last (digits_ne_nil_iff_ne_zero.mpr hm) != 0
参数：b : Nat；hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.digits_ne_nil_iff_ne_zero`：digits_ne_nil_iff_ne_zero {b n : Nat} : d
igits b n != [] ↔ n != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.getLast_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} (w : List.repli
cate n a ≠ []), (List.replicate n a).getLast w = a
· 使用定理 `Nat.digits_of_lt`：digits_of_lt (b x : Nat) (hx : x != 0) (hxb : x < b) :
 digits b x = [x]
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.digits_getLast`：digits_getLast {b : Nat} (m : Nat) (h : 1 < b) (p q)
 : (digits b m).getLast p = (digits b (m / b)).getLast q
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.one_lt_succ_succ`：∀ (n : ℕ), 1 < n.succ.succ
-/
theorem getLast_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) ≠ 0 := by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
    · simp
  · simp
  revert hm
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro hn
  by_cases! hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_getLast n (le_add_left 2 b)]
    refine IH _ (Nat.div_lt_self hn.bot_lt (one_lt_succ_succ b)) ?_
    rw [← pos_iff_ne_zero]
    exact Nat.div_pos hnb (zero_lt_succ (succ b))
/-
**Nat.digits_append_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_append_digits {b m n : Nat} (hb : 0 < b) : digits b n ++ digits b m
 = digits b (n + b ^ (digits b n).length * m)
参数：hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.replicate_append_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {m : ℕ
}, List.replicate n a ++ List.replicate m a = List.replicate (n + m) a
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_digits_append_digits`：ofDigits_digits_append_digits {b m n 
: Nat} : ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m
· 使用定理 `Nat.digits_ofDigits`：digits_ofDigits (b : Nat) (h : 1 < b) (L : List Nat
) (w₁ : forall l in L, l < b) (w₂ : forall h : L != [], L.getLast h != 0) : digi
ts b (ofD…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
· 使用定理 `Nat.digits_lt_base`：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in
 digits b m) : d < b
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `Nat.getLast_digit_ne_zero`：getLast_digit_ne_zero (b : Nat) {m : Nat} (hm
 : m != 0) : (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) != 0
· 使用定理 `Nat.digits_ne_nil_iff_ne_zero`：digits_ne_nil_iff_ne_zero {b n : Nat} : d
igits b n != [] ↔ n != 0
· 使用定理 `List.append_ne_nil_of_right_ne_nil`：∀ {α : Type u_1} {t : List α} (s : L
ist α), t ≠ [] → s ++ t ≠ []
· 使用定理 `List.getLast_append_of_right_ne_nil`：getLast_append_of_right_ne_nil (l₁ 
l₂ : List α) (h : l₂ != []) : getLast (l₁ ++ l₂) (append_ne_nil_of_right_ne_nil 
l₁ h) = getLast l₂ h
-/
theorem digits_append_digits {b m n : ℕ} (hb : 0 < b) :
    digits b n ++ digits b m = digits b (n + b ^ (digits b n).length * m) := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with (rfl | hb)
  · simp
  rw [← ofDigits_digits_append_digits]
  refine (digits_ofDigits b hb _ (fun l hl => ?_) (fun h_append => ?_)).symm
  · rcases (List.mem_append.mp hl) with (h | h) <;> exact digits_lt_base hb h
  · by_cases h : digits b m = []
    · simp only [h, List.append_nil] at h_append ⊢
      exact getLast_digit_ne_zero b <| digits_ne_nil_iff_ne_zero.mp h_append
    · exact (List.getLast_append_of_right_ne_nil _ _ h) ▸
          (getLast_digit_ne_zero _ <| digits_ne_nil_iff_ne_zero.mp h)
/-
**Nat.digits_append_zeroes_append_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_append_zeroes_append_digits {b k m n : Nat} (hb : 1 < b) (hm : 0 < 
m) : digits b n ++ List.replicate k 0 ++ digits b m = digits b (n + b ^ ((digits
 b n).length + k) * m)
参数：hb : 1 < b；hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.digits_base_pow_mul`：digits_base_pow_mul {b k m : Nat} (hb : 1 < b) 
(hm : 0 < m) : digits b (b ^ k * m) = List.replicate k 0 ++ digits b m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.digits_append_digits`：digits_append_digits {b m n : Nat} (hb : 0 < b
) : digits b n ++ digits b m = digits b (n + b ^ (digits b n).length * m)
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 32 条，此处仅展示前 30 条）
-/
theorem digits_append_zeroes_append_digits {b k m n : ℕ} (hb : 1 < b) (hm : 0 < m) :
    digits b n ++ List.replicate k 0 ++ digits b m =
    digits b (n + b ^ ((digits b n).length + k) * m) := by
  rw [List.append_assoc, ← digits_base_pow_mul hb hm]
  simp only [digits_append_digits (zero_lt_of_lt hb), digits_inj_iff, add_right_inj]
  ring
/-
**Nat.length_digits_le_length_digits_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：length_digits_le_length_digits_succ (b n : Nat) : (digits b n).length <= (
digits b (n + 1)).length
参数：b n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
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
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_right`：of_le_right [LE α] (h : (a : α
) <= b) (eq : b = b') : a <= b'
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.digits_zero_succ'`：∀ {n : ℕ}, n ≠ 0 → Nat.digits 0 n = [n]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.length_digits`：length_digits (b n : Nat) (hb : 1 < b) (hn : n != 0) 
: (b.digits n).length = b.log n + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 35 条，此处仅展示前 30 条）
-/
theorem length_digits_le_length_digits_succ (b n : ℕ) :
    (digits b n).length ≤ (digits b (n + 1)).length := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases le_or_gt b 1 with hb | hb
  · interval_cases b <;> simp +arith [digits_zero_succ', hn]
  simpa [length_digits, hb, hn] using log_mono_right (le_succ _)

@[deprecated (since := "2026-03-18")]
alias digits_len_le_digits_len_succ := length_digits_le_length_digits_succ
/-
**Nat.le_length_digits_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_length_digits_le (b n m : Nat) (h : n <= m) : (digits b n).length <= (d
igits b m).length
参数：b n m : Nat；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `Nat.length_digits_le_length_digits_succ`：length_digits_le_length_digits_
succ (b n : Nat) : (digits b n).length <= (digits b (n + 1)).length
-/
theorem le_length_digits_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
  monotone_nat_of_le_succ (length_digits_le_length_digits_succ b) h

@[deprecated (since := "2026-03-18")] alias le_digits_len_le := le_length_digits_le
/-
**Nat.pow_length_le_mul_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_length_le_mul_ofDigits {b : Nat} {l : List Nat} (hl : l != []) (hl2 : 
l.getLast hl != 0) : (b + 2) ^ l.length <= (b + 2) * ofDigits (b + 2) l
参数：hl : l != []；hl2 : l.getLast hl != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dropLast_append_getLast`：∀ {α : Type u} {l : List α} (h : l ≠ []), 
l.dropLast ++ [l.getLast h] = l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.ofDigits_append`：ofDigits_append {b : Nat} {l1 l2 : List Nat} : ofDi
gits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2
· 使用定理 `Nat.ofDigits_singleton`：ofDigits_singleton {b n : Nat} : ofDigits b [n] 
= n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem pow_length_le_mul_ofDigits {b : ℕ} {l : List ℕ} (hl : l ≠ []) (hl2 : l.getLast hl ≠ 0) :
    (b + 2) ^ l.length ≤ (b + 2) * ofDigits (b + 2) l := by
  rw [← List.dropLast_append_getLast hl]
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, ofDigits_append,
    List.length_dropLast, ofDigits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  refine le_trans ?_ (Nat.le_add_left _ _)
  have : 0 < l.getLast hl := by rwa [pos_iff_ne_zero]
  convert! Nat.mul_le_mul_left ((b + 2) ^ (l.length - 1)) this using 1
  rw [Nat.mul_one]

/-- Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
/-
**Nat.base_pow_length_digits_le'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：base_pow_length_digits_le' (b m : Nat) (hm : m != 0) : (b + 2) ^ (digits (
b + 2) m).length <= (b + 2) * m
参数：b m : Nat；hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.digits_ne_nil_iff_ne_zero`：digits_ne_nil_iff_ne_zero {b n : Nat} : d
igits b n != [] ↔ n != 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `Nat.pow_length_le_mul_ofDigits`：pow_length_le_mul_ofDigits {b : Nat} {l 
: List Nat} (hl : l != []) (hl2 : l.getLast hl != 0) : (b + 2) ^ l.length <= (b 
+ 2) * ofDigits (b +…
· 使用定理 `Nat.getLast_digit_ne_zero`：getLast_digit_ne_zero (b : Nat) {m : Nat} (hm
 : m != 0) : (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) != 0

--- 原说明 ---
Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le' (b m : ℕ) (hm : m ≠ 0) :
    (b + 2) ^ (digits (b + 2) m).length ≤ (b + 2) * m := by
  have : digits (b + 2) m ≠ [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert! @pow_length_le_mul_ofDigits b (digits (b + 2) m) this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]

/-- Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
/-
**Nat.base_pow_length_digits_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：base_pow_length_digits_le (b m : Nat) (hb : 1 < b) : m != 0 -> b ^ (digits
 b m).length <= b * m
参数：b m : Nat；hb : 1 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 1 < b) :
    m ≠ 0 → b ^ (digits b m).length ≤ b * m := by
  rcases b with (_ | _ | b) <;> simp_all [base_pow_length_digits_le']

open Finset
/-
**Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sub_one_mul_sum_div_pow_eq_sub_sum_digits {p : Nat} (L : List Nat) {h_none
mpty} (h_ne_zero : L.getLast h_nonempty != 0) (h_lt : forall l in L, l < p) : (p
 - 1) * ∑ i in range L.length, (ofDigits p L) / p ^ i.succ = (ofDigits p L) - L.
sum
参数：L : List Nat；h_ne_zero : L.getLast h_nonempty != 0；h_lt : forall l in L, l < 
p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用引理 `trichotomous`：trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b 
∨ a = b ∨ b ≺ a
· 使用定理 `Nat.instTrichotomousLt`：Std.Trichotomous fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Nat.self_div_pow_eq_ofDigits_drop`：self_div_pow_eq_ofDigits_drop {p : Na
t} (i n : Nat) (h : 2 <= p) : n / p ^ i = ofDigits p ((p.digits n).drop i)
· 使用定理 `Nat.digits_ofDigits`：digits_ofDigits (b : Nat) (h : 1 < b) (L : List Nat
) (w₁ : forall l in L, l < b) (w₂ : forall h : L != [], L.getLast h != 0) : digi
ts b (ofD…
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `List.drop_length`：∀ {α : Type u_1} {l : List α}, List.drop l.length l = 
[]
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
（共 72 条，此处仅展示前 30 条）
-/
theorem sub_one_mul_sum_div_pow_eq_sub_sum_digits {p : ℕ}
    (L : List ℕ) {h_nonempty} (h_ne_zero : L.getLast h_nonempty ≠ 0) (h_lt : ∀ l ∈ L, l < p) :
    (p - 1) * ∑ i ∈ range L.length, (ofDigits p L) / p ^ i.succ = (ofDigits p L) - L.sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction L with
    | nil => simp [ofDigits]
    | cons hd tl ih =>
      simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
          digits_ofDigits p h (hd :: tl) h_lt (fun _ => h_ne_zero)]
      simp only [ofDigits]
      rw [sum_range_succ, Nat.cast_id]
      simp only [List.drop, List.drop_length]
      obtain rfl | h' := em <| tl = []
      · simp [ofDigits]
      · have w₁' := fun l hl ↦ h_lt l <| List.mem_cons_of_mem hd hl
        have w₂' := fun (h : tl ≠ []) ↦ (List.getLast_cons h) ▸ h_ne_zero
        have ih := ih (w₂' h') w₁'
        simp only [self_div_pow_eq_ofDigits_drop _ _ h, digits_ofDigits p h tl w₁' w₂',
          ← Nat.one_add] at ih
        have := sum_singleton (fun x ↦ ofDigits p <| tl.drop x) tl.length
        rw [← Ico_succ_singleton, List.drop_length, ofDigits] at this
        have h₁ : 1 ≤ tl.length := List.length_pos_iff.mpr h'
        rw [← sum_range_add_sum_Ico _ <| h₁, ← add_zero (∑ x ∈ Ico _ _, ofDigits p (tl.drop x)),
            ← this, sum_Ico_consecutive _ h₁ <| (le_add_right tl.length 1),
            ← sum_Ico_add _ 0 tl.length 1,
            Ico_zero_eq_range, mul_add, mul_add, ih, range_one, sum_singleton, List.drop, ofDigits,
            mul_zero, add_zero, ← Nat.add_sub_assoc <| sum_le_ofDigits _ <| Nat.le_of_lt h]
        nth_rw 2 [← one_mul <| ofDigits p tl]
        rw [← add_mul, Nat.sub_add_cancel (one_le_of_lt h), Nat.add_sub_add_left]
  · simp [ofDigits_one]
  · simp [lt_one_iff.mp h]
    cases L
    · rfl
    · simp [ofDigits]
/-
**Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits** 是 Mathlib 中的一个定理，位于命名空间 `N
at`。
形式化陈述：sub_one_mul_sum_log_div_pow_eq_sub_sum_digits {p : Nat} (n : Nat) : (p - 1
) * ∑ i in range (log p n).succ, n / p ^ i.succ = n - (p.digits n).sum
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous`：trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b 
∨ a = b ∨ b ≺ a
· 使用定理 `Nat.instTrichotomousLt`：Std.Trichotomous fun x1 x2 => x1 < x2
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.length_digits`：length_digits (b n : Nat) (hb : 1 < b) (hn : n != 0) 
: (b.digits n).length = b.log n + 1
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits`：sub_one_mul_sum_div_pow_e
q_sub_sum_digits {p : Nat} (L : List Nat) {h_nonempty} (h_ne_zero : L.getLast h_
nonempty != 0) (h_lt : forall l in …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.digits_ne_nil_iff_ne_zero`：digits_ne_nil_iff_ne_zero {b n : Nat} : d
igits b n != [] ↔ n != 0
· 使用定理 `Nat.getLast_digit_ne_zero`：getLast_digit_ne_zero (b : Nat) {m : Nat} (hm
 : m != 0) : (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) != 0
· 使用定理 `Nat.digits_lt_base`：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in
 digits b m) : d < b
· 使用定理 `Nat.log_one_left`：log_one_left : forall n, log 1 n = 0
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
（共 48 条，此处仅展示前 30 条）
-/
theorem sub_one_mul_sum_log_div_pow_eq_sub_sum_digits {p : ℕ} (n : ℕ) :
    (p - 1) * ∑ i ∈ range (log p n).succ, n / p ^ i.succ = n - (p.digits n).sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · convert!
      sub_one_mul_sum_div_pow_eq_sub_sum_digits (p.digits n) (getLast_digit_ne_zero p hn) <|
        (fun l a ↦ digits_lt_base h a)
      · refine (length_digits p n h hn).symm
      all_goals exact (ofDigits_digits p n).symm
  · simp
  · simp [lt_one_iff.mp h]
    cases n
    all_goals simp

/-! ### Binary -/


/-
**Nat.digits_two_eq_bits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_two_eq_bits (n : Nat) : digits 2 n = n.bits.map fun b => cond b 1 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `Nat.zero_bits`：zero_bits : bits 0 = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.digits_of_two_le_of_pos`：digits_of_two_le_of_pos {b : Nat} (hb : 2 <
= b) (hn : 0 < n) : Nat.digits b n = n % b :: Nat.digits b (n / b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Nat.one_bits`：one_bits : Nat.bits 1 = [true]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.bits_append_bit`：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 ->
 b = true) : (bit b n).bits = b :: n.bits
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.digits_def'`：∀ {b : ℕ}, 1 < b → ∀ {n : ℕ}, 0 < n → b.digits n = n % 
b :: b.digits (n / b)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
### Binary
-/
theorem digits_two_eq_bits (n : ℕ) : digits 2 n = n.bits.map fun b => cond b 1 0 := by
  induction n using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp
  | bit b n h ih =>
    rw [bits_append_bit _ _ fun hn => absurd hn h]
    cases b
    · rw [digits_def' one_lt_two]
      · simpa [Nat.bit]
      · simpa [Nat.bit, pos_iff_ne_zero]
    · simpa [Nat.bit, add_comm, digits_add 2 one_lt_two 1 n, Nat.add_mul_div_left]

/-! ### Modular Arithmetic -/


-- This is really a theorem about polynomials.
/-
**Nat.dvd_ofDigits_sub_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_ofDigits_sub_ofDigits {α : Type*} [CommRing α] {a b k : α} (h : k ∣ a 
- b) (L : List Nat) : k ∣ ofDigits a L - ofDigits b L
参数：h : k ∣ a - b；L : List Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `dvd_mul_sub_mul`：dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy 
: k ∣ x - y) : k ∣ a * x - b * y
-/
theorem dvd_ofDigits_sub_ofDigits {α : Type*} [CommRing α] {a b k : α} (h : k ∣ a - b)
    (L : List ℕ) : k ∣ ofDigits a L - ofDigits b L := by
  induction L with
  | nil => change k ∣ 0 - 0; simp
  | cons d L ih =>
    simp only [ofDigits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih
/-
**Nat.ofDigits_modEq'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_modEq' (b b' : Nat) (k : Nat) (h : b ≡ b' [MOD k]) (L : List Nat)
 : ofDigits b L ≡ ofDigits b' L [MOD k]
参数：b b' : Nat；k : Nat；h : b ≡ b' [MOD k]；L : List Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
-/
theorem ofDigits_modEq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [MOD k] := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Nat.ModEq] at *
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
/-
**Nat.ofDigits_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_modEq (b k : Nat) (L : List Nat) : ofDigits b L ≡ ofDigits (b % k
) L [MOD k]
参数：b k : Nat；L : List Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofDigits_modEq'`：ofDigits_modEq' (b b' : Nat) (k : Nat) (h : b ≡ b' 
[MOD k]) (L : List Nat) : ofDigits b L ≡ ofDigits b' L [MOD k]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.mod_modEq`：mod_modEq (a n) : a % n ≡ a [MOD n]
-/
theorem ofDigits_modEq (b k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L
/-
**Nat.ofDigits_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_mod (b k : Nat) (L : List Nat) : ofDigits b L % k = ofDigits (b %
 k) L % k
参数：b k : Nat；L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofDigits_modEq`：ofDigits_modEq (b k : Nat) (L : List Nat) : ofDigits
 b L ≡ ofDigits (b % k) L [MOD k]
-/
theorem ofDigits_mod (b k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_modEq b k L
/-
**Nat.ofDigits_mod_eq_head** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_mod_eq_head! (b : Nat) (l : List Nat) : ofDigits b l % b = l.head
! % b
参数：b : Nat；l : List Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDigits_mod_eq_head! (b : ℕ) (l : List ℕ) : ofDigits b l % b = l.head! % b := by
  induction l <;> simp [Nat.ofDigits]
/-
**Nat.head** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：head!_digits {b n : Nat} (h : b != 1) : (Nat.digits b n).head! = n % b
参数：h : b != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_digits {b n : ℕ} (h : b ≠ 1) : (Nat.digits b n).head! = n % b := by
  by_cases hb : 1 < b
  · rcases n with _ | n
    · simp
    · nth_rw 2 [← Nat.ofDigits_digits b (n + 1)]
      rw [Nat.ofDigits_mod_eq_head! _ _]
      exact (Nat.mod_eq_of_lt (Nat.digits_lt_base hb <| List.head!_mem_self <|
          Nat.digits_ne_nil_iff_ne_zero.mpr <| Nat.succ_ne_zero n)).symm
  · rcases n with _ | _ <;> simp_all [show b = 0 by lia]
/-
**Nat.ofDigits_zmodeq'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_zmodeq' (b b' : Int) (k : Nat) (h : b ≡ b' [ZMOD k]) (L : List Na
t) : ofDigits b L ≡ ofDigits b' L [ZMOD k]
参数：b b' : Int；k : Nat；h : b ≡ b' [ZMOD k]；L : List Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_emod`：∀ (a b n : ℤ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Int.mul_emod`：∀ (a b n : ℤ), a * b % n = a % n * (b % n) % n
-/
theorem ofDigits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Int.ModEq] at *
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]
/-
**Nat.ofDigits_zmodeq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_zmodeq (b : Int) (k : Nat) (L : List Nat) : ofDigits b L ≡ ofDigi
ts (b % k) L [ZMOD k]
参数：b : Int；k : Nat；L : List Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofDigits_zmodeq'`：ofDigits_zmodeq' (b b' : Int) (k : Nat) (h : b ≡ b
' [ZMOD k]) (L : List Nat) : ofDigits b L ≡ ofDigits b' L [ZMOD k]
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Int.mod_modEq`：mod_modEq (a n) : a % n ≡ a [ZMOD n]
-/
theorem ofDigits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L
/-
**Nat.ofDigits_zmod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_zmod (b : Int) (k : Nat) (L : List Nat) : ofDigits b L % k = ofDi
gits (b % k) L % k
参数：b : Int；k : Nat；L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofDigits_zmodeq`：ofDigits_zmodeq (b : Int) (k : Nat) (L : List Nat) 
: ofDigits b L ≡ ofDigits (b % k) L [ZMOD k]
-/
theorem ofDigits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_zmodeq b k L
/-
**Nat.modEq_digits_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_digits_sum (b b' : Nat) (h : b' % b = 1) (n : Nat) : n ≡ (digits b' 
n).sum [MOD b]
参数：b b' : Nat；h : b' % b = 1；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_one`：ofDigits_one (L : List Nat) : ofDigits 1 L = L.sum
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.ofDigits_modEq`：ofDigits_modEq (b k : Nat) (L : List Nat) : ofDigits
 b L ≡ ofDigits (b % k) L [MOD k]
-/
theorem modEq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (digits b' n).sum [MOD b] := by
  rw [← ofDigits_one]
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  convert! ofDigits_modEq b' b (digits b' n)
  exact h.symm
/-
**Nat.zmodeq_ofDigits_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：zmodeq_ofDigits_digits (b b' : Nat) (c : Int) (h : b' ≡ c [ZMOD b]) (n : N
at) : n ≡ ofDigits c (digits b' n) [ZMOD b]
参数：b b' : Nat；c : Int；h : b' ≡ c [ZMOD b]；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `Nat.coe_ofDigits`：coe_ofDigits (α : Type*) [Semiring α] (b : Nat) (L : L
ist Nat) : ((ofDigits b L : Nat) : α) = ofDigits (b : α) L
· 使用定理 `Nat.ofDigits_zmodeq'`：ofDigits_zmodeq' (b b' : Int) (k : Nat) (h : b ≡ b
' [ZMOD k]) (L : List Nat) : ofDigits b L ≡ ofDigits b' L [ZMOD k]
-/
theorem zmodeq_ofDigits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
    n ≡ ofDigits c (digits b' n) [ZMOD b] := by
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  rw [coe_ofDigits]
  apply ofDigits_zmodeq' _ _ _ h
/-
**Nat.ofDigits_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (L : List ℕ), Nat.ofDigits (-1) L = (List.map (fun n => ↑n) L).alternati
ngSum
参数：L : List ℕ；-1；List.map (fun n => ↑n) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDigits_neg_one :
    ∀ L : List ℕ, ofDigits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
  | [] => rfl
  | [n] => by simp [ofDigits, List.alternatingSum]
  | a :: b :: t => by
    simp only [ofDigits, List.alternatingSum, List.map_cons, ofDigits_neg_one t]
    ring

/-- Explicit computation of the `i`-th digit of `n` in base `b`. -/
/-
**Nat.getD_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：getD_digits (n i : Nat) {b : Nat} (h : 2 <= b) : (digits b n).getD i 0 = n
 / b ^ i % b
参数：n i : Nat；h : 2 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head?_eq_getElem?`：∀ {α : Type u_1} {l : List α}, l.head? = l[0]?
· 使用定理 `Nat.default_eq_zero`：default = 0
· 使用定理 `List.head!_eq_head?_getD`：∀ {α : Type u} [inst : Inhabited α] (l : List 
α), l.head! = l.head?.getD default
· 使用定理 `Nat.head!_digits`：∀ {b n : ℕ}, b ≠ 1 → (b.digits n).head! = n % b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用引理 `Nat.digits_of_two_le_of_pos`：digits_of_two_le_of_pos {b : Nat} (hb : 2 <
= b) (hn : 0 < n) : Nat.digits b n = n % b :: Nat.digits b (n / b)
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
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit computation of the `i`-th digit of `n` in base `b`.
-/
theorem getD_digits (n i : ℕ) {b : ℕ} (h : 2 ≤ b) : (digits b n).getD i 0 = n / b ^ i % b := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' h
  clear h
  rw [List.getD_eq_getElem?_getD]
  induction n using Nat.caseStrongRecOn generalizing i with
  | zero => simp
  | ind n IH =>
    rcases i with _ | i
    · rw [← List.head?_eq_getElem?, ← default_eq_zero, ← List.head!_eq_head?_getD,
        head!_digits (by grind)]
      simp
    · simp [IH _ (le_of_lt_succ (div_lt_self' n b)), pow_succ', Nat.div_div_eq_div_mul]

/-! ### Bijection -/

open List

/--
The list of digits of `n` in base `b` with some `0`'s appended so that its length is equal to `l`
if it is `< l`. This is an inverse function of `Nat.ofDigits` for `n < b ^ l`,
see `Nat.setInvOn_digitsAppend_ofDigits`.
If `n ≥ b ^ l`, then the list of digits of `n` in base `b` is of length at least `l` and
this function just return `b.digits n`.
-/
/-
**Nat.digitsAppend** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：digitsAppend (b l n : Nat) : List Nat
参数：b l n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list of digits of `n` in base `b` with some `0`'s appended so that its lengt
h is equal to `l`
if it is `< l`. This is an inverse function of `Nat.ofDigits` for `n < b ^ l`,
see `Nat.setInvOn_digitsAppend_ofDigits`.
If `n ≥ b ^ l`, then the list of digits of `n` in base `b` is of length at least
 `l` and
this function just return `b.digits n`.
-/
def digitsAppend (b l n : ℕ) : List ℕ :=
  b.digits n ++ replicate (l - (b.digits n).length) 0
/-
**Nat.length_digitsAppend** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：length_digitsAppend {b : Nat} (hb : 1 < b) (l : Nat) (hn : n < b ^ l) : (d
igitsAppend b l n).length = l
参数：hb : 1 < b；l : Nat；hn : n < b ^ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Nat.Digits.Lemmas.0.Nat.digitsAppend.eq_1`：∀ (b l 
n : ℕ), b.digitsAppend l n = b.digits n ++ List.replicate (l - (b.digits n).leng
th) 0
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.digits_length_le_iff`：digits_length_le_iff {b k : Nat} (hb : 1 < b) 
(n : Nat) : (b.digits n).length <= k ↔ n < b ^ k
-/
theorem length_digitsAppend {b : ℕ} (hb : 1 < b) (l : ℕ) (hn : n < b ^ l) :
    (digitsAppend b l n).length = l := by
  rw [digitsAppend, length_append, length_replicate, Nat.add_sub_cancel']
  rwa [digits_length_le_iff hb]
/-
**Nat.lt_of_mem_digitsAppend** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_mem_digitsAppend {b : Nat} (hb : 1 < b) (l i : Nat) (hi : i in digit
sAppend b l n) : i < b
参数：hb : 1 < b；l i : Nat；hi : i in digitsAppend b l n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.replica
te n a ↔ n ≠ 0 ∧ b = a
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
· 使用定理 `_private.Mathlib.Data.Nat.Digits.Lemmas.0.Nat.digitsAppend.eq_1`：∀ (b l 
n : ℕ), b.digitsAppend l n = b.digits n ++ List.replicate (l - (b.digits n).leng
th) 0
· 使用定理 `Nat.digits_lt_base`：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in
 digits b m) : d < b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 57 条，此处仅展示前 30 条）
-/
theorem lt_of_mem_digitsAppend {b : ℕ} (hb : 1 < b) (l i : ℕ)
    (hi : i ∈ digitsAppend b l n) : i < b := by
  rw [digitsAppend, mem_append, mem_replicate] at hi
  obtain hi | ⟨_, rfl⟩ := hi
  · exact digits_lt_base hb hi
  · linarith
/-
**Nat.mapsTo_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : Set.MapsTo (ofDigits b)
 {L : List Nat | L.length = l ∧ forall x in L, x < b} {n | n < b ^ l}
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofDigits_lt_base_pow_length`：ofDigits_lt_base_pow_length {b : Nat} {
l : List Nat} (hb : 1 < b) (hl : forall x in l, x < b) : ofDigits b l < b ^ l.le
ngth
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mapsTo_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.MapsTo (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} {n | n < b ^ l} :=
  fun _ h ↦ Set.mem_ofPred.mpr h.1 ▸ Nat.ofDigits_lt_base_pow_length hb h.2
/-
**Nat.mapsTo_digitsAppend** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mapsTo_digitsAppend {b : Nat} (hb : 1 < b) (l : Nat) : Set.MapsTo (digitsA
ppend b l) {n | n < b ^ l} {L : List Nat | L.length = l ∧ forall x in L, x < b}
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.length_digitsAppend`：length_digitsAppend {b : Nat} (hb : 1 < b) (l :
 Nat) (hn : n < b ^ l) : (digitsAppend b l n).length = l
· 使用定理 `Nat.lt_of_mem_digitsAppend`：lt_of_mem_digitsAppend {b : Nat} (hb : 1 < b
) (l i : Nat) (hi : i in digitsAppend b l n) : i < b
-/
theorem mapsTo_digitsAppend {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.MapsTo (digitsAppend b l) {n | n < b ^ l} {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
  fun _ h ↦ ⟨by rw [length_digitsAppend hb _ h], fun _ hi ↦ lt_of_mem_digitsAppend hb l _ hi⟩
/-
**Nat.injOn_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：injOn_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : Set.InjOn (ofDigits b) {
L : List Nat | L.length = l ∧ forall x in L, x < b}
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ofDigits_inj_of_len_eq`：ofDigits_inj_of_len_eq {b : Nat} (hb : 1 < b
) {L1 L2 : List Nat} (len : L1.length = L2.length) (w1 : forall l in L1, l < b) 
(w2 : forall l i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem injOn_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.InjOn (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
  fun _ _ _ _ h ↦ ofDigits_inj_of_len_eq hb (by simp_all) (by simp_all) (by simp_all) h
/-
**Nat.setInvOn_digitsAppend_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：setInvOn_digitsAppend_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : Set.InvO
n (digitsAppend b l) (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, 
x < b} {n | n < b ^ l}
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.injOn_ofDigits`：injOn_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : Se
t.InjOn (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.length_digitsAppend`：length_digitsAppend {b : Nat} (hb : 1 < b) (l :
 Nat) (hn : n < b ^ l) : (digitsAppend b l n).length = l
· 使用定理 `Nat.mapsTo_ofDigits`：mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : 
Set.MapsTo (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n 
| n < b ^…
· 使用定理 `Nat.lt_of_mem_digitsAppend`：lt_of_mem_digitsAppend {b : Nat} (hb : 1 < b
) (l i : Nat) (hi : i in digitsAppend b l n) : i < b
· 使用定理 `_private.Mathlib.Data.Nat.Digits.Lemmas.0.Nat.digitsAppend.eq_1`：∀ (b l 
n : ℕ), b.digitsAppend l n = b.digits n ++ List.replicate (l - (b.digits n).leng
th) 0
· 使用定理 `Nat.ofDigits_append_replicate_zero`：ofDigits_append_replicate_zero {b k 
: Nat} (l : List Nat) : ofDigits b (l ++ List.replicate k 0) = ofDigits b l
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
-/
theorem setInvOn_digitsAppend_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.InvOn (digitsAppend b l) (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}
      {n | n < b ^ l} := by
  refine ⟨fun L hL ↦ ?_, fun _ _ ↦ by rw [digitsAppend, ofDigits_append_replicate_zero,
    ofDigits_digits]⟩
  refine (injOn_ofDigits hb l) ⟨?_, ?_⟩ hL
    (by rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits])
  · rw [length_digitsAppend hb _ (mapsTo_ofDigits hb _ hL)]
  · exact fun x hx ↦ lt_of_mem_digitsAppend hb l x hx

/--
The map `L ↦ Nat.ofDigits b L` is bijection between the set of lists of natural integers of
length `l` with coefficients `< b` to the set of natural integers `< b ^ l`.
-/
/-
**Nat.bijOn_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bijOn_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : Set.BijOn (ofDigits b) {
L : List Nat | L.length = l ∧ forall x in L, x < b} {n | n < b ^ l}
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `Nat.setInvOn_digitsAppend_ofDigits`：setInvOn_digitsAppend_ofDigits {b : 
Nat} (hb : 1 < b) (l : Nat) : Set.InvOn (digitsAppend b l) (ofDigits b) {L : Lis
t Nat | L.length = l ∧ f…
· 使用定理 `Nat.mapsTo_ofDigits`：mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : 
Set.MapsTo (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n 
| n < b ^…
· 使用定理 `Nat.mapsTo_digitsAppend`：mapsTo_digitsAppend {b : Nat} (hb : 1 < b) (l :
 Nat) : Set.MapsTo (digitsAppend b l) {n | n < b ^ l} {L : List Nat | L.length =
 l ∧ forall x…

--- 原说明 ---
The map `L ↦ Nat.ofDigits b L` is bijection between the set of lists of natural 
integers of
length `l` with coefficients `< b` to the set of natural integers `< b ^ l`.
-/
theorem bijOn_ofDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (ofDigits b) {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} {n | n < b ^ l} :=
  (setInvOn_digitsAppend_ofDigits hb l).bijOn (mapsTo_ofDigits hb l) (mapsTo_digitsAppend hb l)

/--
The map `n ↦ Nat.digitsAppend b L` is bijection between the set of natural integers `< b ^ l`
to the set of lists of natural integers of length `l` with coefficients `< b` to .
-/
/-
**Nat.bijOn_digitsAppend** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bijOn_digitsAppend {b : Nat} (hb : 1 < b) (l : Nat) : Set.BijOn (digitsApp
end b l) {n | n < b ^ l} {L : List Nat | L.length = l ∧ forall x in L, x < b}
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} 
{f : α → β} {g : β → α},   Set.InvOn f g t s → Set.BijOn f s t → Set.BijOn g t s
· 使用定理 `Set.InvOn.symm`：symm (h : InvOn f' f s t) : InvOn f f' t s
· 使用定理 `Nat.setInvOn_digitsAppend_ofDigits`：setInvOn_digitsAppend_ofDigits {b : 
Nat} (hb : 1 < b) (l : Nat) : Set.InvOn (digitsAppend b l) (ofDigits b) {L : Lis
t Nat | L.length = l ∧ f…
· 使用定理 `Nat.bijOn_ofDigits`：bijOn_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : Se
t.BijOn (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n | n
 < b ^ l…

--- 原说明 ---
The map `n ↦ Nat.digitsAppend b L` is bijection between the set of natural integ
ers `< b ^ l`
to the set of lists of natural integers of length `l` with coefficients `< b` to
 .
-/
theorem bijOn_digitsAppend {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (digitsAppend b l) {n | n < b ^ l} {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
  (bijOn_ofDigits hb l).symm (setInvOn_digitsAppend_ofDigits hb l).symm
/-
**Nat.sum_digits_ofDigits_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_digits_ofDigits_eq_sum {b : Nat} (hb : 1 < b) {l : Nat} {L : List Nat}
 (hL : L in {L : List Nat | L.length = l ∧ forall x in L, x < b}) : (b.digits (o
fDigits b L)).sum = L.sum
参数：hb : 1 < b；hL : L in {L : List Nat | L.length = l ∧ forall x in L, x < b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.setInvOn_digitsAppend_ofDigits`：setInvOn_digitsAppend_ofDigits {b : 
Nat} (hb : 1 < b) (l : Nat) : Set.InvOn (digitsAppend b l) (ofDigits b) {L : Lis
t Nat | L.length = l ∧ f…
· 使用定理 `_private.Mathlib.Data.Nat.Digits.Lemmas.0.Nat.digitsAppend.eq_1`：∀ (b l 
n : ℕ), b.digitsAppend l n = b.digits n ++ List.replicate (l - (b.digits n).leng
th) 0
· 使用定理 `List.sum_append_nat`：∀ {l₁ l₂ : List ℕ}, (l₁ ++ l₂).sum = l₁.sum + l₂.su
m
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem sum_digits_ofDigits_eq_sum {b : ℕ} (hb : 1 < b) {l : ℕ} {L : List ℕ}
    (hL : L ∈ {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}) :
    (b.digits (ofDigits b L)).sum = L.sum := by
  nth_rewrite 2 [← (setInvOn_digitsAppend_ofDigits hb l).1 hL]
  rw [digitsAppend, List.sum_append_nat, List.sum_replicate, nsmul_zero, add_zero]

end Nat

namespace List

open Nat

/--
The set of lists of natural integers of length `l` with coefficients `< b` as a `Finset`.
This can be seen as the set of lists of length `l` of the digits in base `b` of
the integers `< b ^ l`.
Having this set as a `Finset` can be helpful for some proofs.
-/
/-
**List.fixedLengthDigits** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：fixedLengthDigits {b : Nat} (hb : 1 < b) (l : Nat) : Finset (List Nat)
参数：hb : 1 < b；l : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mapsTo_ofDigits`：mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : 
Set.MapsTo (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n 
| n < b ^…

--- 原说明 ---
The set of lists of natural integers of length `l` with coefficients `< b` as a 
`Finset`.
This can be seen as the set of lists of length `l` of the digits in base `b` of
the integers `< b ^ l`.
Having this set as a `Finset` can be helpful for some proofs.
-/
noncomputable def fixedLengthDigits {b : ℕ} (hb : 1 < b) (l : ℕ) : Finset (List ℕ) := by
  have : Fintype {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b} :=
    Fintype.ofInjective (Set.MapsTo.restrict _ _ _ (mapsTo_ofDigits hb l))
      <| (Set.MapsTo.restrict_inj (mapsTo_ofDigits hb l)).mpr <| injOn_ofDigits hb l
  exact {L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}.toFinset
/-
**List.mem_fixedLengthDigits_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_fixedLengthDigits_iff {b : Nat} (hb : 1 < b) {l : Nat} {L : List Nat} 
: L in fixedLengthDigits hb l ↔ L.length = l ∧ forall x in L, x < b
参数：hb : 1 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mapsTo_ofDigits`：mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : 
Set.MapsTo (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n 
| n < b ^…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_fixedLengthDigits_iff {b : ℕ} (hb : 1 < b) {l : ℕ} {L : List ℕ} :
    L ∈ fixedLengthDigits hb l ↔ L.length = l ∧ ∀ x ∈ L, x < b := by
  simp [fixedLengthDigits]

/--
The bijection `Nat.bijOn_ofDigits` stated as a bijection between `Finset`.
This spelling can be helpful for some proofs.
-/
/-
**List._root_.Nat.bijOn_ofDigits'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Nat.bijOn_ofDigits` stated as a bijection between `Finset`.
This spelling can be helpful for some proofs.
-/
theorem _root_.Nat.bijOn_ofDigits' {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (ofDigits b) (fixedLengthDigits hb l) (Finset.range (b ^ l)) := by
  rw [fixedLengthDigits, Set.coe_toFinset]
  convert! bijOn_ofDigits hb l
  ext; simp

/--
The bijection `Nat.bijOn_digitsAppend` stated as a bijection between `Finset`.
This spelling can be helpful for some proofs.
-/
/-
**List._root_.Nat.bijOn_digitsAppend'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Nat.bijOn_digitsAppend` stated as a bijection between `Finset`.
This spelling can be helpful for some proofs.
-/
theorem _root_.Nat.bijOn_digitsAppend' {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.BijOn (digitsAppend b l) (Finset.range (b ^ l)) (fixedLengthDigits hb l) := by
  rw [fixedLengthDigits, Set.coe_toFinset]
  convert! bijOn_digitsAppend hb l
  ext; simp

@[simp]
/-
**List.fixedLengthDigits_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：fixedLengthDigits_zero {b : Nat} (hb : 1 < b) : fixedLengthDigits hb 0 = {
[]}
参数：hb : 1 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mapsTo_ofDigits`：mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) : 
Set.MapsTo (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n 
| n < b ^…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem fixedLengthDigits_zero {b : ℕ} (hb : 1 < b) :
    fixedLengthDigits hb 0 = {[]} := by
  ext
  simp [fixedLengthDigits]
  grind

@[simp]
/-
**List.fixedLengthDigits_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：fixedLengthDigits_one {b : Nat} (hb : 1 < b) : fixedLengthDigits hb 1 = Fi
nset.image (fun x : Nat => [x]) (Finset.range b)
参数：hb : 1 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_fixedLengthDigits_iff`：mem_fixedLengthDigits_iff {b : Nat} (hb 
: 1 < b) {l : Nat} {L : List Nat} : L in fixedLengthDigits hb l ↔ L.length = l ∧
 forall x in L, x < …
· 使用定理 `List.length_eq_one_iff`：∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ 
a, l = [a]
-/
theorem fixedLengthDigits_one {b : ℕ} (hb : 1 < b) :
    fixedLengthDigits hb 1 = Finset.image (fun x : ℕ ↦ [x]) (Finset.range b) := by
  ext
  rw [mem_fixedLengthDigits_iff, List.length_eq_one_iff]
  grind
/-
**List.card_fixedLengthDigits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：card_fixedLengthDigits {b : Nat} (hb : 1 < b) (l : Nat) : Finset.card (fix
edLengthDigits hb l) = b ^ l
参数：hb : 1 < b；l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.BijOn.finsetCard_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β} (e : α → β), Set.BijOn e ↑s ↑t → s.card = t.card
· 使用定理 `Nat.bijOn_ofDigits'`：∀ {b : ℕ} (hb : 1 < b) (l : ℕ), Set.BijOn (Nat.ofDi
gits b) ↑(List.fixedLengthDigits hb l) ↑(Finset.range (b ^ l))
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem card_fixedLengthDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Finset.card (fixedLengthDigits hb l) = b ^ l := by
  rw [Set.BijOn.finsetCard_eq (ofDigits b) (bijOn_ofDigits' hb l), Finset.card_range]

/--
The `Finset` of lists whose head is a fixed integer `d` and tail is a list
in `List.fixedLengthDigits b l`.
-/
/-
**List.consFixedLengthDigits** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：consFixedLengthDigits {b : Nat} (hb : 1 < b) (l d : Nat) : Finset (List Na
t)
参数：hb : 1 < b；l d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of lists whose head is a fixed integer `d` and tail is a list
in `List.fixedLengthDigits b l`.
-/
noncomputable def consFixedLengthDigits {b : ℕ} (hb : 1 < b) (l d : ℕ) :
    Finset (List ℕ) := Finset.image (fun L ↦ d :: L) (fixedLengthDigits hb l)
/-
**List.ne_empty_of_mem_consFixedLengthDigits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ne_empty_of_mem_consFixedLengthDigits {b : Nat} (hb : 1 < b) {l d : Nat} {
L : List Nat} (hL : L in consFixedLengthDigits hb l d) : L != []
参数：hb : 1 < b；hL : L in consFixedLengthDigits hb l d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem ne_empty_of_mem_consFixedLengthDigits {b : ℕ} (hb : 1 < b) {l d : ℕ} {L : List ℕ}
    (hL : L ∈ consFixedLengthDigits hb l d) : L ≠ [] := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  exact cons_ne_nil d _
/-
**List.consFixedLengthDigits_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：consFixedLengthDigits_head {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Na
t} (hL : L in consFixedLengthDigits hb l d) : List.head L (ne_empty_of_mem_consF
ixedLengthDigits hb hL) = d
参数：hb : 1 < b；hL : L in consFixedLengthDigits hb l d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.ne_empty_of_mem_consFixedLengthDigits`：ne_empty_of_mem_consFixedLen
gthDigits {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Nat} (hL : L in consFixed
LengthDigits hb l d) : L != []
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head_cons`：∀ {α : Type u} {a : α} {l : List α} {h : a :: l ≠ []}, (
a :: l).head h = a
-/
theorem consFixedLengthDigits_head {b : ℕ} (hb : 1 < b) {l d : ℕ} {L : List ℕ}
    (hL : L ∈ consFixedLengthDigits hb l d) :
    List.head L (ne_empty_of_mem_consFixedLengthDigits hb hL) = d := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  rw [head_cons]

/--
If `L` is a list in `List.fixedLengthDigits b l` and `d` is an integer `< b`, then
`d :: L` is a list in `List.fixedLengthDigits b (l + 1).`
-/
/-
**List.cons_mem_fixedLengthDigits_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_mem_fixedLengthDigits_succ {b : Nat} (hb : 1 < b) (l d : Nat) (hd : d
 < b) {L : List Nat} (hL : L in fixedLengthDigits hb l) : d :: L in fixedLengthD
igits hb (l + 1)
参数：hb : 1 < b；l d : Nat；hd : d < b；hL : L in fixedLengthDigits hb l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_fixedLengthDigits_iff`：mem_fixedLengthDigits_iff {b : Nat} (hb 
: 1 < b) {l : Nat} {L : List Nat} : L in fixedLengthDigits hb l ↔ L.length = l ∧
 forall x in L, x < …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `L` is a list in `List.fixedLengthDigits b l` and `d` is an integer `< b`, th
en
`d :: L` is a list in `List.fixedLengthDigits b (l + 1).`
-/
theorem cons_mem_fixedLengthDigits_succ {b : ℕ} (hb : 1 < b) (l d : ℕ) (hd : d < b) {L : List ℕ}
    (hL : L ∈ fixedLengthDigits hb l) :
    d :: L ∈ fixedLengthDigits hb (l + 1) := by
  refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
  · simpa using ((mem_fixedLengthDigits_iff hb).mp hL).1
  · intro x hx
    obtain rfl | hx := mem_cons.mp hx
    · exact hd
    · exact ((mem_fixedLengthDigits_iff hb).mp hL).2 _ hx
/-
**List.pairwiseDisjoint_consFixedLengthDigits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwiseDisjoint_consFixedLengthDigits {b : Nat} (hb : 1 < b) (l : Nat) : 
Set.PairwiseDisjoint (Finset.range b : Set Nat) (fun d => consFixedLengthDigits 
hb l d)
参数：hb : 1 < b；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.pairwiseDisjoint_iff`：pairwiseDisjoint_iff {ι : Type*} {s : Set ι
} {f : ι -> Finset α} : s.PairwiseDisjoint f ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄,
 j in s -> (f i i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.ne_empty_of_mem_consFixedLengthDigits`：ne_empty_of_mem_consFixedLen
gthDigits {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Nat} (hL : L in consFixed
LengthDigits hb l d) : L != []
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.consFixedLengthDigits_head`：consFixedLengthDigits_head {b : Nat} (h
b : 1 < b) {l d : Nat} {L : List Nat} (hL : L in consFixedLengthDigits hb l d) :
 List.head L (ne_empt…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem pairwiseDisjoint_consFixedLengthDigits {b : ℕ} (hb : 1 < b) (l : ℕ) :
    Set.PairwiseDisjoint (Finset.range b : Set ℕ) (fun d ↦ consFixedLengthDigits hb l d) := by
  refine Finset.pairwiseDisjoint_iff.mpr fun i _ j _ ⟨L, hL⟩ ↦ ?_
  rw [Finset.mem_inter] at hL
  exact (consFixedLengthDigits_head hb hL.1).symm.trans (consFixedLengthDigits_head hb hL.2)

/--
The set `List.fixedLengthDigits b (l + 1)` is the disjoint union of the sets
`List.consFixedLengthDigits b l d` where `d` ranges through the natural integers `< d`.
-/
/-
**List.fixedLengthDigits_succ_eq_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：fixedLengthDigits_succ_eq_disjiUnion {b : Nat} (hb : 1 < b) (l : Nat) : fi
xedLengthDigits hb (l + 1) = Finset.disjiUnion (Finset.range b) (consFixedLength
Digits hb l) (pairwiseDisjoint_consFixedLengthDigits hb l)
参数：hb : 1 < b；l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `List.pairwiseDisjoint_consFixedLengthDigits`：pairwiseDisjoint_consFixedL
engthDigits {b : Nat} (hb : 1 < b) (l : Nat) : Set.PairwiseDisjoint (Finset.rang
e b : Set Nat) (fun d => consFixe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_fixedLengthDigits_iff`：mem_fixedLengthDigits_iff {b : Nat} (hb 
: 1 < b) {l : Nat} {L : List Nat} : L in fixedLengthDigits hb l ↔ L.length = l ∧
 forall x in L, x < …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.length_tail`：∀ {α : Type u_1} {l : List α}, l.tail.length = l.lengt
h - 1
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `List.cons_head_tail`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head 
h :: l.tail = l
· 使用定理 `List.cons_mem_fixedLengthDigits_succ`：cons_mem_fixedLengthDigits_succ {b
 : Nat} (hb : 1 < b) (l d : Nat) (hd : d < b) {L : List Nat} (hL : L in fixedLen
gthDigits hb l) : d :: L i…

--- 原说明 ---
The set `List.fixedLengthDigits b (l + 1)` is the disjoint union of the sets
`List.consFixedLengthDigits b l d` where `d` ranges through the natural integers
 `< d`.
-/
theorem fixedLengthDigits_succ_eq_disjiUnion {b : ℕ} (hb : 1 < b) (l : ℕ) :
    fixedLengthDigits hb (l + 1) = Finset.disjiUnion (Finset.range b)
      (consFixedLengthDigits hb l) (pairwiseDisjoint_consFixedLengthDigits hb l) := by
  ext L
  simp_rw [Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_range,
    consFixedLengthDigits, Finset.mem_image]
  refine ⟨fun hL ↦ ?_, ?_⟩
  · have hL₁ : L.length = l + 1 := ((mem_fixedLengthDigits_iff hb).mp hL).1
    have hL₂ : ∀ x ∈ L, x < b := ((mem_fixedLengthDigits_iff hb).mp hL).2
    have hL₃ : L ≠ [] := by simp [ne_nil_iff_length_pos, hL₁]
    refine ⟨L.head hL₃, hL₂ _ (L.head_mem hL₃), L.tail, ?_, cons_head_tail hL₃⟩
    refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
    · rw [length_tail, hL₁, Nat.add_sub_cancel_right]
    · exact fun x hx ↦ hL₂ _ <| mem_of_mem_tail hx
  · rintro ⟨d, hd₁, T, hT, rfl⟩
    exact cons_mem_fixedLengthDigits_succ hb l d hd₁ hT
/-
**List.sum_fixedLengthDigits_sum** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_fixedLengthDigits_sum {b : Nat} (hb : 1 < b) (l : Nat) : ∑ L in fixedL
engthDigits hb l, L.sum = l * b ^ (l - 1) * b.choose 2
参数：hb : 1 < b；l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `List.fixedLengthDigits_zero`：fixedLengthDigits_zero {b : Nat} (hb : 1 < 
b) : fixedLengthDigits hb 0 = {[]}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.fixedLengthDigits.congr_simp`：∀ {b b_1 : ℕ} (e_b : b = b_1) (hb : 1
 < b) (l l_1 : ℕ),   l = l_1 → List.fixedLengthDigits hb l = List.fixedLengthDig
its ⋯ l_1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.fixedLengthDigits_one`：fixedLengthDigits_one {b : Nat} (hb : 1 < b)
 : fixedLengthDigits hb 1 = Finset.image (fun x : Nat => [x]) (Finset.range b)
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_range_id`：sum_range_id (n : Nat) : ∑ i in range n, i = n * (n
 - 1) / 2
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.choose_two_right`：choose_two_right (n : Nat) : choose n 2 = n * (n -
 1) / 2
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `List.pairwiseDisjoint_consFixedLengthDigits`：pairwiseDisjoint_consFixedL
engthDigits {b : Nat} (hb : 1 < b) (l : Nat) : Set.PairwiseDisjoint (Finset.rang
e b : Set Nat) (fun d => consFixe…
（共 73 条，此处仅展示前 30 条）
-/
theorem sum_fixedLengthDigits_sum {b : ℕ} (hb : 1 < b) (l : ℕ) :
    ∑ L ∈ fixedLengthDigits hb l, L.sum = l * b ^ (l - 1) * b.choose 2 := by
  induction l with
  | zero => simp
  | succ l hr =>
      by_cases hl : l = 0
      · simp [hl, fixedLengthDigits_one, Finset.sum_range_id, choose_two_right]
      rw [fixedLengthDigits_succ_eq_disjiUnion, Finset.sum_disjiUnion]
      simp only [consFixedLengthDigits, cons.injEq, true_and, implies_true, Set.injOn_of_eq_iff_eq,
        Finset.sum_image, sum_cons]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_nsmul, Finset.sum_range_id, hr,
        nsmul_eq_mul, Finset.card_range, add_tsub_cancel_right, cast_id, card_fixedLengthDigits,
        choose_two_right]
      rw [show b ^ l = b * b ^ (l - 1) by rw [← Nat.pow_succ', Nat.sub_one, Nat.succ_pred hl]]
      ring

end List

/--
The formula for the sum of the sum of the digits in base `b` over the natural integers `< b ^ l`.
-/
/-
**Nat.sum_sum_digits_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.sum_sum_digits_eq {b : Nat} (hb : 1 < b) (l : Nat) : ∑ x in Finset.ran
ge (b ^ l), (b.digits x).sum = l * b ^ (l - 1) * b.choose 2
参数：hb : 1 < b；l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sum_fixedLengthDigits_sum`：sum_fixedLengthDigits_sum {b : Nat} (hb 
: 1 < b) (l : Nat) : ∑ L in fixedLengthDigits hb l, L.sum = l * b ^ (l - 1) * b.
choose 2
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.bijOn_ofDigits'`：∀ {b : ℕ} (hb : 1 < b) (l : ℕ), Set.BijOn (Nat.ofDi
gits b) ↑(List.fixedLengthDigits hb l) ↑(Finset.range (b ^ l))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.sum_digits_ofDigits_eq_sum`：sum_digits_ofDigits_eq_sum {b : Nat} (hb
 : 1 < b) {l : Nat} {L : List Nat} (hL : L in {L : List Nat | L.length = l ∧ for
all x in L, x < b}) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_fixedLengthDigits_iff`：mem_fixedLengthDigits_iff {b : Nat} (hb 
: 1 < b) {l : Nat} {L : List Nat} : L in fixedLengthDigits hb l ↔ L.length = l ∧
 forall x in L, x < …

--- 原说明 ---
The formula for the sum of the sum of the digits in base `b` over the natural in
tegers `< b ^ l`.
-/
theorem Nat.sum_sum_digits_eq {b : ℕ} (hb : 1 < b) (l : ℕ) :
    ∑ x ∈ Finset.range (b ^ l), (b.digits x).sum = l * b ^ (l - 1) * b.choose 2 := by
  rw [← List.sum_fixedLengthDigits_sum hb]
  refine (Finset.sum_nbij (ofDigits b) (by exact (bijOn_ofDigits' hb l).1)
    (bijOn_ofDigits' hb l).2.1 (bijOn_ofDigits' hb l).2.2 fun L hL ↦ ?_).symm
  rw [sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)]
