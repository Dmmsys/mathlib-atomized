/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Sums of two squares

Fermat's theorem on the sum of two squares. Every prime `p` congruent to 1 mod 4 is the
sum of two squares; see `Nat.Prime.sq_add_sq` (which has the weaker assumption `p % 4 ≠ 3`).

We also give the result that characterizes the (positive) natural numbers that are sums
of two squares as those numbers `n` such that for every prime `q` congruent to 3 mod 4, the
exponent of the largest power of `q` dividing `n` is even; see `Nat.eq_sq_add_sq_iff`.

There is an alternative characterization as the numbers of the form `a^2 * b`, where `b` is a
natural number such that `-1` is a square modulo `b`; see `Nat.eq_sq_add_sq_iff_eq_sq_mul`.
-/

public section


section Fermat

open GaussianInt

/-- **Fermat's theorem on the sum of two squares**. Every prime not congruent to 3 mod 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**. -/
/-
**Nat.Prime.sq_add_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Prime.sq_add_sq {p : Nat} [Fact p.Prime] (hp : p % 4 != 3) : exists a 
b : Nat, a ^ 2 + b ^ 2 = p
参数：hp : p % 4 != 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible`：sq_add_sq_of_nat_
prime_of_not_irreducible (p : Nat) [hp : Fact p.Prime] (hpi : ¬Irreducible (p : 
Int[i])) : exists a b, a ^ 2 + b ^ 2 = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime`：prime_iff_mod_four
_eq_three_of_nat_prime (p : Nat) [Fact p.Prime] : Prime (p : Int[i]) ↔ p % 4 = 3

--- 原说明 ---
**Fermat's theorem on the sum of two squares**. Every prime not congruent to 3 m
od 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**.
-/
theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]

end Fermat

/-!
### Generalities on sums of two squares
-/


section General

/-- The set of sums of two squares is closed under multiplication in any commutative ring.
See also `sq_add_sq_mul_sq_add_sq`. -/
/-
**sq_add_sq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sq_add_sq_mul {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2) 
(hb : b = u ^ 2 + v ^ 2) : exists r s : R, a * b = r ^ 2 + s ^ 2
参数：ha : a = x ^ 2 + y ^ 2；hb : b = u ^ 2 + v ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The set of sums of two squares is closed under multiplication in any commutative
 ring.
See also `sq_add_sq_mul_sq_add_sq`.
-/
theorem sq_add_sq_mul {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
    (hb : b = u ^ 2 + v ^ 2) : ∃ r s : R, a * b = r ^ 2 + s ^ 2 :=
  ⟨x * u - y * v, x * v + y * u, by rw [ha, hb]; ring⟩

/-- The set of natural numbers that are sums of two squares is closed under multiplication. -/
/-
**Nat.sq_add_sq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.sq_add_sq_mul {a b x y u v : Nat} (ha : a = x ^ 2 + y ^ 2) (hb : b = u
 ^ 2 + v ^ 2) : exists r s : Nat, a * b = r ^ 2 + s ^ 2
参数：ha : a = x ^ 2 + y ^ 2；hb : b = u ^ 2 + v ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `sq_add_sq_mul`：sq_add_sq_mul {R} [CommRing R] {a b x y u v : R} (ha : a 
= x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) : exists r s : R, a * b = r ^ 2 + s ^ 
2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2

--- 原说明 ---
The set of natural numbers that are sums of two squares is closed under multipli
cation.
-/
theorem Nat.sq_add_sq_mul {a b x y u v : ℕ} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
    ∃ r s : ℕ, a * b = r ^ 2 + s ^ 2 := by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs]

end General

/-!
### Results on when -1 is a square modulo a natural number
-/


section NegOneSquare

-- This could be formulated for a general integer `a` in place of `-1`,
-- but it would not directly specialize to `-1`,
-- because `((-1 : ℤ) : ZMod n)` is not the same as `(-1 : ZMod n)`.
/-- If `-1` is a square modulo `n` and `m` divides `n`, then `-1` is also a square modulo `m`. -/
/-
**ZMod.isSquare_neg_one_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.isSquare_neg_one_of_dvd {m n : Nat} (hd : m ∣ n) (hs : IsSquare (-1 :
 ZMod n)) : IsSquare (-1 : ZMod m)
参数：hd : m ∣ n；hs : IsSquare (-1 : ZMod n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `IsSquare.map`：IsSquare.map {a : α} (f : F) : IsSquare a -> IsSquare (f a
)

--- 原说明 ---
If `-1` is a square modulo `n` and `m` divides `n`, then `-1` is also a square m
odulo `m`.
-/
theorem ZMod.isSquare_neg_one_of_dvd {m n : ℕ} (hd : m ∣ n) (hs : IsSquare (-1 : ZMod n)) :
    IsSquare (-1 : ZMod m) := by
  let f : ZMod n →+* ZMod m := ZMod.castHom hd _
  rw [← map_one f, ← map_neg]
  exact hs.map f

/-- If `-1` is a square modulo coprime natural numbers `m` and `n`, then `-1` is also
a square modulo `m*n`. -/
/-
**ZMod.isSquare_neg_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.isSquare_neg_one_mul {m n : Nat} (hc : m.Coprime n) (hm : IsSquare (-
1 : ZMod m)) (hn : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod (m * n))
参数：hc : m.Coprime n；hm : IsSquare (-1 : ZMod m)；hn : IsSquare (-1 : ZMod n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.map_neg_one`：map_neg_one : f (-1) = -1
· 使用引理 `IsSquare.map`：IsSquare.map {a : α} (f : F) : IsSquare a -> IsSquare (f a
)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
If `-1` is a square modulo coprime natural numbers `m` and `n`, then `-1` is als
o
a square modulo `m*n`.
-/
theorem ZMod.isSquare_neg_one_mul {m n : ℕ} (hc : m.Coprime n) (hm : IsSquare (-1 : ZMod m))
    (hn : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod (m * n)) := by
  have : IsSquare (-1 : ZMod m × ZMod n) := by
    rw [show (-1 : ZMod m × ZMod n) = ((-1 : ZMod m), (-1 : ZMod n)) from rfl]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    rw [hx, hy]
    exact ⟨(x, y), rfl⟩
  simpa only [RingEquiv.map_neg_one] using this.map (ZMod.chineseRemainder hc).symm

/-- If `p` is a prime factor of `n` such that `-1` is a square modulo `n`, then `p % 4 ≠ 3`. -/
/-
**Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one {p n : Nat} 
(hp : p in n.primeFactors) (hs : IsSquare (-1 : ZMod n)) : p % 4 != 3
参数：hp : p in n.primeFactors；hs : IsSquare (-1 : ZMod n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.isSquare_neg_one_of_dvd`：ZMod.isSquare_neg_one_of_dvd {m n : Nat} (
hd : m ∣ n) (hs : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod m)
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'`：mod_four_ne_three_of_sq_eq_neg_
sq' {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 = -y ^ 2) : p % 4 != 3
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a prime factor of `n` such that `-1` is a square modulo `n`, then `p %
 4 ≠ 3`.
-/
theorem Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one {p n : ℕ}
    (hp : p ∈ n.primeFactors) (hs : IsSquare (-1 : ZMod n)) : p % 4 ≠ 3 := by
  obtain ⟨y, h⟩ := ZMod.isSquare_neg_one_of_dvd (Nat.dvd_of_mem_primeFactors hp) hs
  rw [← sq, eq_comm, show (-1 : ZMod p) = -1 ^ 2 by ring] at h
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h

/-- If `n` is a squarefree natural number, then `-1` is a square modulo `n` if and only if
`n` does not have a prime factor `q` such that `q % 4 = 3`. -/
/-
**ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three {n : N
at} (hn : Squarefree n) : IsSquare (-1 : ZMod n) ↔ forall q in n.primeFactors, q
 % 4 != 3
参数：hn : Squarefree n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`：Nat.mod_f
our_ne_three_of_mem_primeFactors_of_isSquare_neg_one {p n : Nat} (hp : p in n.pr
imeFactors) (hs : IsSquare (-1 : ZMod n)) : p % 4 !…
· 使用定理 `induction_on_primes`：∀ {motive : ℕ → Prop},   motive 0 → motive 1 → (∀ (
p a : ℕ), Nat.Prime p → motive a → motive (p * a)) → ∀ (n : ℕ), motive n
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.dvd_iff_not_coprime`：∀ {p n : ℕ}, Nat.Prime p → (p ∣ n ↔ ¬p.Co
prime n)
· 使用定理 `ZMod.exists_sq_eq_neg_one_iff`：exists_sq_eq_neg_one_iff : IsSquare (-1 :
 ZMod p) ↔ p % 4 != 3
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `ZMod.isSquare_neg_one_mul`：ZMod.isSquare_neg_one_mul {m n : Nat} (hc : m
.Coprime n) (hm : IsSquare (-1 : ZMod m)) (hn : IsSquare (-1 : ZMod n)) : IsSqua
re (-1 : ZMod (…
· 使用定理 `Squarefree.of_mul_right`：Squarefree.of_mul_right [CommMonoid R] {m n : R
} (hmn : Squarefree (m * n)) : Squarefree n
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n

--- 原说明 ---
If `n` is a squarefree natural number, then `-1` is a square modulo `n` if and o
nly if
`n` does not have a prime factor `q` such that `q % 4 = 3`.
-/
theorem ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three {n : ℕ}
    (hn : Squarefree n) : IsSquare (-1 : ZMod n) ↔ ∀ q ∈ n.primeFactors, q % 4 ≠ 3 := by
  refine ⟨fun H q hq ↦ Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq H,
    fun H ↦ ?_⟩
  induction n using induction_on_primes with
  | zero => exact False.elim (hn.ne_zero rfl)
  | one => exact ⟨0, by simp only [mul_zero, eq_iff_true_of_subsingleton]⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hcp : p.Coprime n := by
      by_contra hc
      exact hpp.not_isUnit (hn p <| mul_dvd_mul_left p <| hpp.dvd_iff_not_coprime.mpr hc)
    have hp₁ := ZMod.exists_sq_eq_neg_one_iff.mpr <| H _ <|
      Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_mul_right .., Squarefree.ne_zero hn⟩
    exact ZMod.isSquare_neg_one_mul hcp hp₁ <| ih hn.of_mul_right fun q hqp => H q <|
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqp,
          dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hqp) _, Squarefree.ne_zero hn⟩

/-- If `n` is a squarefree natural number, then `-1` is a square modulo `n` if and only if
`n` has no divisor `q` that is `≡ 3 mod 4`. -/
/-
**ZMod.isSquare_neg_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.isSquare_neg_one_iff' {n : Nat} (hn : Squarefree n) : IsSquare (-1 : 
ZMod n) ↔ forall {q : Nat}, q ∣ n -> q % 4 != 3
参数：hn : Squarefree n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three`：ZMo
d.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three {n : Nat} (hn :
 Squarefree n) : IsSquare (-1 : ZMod n) ↔ forall q in n.p…
· 使用定理 `induction_on_primes`：∀ {motive : ℕ → Prop},   motive 0 → motive 1 → (∀ (
p a : ℕ), Nat.Prime p → motive a → motive (p * a)) → ∀ (n : ℕ), motive n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
· 使用定理 `dvd_of_mul_right_dvd`：dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_eq_natCast_iff'`：natCast_eq_natCast_iff' (a b c : Nat) : (a
 : ZMod c) = (b : ZMod c) ↔ a % c = b % c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n

--- 原说明 ---
If `n` is a squarefree natural number, then `-1` is a square modulo `n` if and o
nly if
`n` has no divisor `q` that is `≡ 3 mod 4`.
-/
theorem ZMod.isSquare_neg_one_iff' {n : ℕ} (hn : Squarefree n) :
    IsSquare (-1 : ZMod n) ↔ ∀ {q : ℕ}, q ∣ n → q % 4 ≠ 3 := by
  have help : ∀ a b : ZMod 4, a ≠ 3 → b ≠ 3 → a * b ≠ 3 := by decide
  rw [ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hn]
  refine ⟨?_, fun H q hq => H <| Nat.dvd_of_mem_primeFactors hq⟩
  intro H
  refine @induction_on_primes _ ?_ ?_ (fun p q hp hq hpq => ?_)
  · exact fun _ => by simp
  · exact fun _ => by simp
  · replace hp := H _ <|
      Nat.mem_primeFactors.mpr ⟨hp, dvd_of_mul_right_dvd hpq, Squarefree.ne_zero hn⟩
    replace hq := hq (dvd_of_mul_left_dvd hpq)
    rw [show 3 = 3 % 4 by simp, Ne, ← ZMod.natCast_eq_natCast_iff'] at hp hq ⊢
    rw [Nat.cast_mul]
    exact help p q hp hq

/-!
### Relation to sums of two squares
-/


/-- If `-1` is a square modulo the natural number `n`, then `n` is a sum of two squares. -/
/-
**Nat.eq_sq_add_sq_of_isSquare_mod_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.eq_sq_add_sq_of_isSquare_mod_neg_one {n : Nat} (h : IsSquare (-1 : ZMo
d n)) : exists x y : Nat, n = x ^ 2 + y ^ 2
参数：h : IsSquare (-1 : ZMod n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `induction_on_primes`：∀ {motive : ℕ → Prop},   motive 0 → motive 1 → (∀ (
p a : ℕ), Nat.Prime p → motive a → motive (p * a)) → ∀ (n : ℕ), motive n
· 使用定理 `ZMod.isSquare_neg_one_of_dvd`：ZMod.isSquare_neg_one_of_dvd {m n : Nat} (
hd : m ∣ n) (hs : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod m)
· 使用定理 `Nat.Prime.sq_add_sq`：Nat.Prime.sq_add_sq {p : Nat} [Fact p.Prime] (hp : 
p % 4 != 3) : exists a b : Nat, a ^ 2 + b ^ 2 = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.exists_sq_eq_neg_one_iff`：exists_sq_eq_neg_one_iff : IsSquare (-1 :
 ZMod p) ↔ p % 4 != 3
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.sq_add_sq_mul`：Nat.sq_add_sq_mul {a b x y u v : Nat} (ha : a = x ^ 2
 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) : exists r s : Nat, a * b = r ^ 2 + s ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `-1` is a square modulo the natural number `n`, then `n` is a sum of two squa
res.
-/
theorem Nat.eq_sq_add_sq_of_isSquare_mod_neg_one {n : ℕ} (h : IsSquare (-1 : ZMod n)) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, rfl⟩
  | one => exact ⟨0, 1, rfl⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hp : IsSquare (-1 : ZMod p) := ZMod.isSquare_neg_one_of_dvd ⟨n, rfl⟩ h
    obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq (ZMod.exists_sq_eq_neg_one_iff.mp hp)
    obtain ⟨x, y, hxy⟩ := ih (ZMod.isSquare_neg_one_of_dvd ⟨p, mul_comm _ _⟩ h)
    exact Nat.sq_add_sq_mul huv.symm hxy

/-- If the integer `n` is a sum of two squares of coprime integers,
then `-1` is a square modulo `n`. -/
/-
**ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime {n x y : Int} (h : n = 
x ^ 2 + y ^ 2) (hc : IsCoprime x y) : IsSquare (-1 : ZMod n.natAbs)
参数：h : n = x ^ 2 + y ^ 2；hc : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.pow`：IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y 
^ n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsCoprime.pow_left_iff`：IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime 
(x ^ m) y ↔ IsCoprime x y
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsCoprime.of_add_mul_right_right`：IsCoprime.of_add_mul_right_right (h : 
IsCoprime x (y + z * x)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
If the integer `n` is a sum of two squares of coprime integers,
then `-1` is a square modulo `n`.
-/
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime {n x y : ℤ} (h : n = x ^ 2 + y ^ 2)
    (hc : IsCoprime x y) : IsSquare (-1 : ZMod n.natAbs) := by
  obtain ⟨u, v, huv⟩ : IsCoprime x n := by
    have hc2 : IsCoprime (x ^ 2) (y ^ 2) := hc.pow
    rw [show y ^ 2 = n + -1 * x ^ 2 by lia] at hc2
    exact (IsCoprime.pow_left_iff zero_lt_two).mp hc2.of_add_mul_right_right
  have H : u * y * (u * y) - -1 = n * (-v ^ 2 * n + u ^ 2 + 2 * v) := by
    linear_combination -u ^ 2 * h + (n * v - u * x - 1) * huv
  refine ⟨u * y, ?_⟩
  conv_rhs => tactic => norm_cast
  rw [(by norm_cast : (-1 : ZMod n.natAbs) = (-1 : ℤ))]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (Int.natAbs_dvd.mpr ⟨_, H⟩)

/-- If the natural number `n` is a sum of two squares of coprime natural numbers, then
`-1` is a square modulo `n`. -/
/-
**ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime {n x y : Nat} (h : n = x 
^ 2 + y ^ 2) (hc : x.Coprime y) : IsSquare (-1 : ZMod n)
参数：h : n = x ^ 2 + y ^ 2；hc : x.Coprime y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime`：ZMod.isSquare_neg_on
e_of_eq_sq_add_sq_of_isCoprime {n x y : Int} (h : n = x ^ 2 + y ^ 2) (hc : IsCop
rime x y) : IsSquare (-1 : ZMod n.natAbs…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.Coprime.isCoprime`：∀ {m n : ℕ}, m.Coprime n → IsCoprime ↑m ↑n

--- 原说明 ---
If the natural number `n` is a sum of two squares of coprime natural numbers, th
en
`-1` is a square modulo `n`.
-/
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime {n x y : ℕ} (h : n = x ^ 2 + y ^ 2)
    (hc : x.Coprime y) : IsSquare (-1 : ZMod n) := by
  zify at h
  exact ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime h hc.isCoprime

set_option backward.isDefEq.respectTransparency false in
/-- A natural number `n` is a sum of two squares if and only if `n = a^2 * b` with natural
numbers `a` and `b` such that `-1` is a square modulo `b`. -/
/-
**Nat.eq_sq_add_sq_iff_eq_sq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.eq_sq_add_sq_iff_eq_sq_mul {n : Nat} : (exists x y : Nat, n = x ^ 2 + 
y ^ 2) ↔ exists a b : Nat, n = a ^ 2 * b ∧ IsSquare (-1 : ZMod b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Fin.one_eq_zero_iff`：∀ {n : ℕ} [inst : NeZero n], 1 = 0 ↔ n = 1
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.gcd_eq_zero_iff`：∀ {i j : ℕ}, i.gcd j = 0 ↔ i = 0 ∧ j = 0
· 使用定理 `Nat.exists_coprime'`：∀ {m n : ℕ}, 0 < m.gcd n → ∃ g m' n', 0 < g ∧ m'.Co
prime n' ∧ m = m' * g ∧ n = n' * g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
A natural number `n` is a sum of two squares if and only if `n = a^2 * b` with n
atural
numbers `a` and `b` such that `-1` is a square modulo `b`.
-/
theorem Nat.eq_sq_add_sq_iff_eq_sq_mul {n : ℕ} :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∃ a b : ℕ, n = a ^ 2 * b ∧ IsSquare (-1 : ZMod b) := by
  constructor
  · rintro ⟨x, y, h⟩
    by_cases hxy : x = 0 ∧ y = 0
    · exact ⟨0, 1, by rw [h, hxy.1, hxy.2, zero_pow two_ne_zero, add_zero, zero_mul],
        ⟨0, by rw [zero_mul, neg_eq_zero, Fin.one_eq_zero_iff]⟩⟩
    · have hg := Nat.pos_of_ne_zero (mt Nat.gcd_eq_zero_iff.mp hxy)
      obtain ⟨g, x₁, y₁, _, h₂, h₃, h₄⟩ := Nat.exists_coprime' hg
      exact ⟨g, x₁ ^ 2 + y₁ ^ 2, by rw [h, h₃, h₄]; ring,
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl h₂⟩
  · rintro ⟨a, b, h₁, h₂⟩
    obtain ⟨x', y', h⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one h₂
    exact ⟨a * x', a * y', by rw [h₁, h]; ring⟩

end NegOneSquare

/-!
### Characterization in terms of the prime factorization
-/


section Main

/-- A (positive) natural number `n` is a sum of two squares if and only if the exponent of
every prime `q` such that `q % 4 = 3` in the prime factorization of `n` is even.
(The assumption `0 < n` is not present, since for `n = 0`, both sides are satisfied;
the right-hand side holds, since `padicValNat q 0 = 0` by definition.) -/
/-
**Nat.eq_sq_add_sq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.eq_sq_add_sq_iff {n : Nat} : (exists x y, n = x ^ 2 + y ^ 2) ↔ forall 
q in n.primeFactors, q % 4 = 3 -> Even (padicValNat q n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用引理 `Even.zero`：Even.zero [Zero β] : Function.Even (fun (_ : α) => (0 : β))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.eq_sq_add_sq_iff_eq_sq_mul`：Nat.eq_sq_add_sq_iff_eq_sq_mul {n : Nat}
 : (exists x y : Nat, n = x ^ 2 + y ^ 2) ↔ exists a b : Nat, n = a ^ 2 * b ∧ IsS
quare (-1 : ZMod b)
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Nat.sq_mul_squarefree_of_pos`：sq_mul_squarefree_of_pos {n : Nat} (hn : 0
 < n) : exists a b : Nat, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three`：ZMo
d.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three {n : Nat} (hn :
 Squarefree n) : IsSquare (-1 : ZMod n) ↔ forall q in n.p…
· 使用引理 `Nat.primeFactors_mono`：primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : p
rimeFactors m subseteq primeFactors n
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b

--- 原说明 ---
A (positive) natural number `n` is a sum of two squares if and only if the expon
ent of
every prime `q` such that `q % 4 = 3` in the prime factorization of `n` is even.
(The assumption `0 < n` is not present, since for `n = 0`, both sides are satisf
ied;
the right-hand side holds, since `padicValNat q 0 = 0` by definition.)
-/
theorem Nat.eq_sq_add_sq_iff {n : ℕ} :
    (∃ x y, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
  rcases n.eq_zero_or_pos with (rfl | hn₀)
  · exact ⟨fun _ q _ _ ↦ (padicValNat_zero_right _).symm ▸ Even.zero, fun _ ↦ ⟨0, 0, rfl⟩⟩
  -- now `0 < n`
  refine eq_sq_add_sq_iff_eq_sq_mul.trans ⟨fun ⟨a, b, h₁, h₂⟩ q hq h ↦ ?_, fun H ↦ ?_⟩
  · have : Fact q.Prime := ⟨prime_of_mem_primeFactors hq⟩
    have : q ∣ b → q ∈ b.primeFactors := by grind
    grind (splits := 10) [padicValNat.mul, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd, mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one]
  · obtain ⟨b, a, hb₀, ha₀, hab, hb⟩ := sq_mul_squarefree_of_pos hn₀
    refine ⟨a, b, hab.symm, ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hb
      |>.mpr fun q hq hq4 ↦ ?_⟩
    have : Fact q.Prime := ⟨prime_of_mem_primeFactors hq⟩
    have := Nat.primeFactors_mono <| Dvd.intro_left _ hab
    have : b.factorization q = 1 := by grind [Squarefree.natFactorization_le_one,
      Prime.dvd_iff_one_le_factorization, prime_of_mem_primeFactors, dvd_of_mem_primeFactors]
    grind [factorization_def, prime_of_mem_primeFactors, padicValNat.mul, padicValNat.pow]

end Main

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Decidable (∃ x y, n = x ^ 2 + y ^ 2) :=
  decidable_of_iff' _ Nat.eq_sq_add_sq_iff
