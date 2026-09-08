/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
## Polynomials over finite fields
-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*}

/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `ZMod n`. -/
/-
**MvPolynomial.C_dvd_iff_zmod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_dvd_iff_zmod (n : Nat) (φ : MvPolynomial σ Int) : C (n : Int) ∣ φ ↔ map 
(Int.castRingHom (ZMod n)) φ = 0
参数：n : Nat；φ : MvPolynomial σ Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.C_dvd_iff_map_hom_eq_zero`：C_dvd_iff_map_hom_eq_zero (q : R
 ->+* S₁) (r : R) (hr : forall r' : R, q r' = 0 ↔ r ∣ r') (φ : MvPolynomial σ R)
 : C r ∣ φ ↔ map q φ = 0
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a

--- 原说明 ---
A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `ZMod n`.
-/
theorem C_dvd_iff_zmod (n : ℕ) (φ : MvPolynomial σ ℤ) :
    C (n : ℤ) ∣ φ ↔ map (Int.castRingHom (ZMod n)) φ = 0 :=
  C_dvd_iff_map_hom_eq_zero _ _ (CharP.intCast_eq_zero_iff (ZMod n) n) _

section frobenius

variable {p : ℕ} [Fact p.Prime]

/-
**MvPolynomial.frobenius_zmod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：frobenius_zmod (f : MvPolynomial σ (ZMod p)) : frobenius _ p f = expand p 
f
参数：f : MvPolynomial σ (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `MvPolynomial.instExpChar`：∀ (σ : Type u) (R : Type v) [inst : CommSemiri
ng R] (p : ℕ) [ExpChar R p], ExpChar (MvPolynomial σ R) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_C`：expand_C (r : R) : expand p (C r : MvPolynomial σ
 R) = C r
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_pow`：C_pow (a : R) (n : Nat) : (C (a ^ n) : MvPolynomial 
σ R) = C a ^ n
· 使用定理 `ZMod.pow_card`：pow_card (x : ZMod p) : x ^ p = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.expand_X`：expand_X (i : σ) : expand p (X i : MvPolynomial σ
 R) = X i ^ p
-/
theorem frobenius_zmod (f : MvPolynomial σ (ZMod p)) : frobenius _ p f = expand p f := by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
  · simp only [map_add]; intro _ _ hf hg; rw [hf, hg]
  · simp only [expand_X, map_mul]
    intro _ _ hf; rw [hf, frobenius_def]
/-
**MvPolynomial.expand_zmod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_zmod (f : MvPolynomial σ (ZMod p)) : expand p f = f ^ p
参数：f : MvPolynomial σ (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.instExpChar`：∀ (σ : Type u) (R : Type v) [inst : CommSemiri
ng R] (p : ℕ) [ExpChar R p], ExpChar (MvPolynomial σ R) p
· 使用定理 `MvPolynomial.frobenius_zmod`：frobenius_zmod (f : MvPolynomial σ (ZMod p)
) : frobenius _ p f = expand p f
-/
theorem expand_zmod (f : MvPolynomial σ (ZMod p)) : expand p f = f ^ p :=
  (frobenius_zmod _).symm

end frobenius

end MvPolynomial

namespace MvPolynomial

noncomputable section

open Set LinearMap Submodule

variable {K : Type*} {σ : Type*}

section Indicator

variable [Fintype K] [Fintype σ]

/-- Over a field, this is the indicator function as an `MvPolynomial`. -/
/-
**MvPolynomial.indicator** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：indicator [CommRing K] (a : σ -> K) : MvPolynomial σ K
参数：a : σ -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Over a field, this is the indicator function as an `MvPolynomial`.
-/
def indicator [CommRing K] (a : σ → K) : MvPolynomial σ K :=
  ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))

section CommRing

variable [CommRing K]

/-
**MvPolynomial.eval_indicator_apply_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：eval_indicator_apply_eq_one (a : σ -> K) : eval a (indicator a) = 1
参数：a : σ -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_indicator_apply_eq_one (a : σ → K) : eval a (indicator a) = 1 := by
  nontriviality
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this.ne', sub_zero, Finset.prod_const_one]
/-
**MvPolynomial.degrees_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_indicator (c : σ -> K) : degrees (indicator c) <= ∑ s : σ, (Fintyp
e.card K - 1) • {s}
参数：c : σ -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.indicator.eq_1`：∀ {K : Type u_1} {σ : Type u_2} [inst : Fin
type K] [inst_1 : Fintype σ] [inst_2 : CommRing K] (a : σ → K),   MvPolynomial.i
ndicator a = ∏ n,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MvPolynomial.degrees_prod_le`：degrees_prod_le {ι : Type*} {s : Finset ι}
 {f : ι -> MvPolynomial σ R} : (∏ i in s, f i).degrees <= ∑ i in s, (f i).degree
s
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `MvPolynomial.degrees_sub_le`：degrees_sub_le [DecidableEq σ] {p q : MvPol
ynomial σ R} : (p - q).degrees <= p.degrees union q.degrees
· 使用定理 `MvPolynomial.degrees_one`：degrees_one : degrees (1 : MvPolynomial σ R) =
 0
· 使用定理 `Multiset.zero_union`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multis
et α}, 0 ∪ s = s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MvPolynomial.degrees_pow_le`：degrees_pow_le {p : MvPolynomial σ R} {n : 
Nat} : (p ^ n).degrees <= n • p.degrees
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
· 使用定理 `Multiset.union_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multis
et α}, s ∪ 0 = s
· 使用定理 `MvPolynomial.degrees_X'`：degrees_X' (n : σ) : degrees (X n : MvPolynomia
l σ R) <= {n}
-/
theorem degrees_indicator (c : σ → K) :
    degrees (indicator c) ≤ ∑ s : σ, (Fintype.card K - 1) • {s} := by
  rw [indicator]
  classical
  refine degrees_prod_le.trans <| Finset.sum_le_sum fun s _ ↦ degrees_sub_le.trans ?_
  rw [degrees_one, Multiset.zero_union]
  refine le_trans degrees_pow_le (nsmul_le_nsmul_right ?_ _)
  refine degrees_sub_le.trans ?_
  rw [degrees_C, Multiset.union_zero]
  exact degrees_X' _
/-
**MvPolynomial.indicator_mem_restrictDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：indicator_mem_restrictDegree (c : σ -> K) : indicator c in restrictDegree 
σ K (Fintype.card K - 1)
参数：c : σ -> K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_restrictDegree_iff_sup`：mem_restrictDegree_iff_sup [Dec
idableEq σ] (p : MvPolynomial σ R) (n : Nat) : p in restrictDegree σ R n ↔ foral
l i, p.degrees.count i <= n
· 使用定理 `MvPolynomial.indicator.eq_1`：∀ {K : Type u_1} {σ : Type u_2} [inst : Fin
type K] [inst_1 : Fintype σ] [inst_2 : CommRing K] (a : σ → K),   MvPolynomial.i
ndicator a = ∏ n,…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `MvPolynomial.degrees_indicator`：degrees_indicator (c : σ -> K) : degrees
 (indicator c) <= ∑ s : σ, (Fintype.card K - 1) • {s}
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Multiset.count_singleton_self`：count_singleton_self (a : α) : count a ({
a} : Multiset α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem indicator_mem_restrictDegree (c : σ → K) :
    indicator c ∈ restrictDegree σ K (Fintype.card K - 1) := by
  classical
  rw [mem_restrictDegree_iff_sup, indicator]
  intro n
  refine le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq ?_)
  simp_rw [← Multiset.coe_countAddMonoidHom, map_sum,
    map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  · refine Finset.sum_eq_single n ?_ ?_
    · intro b _ ne
      simp [ne, eqComm]
    · intro h; exact (h <| Finset.mem_univ _).elim
  · rw [Multiset.count_singleton_self, mul_one]

end CommRing

variable [Field K]

/-
**MvPolynomial.eval_indicator_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：eval_indicator_apply_eq_zero (a b : σ -> K) (h : a != b) : eval a (indicat
or b) = 0
参数：a b : σ -> K；h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem eval_indicator_apply_eq_zero (a b : σ → K) (h : a ≠ b) : eval a (indicator b) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by rwa [Ne, funext_iff, not_forall] at h
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
    Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [FiniteField.pow_card_sub_one_eq_one, sub_self]
  rwa [Ne, sub_eq_zero]

end Indicator

section

variable (K σ)

set_option backward.isDefEq.respectTransparency false in
/-- `MvPolynomial.eval` as a `K`-linear map. -/
@[simps]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.eval` as a `K`-linear map.
-/
def evalₗ [CommSemiring K] : MvPolynomial σ K →ₗ[K] (σ → K) → K where
  toFun p e := eval e p
  map_add' p q := by ext x; simp
  map_smul' a p := by ext e; simp

variable [Field K] [Fintype K] [Finite σ]
/-
**MvPolynomial.map_restrict_dom_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_restrict_dom_evalₗ : (restrictDegree σ K (Fintype.card K - 1)).map (evalₗ K σ) = ⊤ := by
  cases nonempty_fintype σ
  refine top_unique (SetLike.le_def.2 fun e _ => mem_map.2 ?_)
  classical
  refine ⟨∑ n : σ → K, e n • indicator n, ?_, ?_⟩
  · exact sum_mem fun c _ => smul_mem _ _ (indicator_mem_restrictDegree _)
  · ext n
    simp only [evalₗ_apply, map_sum, smul_eval]
    rw [Finset.sum_eq_single n] <;>
      aesop (add simp [eval_indicator_apply_eq_zero, eval_indicator_apply_eq_one, eq_comm])

end

end

end MvPolynomial

namespace MvPolynomial

open scoped Cardinal
open LinearMap Submodule

universe u

variable (σ : Type u) (K : Type u) [Fintype K]

/-- The submodule of multivariate polynomials whose degree of each variable is strictly less
than the cardinality of K. -/
/-
**MvPolynomial.R** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：R [CommRing K] : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of multivariate polynomials whose degree of each variable is stric
tly less
than the cardinality of K.
-/
def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)
-- The `AddCommGroup, Module K, Inhabited` instances should be constructed by a deriving handler.
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommRing K] : AddCommGroup (R σ K) :=
  inferInstanceAs (AddCommGroup (restrictDegree σ K (Fintype.card K - 1)))
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommRing K] : Module K (R σ K) :=
  inferInstanceAs (Module K (restrictDegree σ K (Fintype.card K - 1)))
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommRing K] : Inhabited (R σ K) :=
  inferInstanceAs (Inhabited (restrictDegree σ K (Fintype.card K - 1)))

/-- Evaluation in the `MvPolynomial.R` subtype. -/
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation in the `MvPolynomial.R` subtype.
-/
noncomputable def evalᵢ [CommRing K] : R σ K →ₗ[K] (σ → K) → K :=
  (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).subtype

-- TODO: would be nice to replace this by suitable decidability assumptions
open scoped Classical in
/-
**MvPolynomial.decidableRestrictDegree** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：decidableRestrictDegree (m : Nat) : DecidablePred (· in { n : σ ->₀ Nat | 
forall i, n i <= m })
参数：m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance decidableRestrictDegree (m : ℕ) :
    DecidablePred (· ∈ { n : σ →₀ ℕ | ∀ i, n i ≤ m }) := by
  simp only [Set.mem_ofPred_eq]; infer_instance

variable [Field K]

open scoped Classical in
/-
**MvPolynomial.rank_R** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rank_R [Fintype σ] : Module.rank K (R σ K) = Fintype.card (σ -> K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_finsupp_self'`：rank_finsupp_self' {ι : Type u} : Module.rank R (ι -
>₀ R) = #ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `le_tsub_iff_right`：le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <
= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
-/
theorem rank_R [Fintype σ] : Module.rank K (R σ K) = Fintype.card (σ → K) :=
  calc
    Module.rank K (R σ K) =
        Module.rank K (↥{ s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 } →₀ K) :=
      LinearEquiv.rank_eq
        (AddMonoidAlgebra.supportedEquivFinsupp { s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 })
    _ = #{ s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 } := by rw [rank_finsupp_self']
    _ = #{ s : σ → ℕ | ∀ n : σ, s n < Fintype.card K } := by
      refine Quotient.sound ⟨Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun f => ?_⟩
      refine forall_congr' fun n => le_tsub_iff_right ?_
      exact Fintype.card_pos_iff.2 ⟨0⟩
    _ = #(σ → { n // n < Fintype.card K }) :=
      (@Equiv.subtypePiEquivPi σ (fun _ => ℕ) fun _ n => n < Fintype.card K).cardinal_eq
    _ = #(σ → Fin (Fintype.card K)) :=
      (Equiv.arrowCongr (Equiv.refl σ) Fin.equivSubtype.symm).cardinal_eq
    _ = #(σ → K) := (Equiv.arrowCongr (Equiv.refl σ) (Fintype.equivFin K).symm).cardinal_eq
    _ = Fintype.card (σ → K) := Cardinal.mk_fintype _
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite σ] : FiniteDimensional K (R σ K) := by
  cases nonempty_fintype σ
  rw [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0]
  simpa only [rank_R] using Cardinal.natCast_lt_aleph0

open scoped Classical in
/-
**MvPolynomial.finrank_R** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：finrank_R [Fintype σ] : Module.finrank K (R σ K) = Fintype.card (σ -> K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `MvPolynomial.rank_R`：rank_R [Fintype σ] : Module.rank K (R σ K) = Fintyp
e.card (σ -> K)
-/
theorem finrank_R [Fintype σ] : Module.finrank K (R σ K) = Fintype.card (σ → K) :=
  Module.finrank_eq_of_rank_eq (rank_R σ K)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.range_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_evalᵢ [Finite σ] : range (evalᵢ σ K) = ⊤ := by
  rw [evalᵢ, LinearMap.range_comp, range_subtype]
  exact map_restrict_dom_evalₗ K σ
/-
**MvPolynomial.ker_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_evalₗ [Finite σ] : ker (evalᵢ σ K) = ⊥ := by
  cases nonempty_fintype σ
  refine (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank ?_).mpr (range_evalᵢ σ K)
  classical
  rw [Module.finrank_fintype_fun_eq_card, finrank_R]
/-
**MvPolynomial.eq_zero_of_eval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K) (h : forall v : 
σ -> K, eval v p = 0) (hp : p in restrictDegree σ K (Fintype.card K - 1)) : p = 
0
参数：p : MvPolynomial σ K；h : forall v : σ -> K, eval v p = 0；hp : p in restrictDe
gree σ K (Fintype.card K - 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `MvPolynomial.ker_evalₗ`：ker_evalₗ [Finite σ] : ker (evalᵢ σ K) = ⊥
-/
theorem eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K) (h : ∀ v : σ → K, eval v p = 0)
    (hp : p ∈ restrictDegree σ K (Fintype.card K - 1)) : p = 0 :=
  let p' : R σ K := ⟨p, hp⟩
  have : p' ∈ ker (evalᵢ σ K) := funext h
  show p'.1 = (0 : R σ K).1 from congr_arg _ <| by rwa [ker_evalₗ, mem_bot] at this

end MvPolynomial

