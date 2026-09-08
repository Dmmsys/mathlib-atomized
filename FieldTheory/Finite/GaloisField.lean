/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `GaloisField p n` is defined as the splitting field of `X^(p^n) - X` over `ZMod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `GaloisField p n` is a field with `p ^ n` elements

## Main Results

- `GaloisField.algEquivGaloisField`: Any finite field is isomorphic to some Galois field
- `FiniteField.algEquivOfCardEq`: Uniqueness of finite fields : algebra isomorphism
- `FiniteField.ringEquivOfCardEq`: Uniqueness of finite fields : ring isomorphism
- `card_algHom_of_finrank_dvd`: if `[K:F] ∣ [L:F]` then `#(K →ₐ[F] L) = [K:F]`
- `nonempty_algHom_iff_finrank_dvd`: `(K →ₐ[F] L)` is nonempty iff `[K:F] ∣ [L:F]`. This and the
  above result helps to classify the category of finite fields.

-/

@[expose] public section


noncomputable section


open Polynomial Finset

open scoped Polynomial

/-
**FiniteField.isSplittingField_sub** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiniteField.isSplittingField_sub (K F : Type*) [Field K] [Fintype K] [Fiel
d F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where splits'
参数：K F : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.X_pow_card_sub_X_natDegree_eq`：X_pow_card_sub_X_natDegree_eq
 (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `FiniteField.roots_X_pow_card_sub_X`：roots_X_pow_card_sub_X : roots (X ^ 
q - X : K[X]) = Finset.univ.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.val_toFinset`：val_toFinset [DecidableEq α] (s : Finset α) : s.val
.toFinset = s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Algebra.adjoin_univ`：adjoin_univ : adjoin R (Set.univ : Set A) = ⊤
-/
instance FiniteField.isSplittingField_sub (K F : Type*) [Field K] [Fintype K]
    [Field F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where
  splits' := by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow,
      map_X, h, FiniteField.roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_rootSet' := by
    classical
    trans Algebra.adjoin F ((roots (X ^ Fintype.card K - X : K[X])).toFinset : Set K)
    · simp only [rootSet, aroots, Polynomial.map_pow, map_X, Polynomial.map_sub]
    · rw [FiniteField.roots_X_pow_card_sub_X, val_toFinset, coe_univ, Algebra.adjoin_univ]
/-
**galois_poly_separable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：galois_poly_separable {K : Type*} [CommRing K] (p q : Nat) [CharP K p] (h 
: p ∣ q) : Separable (X ^ q - X : K[X])
参数：p q : Nat；h : p ∣ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_X_pow`：derivative_X_pow (n : Nat) : derivative (X 
^ n : R[X]) = C (n : R) * X ^ (n - 1)
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
（共 49 条，此处仅展示前 30 条）
-/
theorem galois_poly_separable {K : Type*} [CommRing K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
    Separable (X ^ q - X : K[X]) := by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub, derivative_X_pow, derivative_X, C_eq_natCast, h]
  ring

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
/-
**GaloisField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GaloisField
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field.
-/
def GaloisField := SplittingField (X ^ p ^ n - X : (ZMod p)[X])
deriving Inhabited, Field, CharP _ p,
  Algebra (ZMod p),
  Finite, FiniteDimensional (ZMod p),
  IsSplittingField (ZMod p) _ (X ^ p ^ n - X)

namespace GaloisField

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-
**GaloisField.finrank** 是 Mathlib 中的一个定理，位于命名空间 `GaloisField`。
形式化陈述：finrank {n} (h : n != 0) : Module.finrank (ZMod p) (GaloisField p n) = n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFiniteGaloisField`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (n : ℕ), Fi
nite (GaloisField p n)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `FiniteField.X_pow_card_pow_sub_X_ne_zero`：X_pow_card_pow_sub_X_ne_zero (
hn : n != 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.card_rootSet_eq_natDegree`：card_rootSet_eq_natDegree [Algebra
 F K] {p : F[X]} (hsep : p.Separable) (hsplit : Splits (p.map (algebraMap F K)))
 : Fintype.card (p.rootSet…
· 使用定理 `galois_poly_separable`：galois_poly_separable {K : Type*} [CommRing K] (p
 q : Nat) [CharP K p] (h : p ∣ q) : Separable (X ^ q - X : K[X])
· 使用引理 `dvd_pow`：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ 
n | 0, hn => (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_rig…
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `FiniteField.X_pow_card_pow_sub_X_natDegree_eq`：X_pow_card_pow_sub_X_natD
egree_eq (hn : n != 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]).natDegree = p ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.SplittingField.adjoin_rootSet`：adjoin_rootSet : Algebra.adjoi
n K (f.rootSet (SplittingField f)) = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Subring.closure_induction`：closure_induction {s : Set R} {p : (x : R) ->
 x in closure s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_closure hx
)) (zero : p 0 …
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 73 条，此处仅展示前 30 条）
-/
theorem finrank {n} (h : n ≠ 0) : Module.finrank (ZMod p) (GaloisField p n) = n := by
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  have hp : 1 < p := h_prime.out.one_lt
  have aux : g_poly ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) = g_poly.natDegree :=
    card_rootSet_eq_natDegree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
      (SplittingField.splits (g_poly : (ZMod p)[X]))
  have nat_degree_eq : g_poly.natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ h hp
  rw [nat_degree_eq] at key
  suffices g_poly.rootSet (GaloisField p n) = Set.univ by
    simp_rw [this, ← Fintype.ofEquiv_card (Equiv.Set.univ _)] at key
    -- Porting note: prevents `card_eq_pow_finrank` from using a wrong instance for `Fintype`
    rw [@Module.card_eq_pow_finrank (K := ZMod p), ZMod.card] at key
    exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key
  rw [Set.eq_univ_iff_forall]
  suffices ∀ (x) (hx : x ∈ (⊤ : Subalgebra (ZMod p) (GaloisField p n))),
      x ∈ (X ^ p ^ n - X : (ZMod p)[X]).rootSet (GaloisField p n)
    by simpa
  rw [← SplittingField.adjoin_rootSet]
  simp_rw [Algebra.mem_adjoin_iff]
  intro x hx
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  simp only [g_poly] at aux
  refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hx
    <;> simp_rw [mem_rootSet_of_ne aux]
  · rintro x (⟨r, rfl⟩ | hx)
    · simp only [map_sub, map_pow, aeval_X]
      rw [← map_pow, ZMod.pow_card_pow, sub_self]
    · dsimp only [GaloisField] at hx
      rwa [mem_rootSet_of_ne aux] at hx
  · rw [← coeff_zero_eq_aeval_zero']
    simp only [coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub]
    intro hn
    exact Nat.not_lt_zero 1 (eq_zero_of_pow_eq_zero hn.symm ▸ hp)
  · simp
  · simp only [aeval_X_pow, aeval_X, map_sub, add_pow_char_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx, hy]
  · intro x _ hx
    simp only [g_poly, sub_eq_zero, aeval_X_pow, aeval_X, map_sub, sub_neg_eq_add] at *
    rw [neg_pow, hx, neg_one_pow_char_pow]
    simp
  · simp only [aeval_X_pow, aeval_X, map_sub, mul_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx, hy]
/-
**GaloisField.card** 是 Mathlib 中的一个定理，位于命名空间 `GaloisField`。
形式化陈述：card (h : n != 0) : Nat.card (GaloisField p n) = p ^ n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `instFiniteGaloisField`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (n : ℕ), Fi
nite (GaloisField p n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Module.card_fintype`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_
3 : Finty…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `GaloisField.finrank`：finrank {n} (h : n != 0) : Module.finrank (ZMod p) 
(GaloisField p n) = n
-/
theorem card (h : n ≠ 0) : Nat.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card, Module.card_fintype b, ← Module.finrank_eq_card_basis b,
    ZMod.card, finrank p h]
/-
**GaloisField.splits_zmod_X_pow_sub_X** 是 Mathlib 中的一个定理，位于命名空间 `GaloisField`。
形式化陈述：splits_zmod_X_pow_sub_X : Splits (X ^ p - X : (ZMod p)[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `FiniteField.roots_X_pow_card_sub_X`：roots_X_pow_card_sub_X : roots (X ^ 
q - X : K[X]) = Finset.univ.val
· 使用定理 `FiniteField.X_pow_card_sub_X_natDegree_eq`：X_pow_card_sub_X_natDegree_eq
 (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
theorem splits_zmod_X_pow_sub_X : Splits (X ^ p - X : (ZMod p)[X]) := by
  have hp : 1 < p := h_prime.out.one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert! FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  rw [splits_iff_card_roots, h1, ← Finset.card_def, Finset.card_univ, h2, ZMod.card]

/-- A Galois field with exponent 1 is equivalent to `ZMod` -/
/-
**GaloisField.equivZmodP** 是 Mathlib 中的一个定义，位于命名空间 `GaloisField`。
形式化陈述：equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Galois field with exponent 1 is equivalent to `ZMod`
-/
def equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p :=
  have h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  have inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

section Fintype

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

/-
**GaloisField._root_.FiniteField.splits_X_pow_card_sub_X** 是 Mathlib 中的一个定理，位于命名
空间 `GaloisField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FiniteField.splits_X_pow_card_sub_X :
    Splits (map (algebraMap (ZMod p) K) (X ^ Fintype.card K - X)) :=
  (FiniteField.isSplittingField_sub K (ZMod p)).splits
/-
**GaloisField._root_.FiniteField.isSplittingField_of_card_eq** 是 Mathlib 中的一个定理，
位于命名空间 `GaloisField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FiniteField.isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.isSplittingField_sub K (ZMod p)

/-- Any finite field is (possibly noncanonically) isomorphic to some Galois field. -/
/-
**GaloisField.algEquivGaloisFieldOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `GaloisFiel
d`。
形式化陈述：algEquivGaloisFieldOfFintype (h : Fintype.card K = p ^ n) : K ≃ₐ[ZMod p] G
aloisField p n
参数：h : Fintype.card K = p ^ n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.isSplittingField_of_card_eq`：∀ (p : ℕ) [h_prime : Fact (Nat.
Prime p)] (n : ℕ) {K : Type u_1} [inst : Field K] [inst_1 : Fintype K]   [inst_2
 : Algebra (ZMod p) K],   Fin…

--- 原说明 ---
Any finite field is (possibly noncanonically) isomorphic to some Galois field.
-/
def algEquivGaloisFieldOfFintype (h : Fintype.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Fintype

section Finite

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/-
**GaloisField._root_.FiniteField.splits_X_pow_nat_card_sub_X** 是 Mathlib 中的一个定理，
位于命名空间 `GaloisField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FiniteField.splits_X_pow_nat_card_sub_X [Finite K] :
    Splits (map (algebraMap (ZMod p) K) (X ^ Nat.card K - X)) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.isSplittingField_sub K (ZMod p)).splits
/-
**GaloisField._root_.FiniteField.isSplittingField_of_nat_card_eq** 是 Mathlib 中的一
个定理，位于命名空间 `GaloisField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FiniteField.isSplittingField_of_nat_card_eq (h : Nat.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) := by
  have : Finite K := (Nat.card_pos_iff.mp (h ▸ pow_pos h_prime.1.pos n)).2
  have : Fintype K := Fintype.ofFinite K
  rw [← h, Nat.card_eq_fintype_card]
  exact FiniteField.isSplittingField_sub K (ZMod p)
/-
**GaloisField._root_.Polynomial.splits_X_pow_nat_card_sub_X** 是 Mathlib 中的一个定理，位
于命名空间 `GaloisField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.splits_X_pow_nat_card_sub_X :
    Splits (X ^ (Nat.card K) - X : K[X]) := by
  cases fintypeOrInfinite K
  · have := (IsSplittingField.splits (L := K) (X ^ (Fintype.card K) - X : K[X]))
    simpa [Algebra.algebraMap_self, map_sub, map_pow, map_X] using this
  · rw [← Polynomial.splits_neg_iff]
    simpa [Nat.card_eq_zero_of_infinite, pow_zero, neg_sub] using Splits.X_sub_C (1 : K)
/-
**GaloisField.** 是 Mathlib 中的一个实例，位于命名空间 `GaloisField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {K K' : Type*} [Field K] [Field K'] [Finite K'] [Algebra K K'] :
    IsGalois K K' := by
  cases nonempty_fintype K'
  obtain ⟨p, hp⟩ := CharP.exists K
  have : CharP K p := hp
  have : CharP K' p := charP_of_injective_algebraMap' K p
  exact IsGalois.of_separable_splitting_field
    (galois_poly_separable p (Fintype.card K')
      (let ⟨n, _, hn⟩ := FiniteField.card K' p
      hn.symm ▸ dvd_pow_self p n.ne_zero))

/-- Any finite field is (possibly noncanonically) isomorphic to some Galois field. -/
/-
**GaloisField.algEquivGaloisField** 是 Mathlib 中的一个定义，位于命名空间 `GaloisField`。
形式化陈述：algEquivGaloisField (h : Nat.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p 
n
参数：h : Nat.card K = p ^ n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.isSplittingField_of_nat_card_eq`：∀ (p : ℕ) [h_prime : Fact (
Nat.Prime p)] (n : ℕ) {K : Type u_1} [inst : Field K] [inst_1 : Algebra (ZMod p)
 K],   Nat.card K = p ^ n → Polyn…

--- 原说明 ---
Any finite field is (possibly noncanonically) isomorphic to some Galois field.
-/
def algEquivGaloisField (h : Nat.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Finite

end GaloisField

namespace FiniteField

variable {K K' : Type*} [Field K] [Field K']

section norm

variable [Algebra K K'] [Finite K']

/-
**FiniteField.algebraMap_norm_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：algebraMap_norm_eq_pow {x : K'} : algebraMap K K' (Algebra.norm K x) = x ^
 ((Nat.card K' - 1) / (Nat.card K - 1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Algebra.norm_eq_prod_automorphisms`：norm_eq_prod_automorphisms [IsGalois
 K L] (x : L) : algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x
· 使用定理 `GaloisField.instIsGaloisOfFinite`：∀ {K : Type u_2} {K' : Type u_3} [inst
 : Field K] [inst_1 : Field K'] [Finite K'] [inst_3 : Algebra K K'], IsGalois K 
K'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type 
u_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   {e : ι → 
κ}, Function.Bijec…
· 使用定理 `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`：bijective_froben
iusAlgEquivOfAlgebraic_pow : Function.Bijective fun n : Fin (Module.finrank K L)
 => frobeniusAlgEquivOfAlgebraic K L ^ n.1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgEquiv.coe_pow`：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R
] [inst_1 : Semiring A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(
e ^ n)…
· 使用定理 `pow_iterate`：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^
 k)^[n] = fun x => x ^ k ^ n
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `Fin.sum_univ_eq_sum_range`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f 
: ℕ → α) (n : ℕ), ∑ i, f ↑i = ∑ i ∈ Finset.range n, f i
· 使用引理 `Nat.geomSum_eq`：geomSum_eq (hm : 2 <= m) (n : Nat) : ∑ k in range n, m ^
 k = (m ^ n - 1) / (m - 1)
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_norm_eq_pow {x : K'} :
    algebraMap K K' (Algebra.norm K x) = x ^ ((Nat.card K' - 1) / (Nat.card K - 1)) := by
  have := Finite.of_injective _ (algebraMap K K').injective
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  simp_rw [← Fintype.card_eq_nat_card, Algebra.norm_eq_prod_automorphisms,
    ← (bijective_frobeniusAlgEquivOfAlgebraic_pow K K').prod_comp, AlgEquiv.coe_pow,
    coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range, Nat.geomSum_eq Fintype.one_lt_card, ← Module.card_eq_pow_finrank]

variable (K K')
/-
**FiniteField.unitsMap_norm_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：unitsMap_norm_surjective : Function.Surjective (Units.map <| Algebra.norm 
K (S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective_finite_range`：Finite.of_injective_finite_range {f : 
ι -> α} (hf : Function.Injective f) [Finite (range f)] : Finite ι
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `MonoidHom.surjective_of_card_ker_le_div`：surjective_of_card_ker_le_div {
G M : Type*} [Group G] [Group M] [Finite G] [Finite M] (f : G ->* M) (h : Nat.ca
rd f.ker <= Nat.card G / Nat.…
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_units`：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.car
d α - 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `SetLike.coe_sort_coe`：coe_sort_coe : ((p : Set B) : Type _) = p
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `FiniteField.algebraMap_norm_eq_pow`：algebraMap_norm_eq_pow {x : K'} : al
gebraMap K K' (Algebra.norm K x) = x ^ ((Nat.card K' - 1) / (Nat.card K - 1))
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 39 条，此处仅展示前 30 条）
-/
theorem unitsMap_norm_surjective : Function.Surjective (Units.map <| Algebra.norm K (S := K')) :=
  have := Finite.of_injective_finite_range (algebraMap K K').injective
  MonoidHom.surjective_of_card_ker_le_div _ <| by
    simp_rw [Nat.card_units]
    classical
    have := Fintype.ofFinite K'ˣ
    convert!
      IsCyclic.card_pow_eq_one_le (α := K'ˣ) <|
        Nat.div_pos
            (Nat.sub_le_sub_right (Nat.card_le_card_of_injective _ (algebraMap K K').injective)
              _) <|
          Nat.sub_pos_of_lt Finite.one_lt_card
    rw [← Set.ncard_coe_finset, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]; congr 1; ext
    simp [Units.ext_iff, ← (algebraMap K K').injective.eq_iff, algebraMap_norm_eq_pow]
/-
**FiniteField.norm_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：norm_surjective : Function.Surjective (Algebra.norm K (S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Algebra.norm_zero`：norm_zero [Nontrivial S] [Module.Free R S] [Module.Fi
nite R S] : norm R (0 : S) = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.unitsMap_norm_surjective`：unitsMap_norm_surjective : Functio
n.Surjective (Units.map <| Algebra.norm K (S
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem norm_surjective : Function.Surjective (Algebra.norm K (S := K')) := fun k ↦ by
  obtain rfl | ne := eq_or_ne k 0
  · exact ⟨0, Algebra.norm_zero ..⟩
  have ⟨x, eq⟩ := unitsMap_norm_surjective K K' (Units.mk0 k ne)
  exact ⟨x, congr_arg (·.1) eq⟩

end norm

variable [Fintype K] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly noncanonically) isomorphic -/
/-
**FiniteField.algEquivOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField`。
形式化陈述：algEquivOfCardEq (p : Nat) [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [
Algebra (ZMod p) K'] (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[ZMod p] K'
参数：p : Nat；ZMod p；ZMod p；hKK' : Fintype.card K = Fintype.card K'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)

--- 原说明 ---
Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly noncanonically) is
omorphic
-/
def algEquivOfCardEq (p : ℕ) [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
    (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[ZMod p] K' := by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK, hK'] at hKK'
  have hGalK := GaloisField.algEquivGaloisFieldOfFintype p n hK
  have hK'Gal := (GaloisField.algEquivGaloisFieldOfFintype p n' hK').symm
  rw [Nat.pow_right_injective h_prime.out.one_lt hKK'] at *
  exact AlgEquiv.trans hGalK hK'Gal

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly noncanonically) isomorphic -/
/-
**FiniteField.ringEquivOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField`。
形式化陈述：ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K'
参数：hKK' : Fintype.card K = Fintype.card K'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)

--- 原说明 ---
Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly noncanonically) is
omorphic
-/
def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    by_contra hne
    simpa [← hK, hK', hKK', hp'.ne_one] using Nat.coprime_pow_primes n n' hp hp' hne
  rw [← hpp'] at _char_p'_K'
  haveI := fact_iff.2 hp
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  letI : Algebra (ZMod p) K' := ZMod.algebra _ _
  exact ↑(algEquivOfCardEq p hKK')
/-
**FiniteField.pow_finrank_eq_natCard** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：pow_finrank_eq_natCard (p : Nat) [Fact p.Prime] (k : Type*) [AddCommGroup 
k] [Finite k] [Module (ZMod p) k] : p ^ Module.finrank (ZMod p) k = Nat.card k
参数：p : Nat；k : Type*；ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.natCard_eq_pow_finrank`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Module.Fini
te K V], Nat.card V…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
-/
theorem pow_finrank_eq_natCard (p : ℕ) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Finite k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Nat.card k := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
/-
**FiniteField.pow_finrank_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：pow_finrank_eq_card (p : Nat) [Fact p.Prime] (k : Type*) [AddCommGroup k] 
[Fintype k] [Module (ZMod p) k] : p ^ Module.finrank (ZMod p) k = Fintype.card k
参数：p : Nat；k : Type*；ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.pow_finrank_eq_natCard`：pow_finrank_eq_natCard (p : Nat) [Fa
ct p.Prime] (k : Type*) [AddCommGroup k] [Finite k] [Module (ZMod p) k] : p ^ Mo
dule.finrank (ZMod p) k …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
-/
theorem pow_finrank_eq_card (p : ℕ) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Fintype k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Fintype.card k := by
  rw [pow_finrank_eq_natCard, Fintype.card_eq_nat_card]

section
variable {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L] [Finite L]

/-
**FiniteField.nonempty_algHom_of_finrank_dvd** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFi
eld`。
形式化陈述：nonempty_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F 
L) : Nonempty (K ->ₐ[F] L)
参数：h : Module.finrank F K ∣ Module.finrank F L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Module.finite_of_finite`：∀ (R : Type u_1) {M : Type u_2} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite R]   [Modul
e.Finite R M]…
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `FiniteField.X_pow_card_sub_X_ne_zero`：X_pow_card_sub_X_ne_zero (hp : 1 <
 p) : (X ^ p - X : K'[X]) != 0
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.card_eq_pow_finrank`：∀ {K : Type u} {V : Type v} [inst : Division
Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : Finty
pe K] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `dvd_pow_pow_sub_self_of_dvd`：dvd_pow_pow_sub_self_of_dvd {r : R} {p a b 
: Nat} (h : a ∣ b) : r ^ p ^ a - r ∣ r ^ p ^ b - r
-/
theorem nonempty_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
    Nonempty (K →ₐ[F] L) := by
  have := Finite.of_injective _ (algebraMap F L).injective
  have := Fintype.ofFinite F
  have := Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos h Module.finrank_pos)
  have := Module.finite_of_finite F (M := K)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  refine ⟨Polynomial.IsSplittingField.lift _ (X ^ Fintype.card K - X) ?_⟩
  refine (FiniteField.isSplittingField_sub L F).splits.of_dvd ?_ ?_
  · exact map_ne_zero (FiniteField.X_pow_card_sub_X_ne_zero _ Fintype.one_lt_card)
  · rw [Module.card_eq_pow_finrank (K := F), Module.card_eq_pow_finrank (K := F) (V := L)]
    exact (map_dvd_map' _).mpr (dvd_pow_pow_sub_self_of_dvd h)
/-
**FiniteField.natCard_algHom_of_finrank_dvd** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFie
ld`。
形式化陈述：natCard_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L
) : Nat.card (K ->ₐ[F] L) = Module.finrank F K
参数：h : Module.finrank F K ∣ Module.finrank F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.nonempty_algHom_of_finrank_dvd`：nonempty_algHom_of_finrank_d
vd (h : Module.finrank F K ∣ Module.finrank F L) : Nonempty (K ->ₐ[F] L)
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `GaloisField.instIsGaloisOfFinite`：∀ {K : Type u_2} {K' : Type u_3} [inst
 : Field K] [inst_1 : Field K'] [Finite K'] [inst_3 : Algebra K K'], IsGalois K 
K'
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
-/
theorem natCard_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
    Nat.card (K →ₐ[F] L) = Module.finrank F K := by
  obtain ⟨f⟩ := nonempty_algHom_of_finrank_dvd h
  algebraize [f.toRingHom]
  have := Finite.of_injective _ (algebraMap K L).injective
  rw [Nat.card_congr (Normal.algHomEquivAut F L K), IsGalois.card_aut_eq_finrank]
/-
**FiniteField.card_algHom_of_finrank_dvd** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`
。
形式化陈述：card_algHom_of_finrank_dvd [Finite K] (h : Module.finrank F K ∣ Module.fin
rank F L) : Fintype.card (K ->ₐ[F] L) = Module.finrank F K
参数：h : Module.finrank F K ∣ Module.finrank F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `FiniteField.natCard_algHom_of_finrank_dvd`：natCard_algHom_of_finrank_dvd
 (h : Module.finrank F K ∣ Module.finrank F L) : Nat.card (K ->ₐ[F] L) = Module.
finrank F K
-/
theorem card_algHom_of_finrank_dvd [Finite K]
    (h : Module.finrank F K ∣ Module.finrank F L) :
    Fintype.card (K →ₐ[F] L) = Module.finrank F K := by
  rw [Fintype.card_eq_nat_card, natCard_algHom_of_finrank_dvd h]
/-
**FiniteField.nonempty_algHom_iff_finrank_dvd** 是 Mathlib 中的一个定理，位于命名空间 `FiniteF
ield`。
形式化陈述：nonempty_algHom_iff_finrank_dvd : Nonempty (K ->ₐ[F] L) ↔ Module.finrank F
 K ∣ Module.finrank F L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `FiniteField.nonempty_algHom_of_finrank_dvd`：nonempty_algHom_of_finrank_d
vd (h : Module.finrank F K ∣ Module.finrank F L) : Nonempty (K ->ₐ[F] L)
-/
theorem nonempty_algHom_iff_finrank_dvd :
    Nonempty (K →ₐ[F] L) ↔ Module.finrank F K ∣ Module.finrank F L := by
  refine ⟨fun ⟨f⟩ ↦ ?_, nonempty_algHom_of_finrank_dvd⟩
  algebraize [f.toRingHom]
  rw [← Module.finrank_mul_finrank F K L]
  exact dvd_mul_right _ _

end

end FiniteField

