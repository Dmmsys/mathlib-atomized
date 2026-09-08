/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Minimal polynomial of roots of unity

We gather several results about minimal polynomial of root of unity.

## Main results

* `IsPrimitiveRoot.totient_le_degree_minpoly`: The degree of the minimal polynomial of an `n`-th
  primitive root of unity is at least `totient n`.

-/

public section


open minpoly Polynomial

open scoped Polynomial

namespace IsPrimitiveRoot

section CommRing

variable {n : ℕ} {K : Type*} [CommRing K] {μ : K} (h : IsPrimitiveRoot μ n)
include h

/-- `μ` is integral over `ℤ`. -/
/-
**IsPrimitiveRoot.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：isIntegral (hpos : 0 < n) : IsIntegral Int μ
参数：hpos : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPrimitiveRoot.iff_def`：∀ {M : Type u_1} [inst : CommMonoid M] (ζ : M) 
(k : ℕ), IsPrimitiveRoot ζ k ↔ ζ ^ k = 1 ∧ ∀ (l : ℕ), ζ ^ l = 1 → k ∣ l
· 使用定理 `Polynomial.eval₂_one`：eval₂_one : (1 : R[X]).eval₂ f x = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`μ` is integral over `ℤ`.
-/
theorem isIntegral (hpos : 0 < n) : IsIntegral ℤ μ := by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (ne_of_lt hpos).symm
  · simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self]

section IsDomain

variable [IsDomain K] [CharZero K]

/-- The minimal polynomial of a root of unity `μ` divides `X ^ n - 1`. -/
/-
**IsPrimitiveRoot.minpoly_dvd_x_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：minpoly_dvd_x_pow_sub_one : minpoly Int μ ∣ X ^ n - 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `GCDMonoid.toIsIntegrallyClosed`：∀ {R : Type u_1} [inst : CommRing R] [h 
: IsGCDMonoid R], IsIntegrallyClosed R
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
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
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The minimal polynomial of a root of unity `μ` divides `X ^ n - 1`.
-/
theorem minpoly_dvd_x_pow_sub_one : minpoly ℤ μ ∣ X ^ n - 1 := by
  rcases n.eq_zero_or_pos with (rfl | h0)
  · simp
  apply minpoly.isIntegrallyClosed_dvd (isIntegral h h0)
  simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, aeval_X_pow,
    aeval_one, map_sub, sub_self]

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is separable. -/
/-
**IsPrimitiveRoot.separable_minpoly_mod** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRo
ot`。
形式化陈述：separable_minpoly_mod {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n) : Separable
 (map (Int.castRingHom (ZMod p)) (minpoly Int μ))
参数：hdiv : ¬p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsPrimitiveRoot.minpoly_dvd_x_pow_sub_one`：minpoly_dvd_x_pow_sub_one : m
inpoly Int μ ∣ X ^ n - 1
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `Polynomial.separable_X_pow_sub_C`：separable_X_pow_sub_C {n : Nat} (a : F
) (hn : (n : F) != 0) (ha : a != 0) : Separable (X ^ n - C a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.natCast_eq_zero_iff`：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b)
 = 0 ↔ b ∣ a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)

--- 原说明 ---
The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is sep
arable.
-/
theorem separable_minpoly_mod {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Separable (map (Int.castRingHom (ZMod p)) (minpoly ℤ μ)) := by
  have hdvd : map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣ X ^ n - 1 := by
    convert! _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) (minpoly_dvd_x_pow_sub_one h)
    simp only [map_sub, map_pow, coe_mapRingHom, map_X, map_one]
  refine Separable.of_dvd (separable_X_pow_sub_C 1 ?_ one_ne_zero) hdvd
  by_contra hzero
  exact hdiv ((ZMod.natCast_eq_zero_iff n p).1 hzero)

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is squarefree. -/
/-
**IsPrimitiveRoot.squarefree_minpoly_mod** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveR
oot`。
形式化陈述：squarefree_minpoly_mod {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n) : Squarefr
ee (map (Int.castRingHom (ZMod p)) (minpoly Int μ))
参数：hdiv : ¬p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.squarefree`：∀ {R : Type u} [inst : CommSemiring R] 
{p : Polynomial R}, p.Separable → Squarefree p
· 使用定理 `IsPrimitiveRoot.separable_minpoly_mod`：separable_minpoly_mod {p : Nat} [
Fact p.Prime] (hdiv : ¬p ∣ n) : Separable (map (Int.castRingHom (ZMod p)) (minpo
ly Int μ))

--- 原说明 ---
The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is squ
arefree.
-/
theorem squarefree_minpoly_mod {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Squarefree (map (Int.castRingHom (ZMod p)) (minpoly ℤ μ)) :=
  (separable_minpoly_mod h hdiv).squarefree

/-- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a natural number that does not divide `n`. Then `P` divides `expand ℤ p Q`. -/
/-
**IsPrimitiveRoot.minpoly_dvd_expand** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`
。
形式化陈述：minpoly_dvd_expand {p : Nat} (hdiv : ¬p ∣ n) : minpoly Int μ ∣ expand Int 
p (minpoly Int (μ ^ p))
参数：hdiv : ¬p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GCDMonoid.toIsIntegrallyClosed`：∀ {R : Type u_1} [inst : CommRing R] [h 
: IsGCDMonoid R], IsIntegrallyClosed R
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.coe_expand`：coe_expand : (expand R p : R[X] -> R[X]) = eval₂ 
C (X ^ p)
· 使用定理 `Polynomial.comp.eq_1`：∀ {R : Type u} [inst : Semiring R] (p q : Polynomi
al R), p.comp q = Polynomial.eval₂ Polynomial.C q p
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0

--- 原说明 ---
Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal 
polynomial of
`μ ^ p`, where `p` is a natural number that does not divide `n`. Then `P` divide
s `expand ℤ p Q`.
-/
theorem minpoly_dvd_expand {p : ℕ} (hdiv : ¬p ∣ n) :
    minpoly ℤ μ ∣ expand ℤ p (minpoly ℤ (μ ^ p)) := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp_all
  let : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  refine minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos) ?_
  rw [aeval_def, coe_expand, ← comp, eval₂_eq_eval_map, map_comp, Polynomial.map_pow, map_X,
    eval_comp, eval_X_pow, ← eval₂_eq_eval_map, ← aeval_def]
  exact minpoly.aeval _ _

/-- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q ^ p` modulo `p`. -/
/-
**IsPrimitiveRoot.minpoly_dvd_pow_mod** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot
`。
形式化陈述：minpoly_dvd_pow_mod {p : Nat} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) : ma
p (Int.castRingHom (ZMod p)) (minpoly Int μ) ∣ map (Int.castRingHom (ZMod p)) (m
inpoly Int (μ ^ p)) ^ p
参数：hdiv : ¬p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.expand_card`：expand_card (f : Polynomial (ZMod p)) : expand (ZMod p
) p f = f ^ p
· 使用定理 `Polynomial.map_expand`：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : 
map f (expand R p q) = expand S p (map f q)
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsPrimitiveRoot.minpoly_dvd_expand`：minpoly_dvd_expand {p : Nat} (hdiv :
 ¬p ∣ n) : minpoly Int μ ∣ expand Int p (minpoly Int (μ ^ p))

--- 原说明 ---
Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal 
polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q ^ p`
 modulo `p`.
-/
theorem minpoly_dvd_pow_mod {p : ℕ} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly ℤ (μ ^ p)) ^ p := by
  set Q := minpoly ℤ (μ ^ p)
  have hfrob :
    map (Int.castRingHom (ZMod p)) Q ^ p = map (Int.castRingHom (ZMod p)) (expand ℤ p Q) := by
    rw [← ZMod.expand_card, map_expand]
  rw [hfrob]
  apply _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
  exact minpoly_dvd_expand h hdiv

/-- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q` modulo `p`. -/
/-
**IsPrimitiveRoot.minpoly_dvd_mod_p** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：minpoly_dvd_mod_p {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n) : map (Int.cast
RingHom (ZMod p)) (minpoly Int μ) ∣ map (Int.castRingHom (ZMod p)) (minpoly Int 
(μ ^ p))
参数：hdiv : ¬p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.isRadical`：Squarefree.isRadical {x : R} (hx : Squarefree x) :
 IsRadical x
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsPrimitiveRoot.squarefree_minpoly_mod`：squarefree_minpoly_mod {p : Nat}
 [Fact p.Prime] (hdiv : ¬p ∣ n) : Squarefree (map (Int.castRingHom (ZMod p)) (mi
npoly Int μ))
· 使用定理 `IsPrimitiveRoot.minpoly_dvd_pow_mod`：minpoly_dvd_pow_mod {p : Nat} [hpri
me : Fact p.Prime] (hdiv : ¬p ∣ n) : map (Int.castRingHom (ZMod p)) (minpoly Int
 μ) ∣ map (Int.castRingHo…

--- 原说明 ---
Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal 
polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q` mod
ulo `p`.
-/
theorem minpoly_dvd_mod_p {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly ℤ (μ ^ p)) :=
  (squarefree_minpoly_mod h hdiv).isRadical _ _ (minpoly_dvd_pow_mod h hdiv)

/-- If `p` is a prime that does not divide `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ p` are the same. -/
/-
**IsPrimitiveRoot.minpoly_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：minpoly_eq_pow {p : Nat} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) : minpoly
 Int μ = minpoly Int (μ ^ p)
参数：hdiv : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `IsPrimitiveRoot.pow_of_prime`：pow_of_prime (h : IsPrimitiveRoot ζ k) {p 
: Nat} (hprime : Nat.Prime p) (hdiv : ¬p ∣ k) : IsPrimitiveRoot (ζ ^ p) k
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Polynomial.IsPrimitive.mul`：∀ {R : Type u_1} [inst : CommRing R] [Normal
izedGCDMonoid R] {p q : Polynomial R},   p.IsPrimitive → q.IsPrimitive → (p * q)
.IsPrimitive
· 使用定理 `Polynomial.Monic.isPrimitive`：∀ {R : Type u_1} [inst : CommSemiring R] {
p : Polynomial R}, p.Monic → p.IsPrimitive
· 使用定理 `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`：∀ (p q : Polyn
omial ℤ),   p.IsPrimitive → (p ∣ q ↔ Polynomial.map (Int.castRingHom ℚ) p ∣ Poly
nomial.map (Int.castRingHom ℚ) q)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `IsCoprime.mul_dvd`：IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H
2 : y ∣ z) : x * y ∣ z
· 使用定理 `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`：∀ {p : 
Polynomial ℤ}, p.IsPrimitive → (Irreducible p ↔ Irreducible (Polynomial.map (Int
.castRingHom ℚ) p))
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `dvd_or_isCoprime`：dvd_or_isCoprime (x y : R) (h : Irreducible x) : x ∣ y
 ∨ IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.map_dvd_map`：map_dvd_map [Ring S] (f : R ->+* S) (hf : Functi
on.Injective f) {x y : R[X]} (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Polynomial.eq_of_monic_of_associated`：eq_of_monic_of_associated (hp : p.
Monic) (hq : q.Monic) (hpq : Associated p q) : p = q
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a prime that does not divide `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ p` are the same.
-/
theorem minpoly_eq_pow {p : ℕ} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    minpoly ℤ μ = minpoly ℤ (μ ^ p) := by
  by_cases hn : n = 0
  · simp_all
  have hpos := Nat.pos_of_ne_zero hn
  by_contra hdiff
  set P := minpoly ℤ μ
  set Q := minpoly ℤ (μ ^ p)
  have Pmonic : P.Monic := minpoly.monic (h.isIntegral hpos)
  have Qmonic : Q.Monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)
  have Pirr : Irreducible P := minpoly.irreducible (h.isIntegral hpos)
  have Qirr : Irreducible Q := minpoly.irreducible ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)
  have PQprim : IsPrimitive (P * Q) := Pmonic.isPrimitive.mul Qmonic.isPrimitive
  have prod : P * Q ∣ X ^ n - 1 := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (P * Q) (X ^ n - 1) PQprim,
      Polynomial.map_mul]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · have aux := IsPrimitive.Int.irreducible_iff_irreducible_map_cast Pmonic.isPrimitive
      refine (dvd_or_isCoprime _ _ (aux.1 Pirr)).resolve_left ?_
      rw [map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Pmonic]
      intro hdiv
      refine hdiff (eq_of_monic_of_associated Pmonic Qmonic ?_)
      exact associated_of_dvd_dvd hdiv (Pirr.dvd_symm Qirr hdiv)
    · apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Pmonic).2
      exact minpoly_dvd_x_pow_sub_one h
    · apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Qmonic).2
      exact minpoly_dvd_x_pow_sub_one (pow_of_prime h hprime.1 hdiv)
  replace prod := _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) prod
  rw [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, map_X] at prod
  obtain ⟨R, hR⟩ := minpoly_dvd_mod_p h hdiv
  rw [hR, ← mul_assoc, ← Polynomial.map_mul, ← sq, Polynomial.map_pow] at prod
  have habs : map (Int.castRingHom (ZMod p)) P ^ 2 ∣ map (Int.castRingHom (ZMod p)) P ^ 2 * R := by
    use R
  replace habs :=
    lt_of_lt_of_le (Nat.cast_lt.2 one_lt_two)
      (le_emultiplicity_of_pow_dvd (dvd_trans habs prod))
  have hfree : Squarefree (X ^ n - 1 : (ZMod p)[X]) :=
    (separable_X_pow_sub_C 1 (fun h => hdiv <| (ZMod.natCast_eq_zero_iff n p).1 h)
        one_ne_zero).squarefree
  rcases (squarefree_iff_emultiplicity_le_one (X ^ n - 1)).1 hfree
      (map (Int.castRingHom (ZMod p)) P) with hle | hunit
  · rw [Nat.cast_one] at habs; exact hle.not_gt habs
  · replace hunit := degree_eq_zero_of_isUnit hunit
    rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom (ZMod p)) _] at hunit
    · exact (minpoly.degree_pos (isIntegral h hpos)).ne' hunit
    simp only [Pmonic, eq_intCast, Monic.leadingCoeff, Int.cast_one, Ne, not_false_iff,
      one_ne_zero]

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ m` are the same. -/
/-
**IsPrimitiveRoot.minpoly_eq_pow_coprime** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveR
oot`。
形式化陈述：minpoly_eq_pow_coprime {m : Nat} (hcop : Nat.Coprime m n) : minpoly Int μ 
= minpoly Int (μ ^ m)
参数：hcop : Nat.Coprime m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.induction_on_prime`：induction_on_prime {P : α 
-> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, IsUnit x -> P x) (h₃ : forall a 
p : α, a != 0 -> Prime p -> P a ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.Coprime.coprime_mul_left`：∀ {k m n : ℕ}, (k * m).Coprime n → m.Copri
me n
· 使用定理 `Prime.nat_prime`：∀ {p : ℕ}, Prime p → Nat.Prime p
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.Coprime.coprime_mul_right`：∀ {m k n : ℕ}, (m * k).Coprime n → m.Copr
ime n
· 使用定理 `IsPrimitiveRoot.minpoly_eq_pow`：minpoly_eq_pow {p : Nat} [hprime : Fact 
p.Prime] (hdiv : ¬p ∣ n) : minpoly Int μ = minpoly Int (μ ^ p)
· 使用定理 `IsPrimitiveRoot.pow_of_coprime`：pow_of_coprime (h : IsPrimitiveRoot ζ k)
 (i : Nat) (hi : i.Coprime k) : IsPrimitiveRoot (ζ ^ i) k
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `m : ℕ` is coprime with `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ m` are the same.
-/
theorem minpoly_eq_pow_coprime {m : ℕ} (hcop : Nat.Coprime m n) :
    minpoly ℤ μ = minpoly ℤ (μ ^ m) := by
  revert n hcop
  refine UniqueFactorizationMonoid.induction_on_prime m ?_ ?_ ?_
  · intro h hn
    congr
    simpa [(Nat.coprime_zero_left _).mp hn] using h
  · intro u hunit _ _
    congr
    simp [Nat.isUnit_iff.mp hunit]
  · intro a p _ hprime hind h hcop
    rw [hind h (Nat.Coprime.coprime_mul_left hcop)]; clear hind
    replace hprime := hprime.nat_prime
    have hdiv := (Nat.Prime.coprime_iff_not_dvd hprime).1 (Nat.Coprime.coprime_mul_right hcop)
    have := Fact.mk hprime
    rw [minpoly_eq_pow (h.pow_of_coprime a (Nat.Coprime.coprime_mul_left hcop)) hdiv]
    congr 1
    ring

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomial of a primitive `n`-th root of unity `μ`
has `μ ^ m` as root. -/
/-
**IsPrimitiveRoot.pow_isRoot_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`
。
形式化陈述：pow_isRoot_minpoly {m : Nat} (hcop : Nat.Coprime m n) : IsRoot (map (Int.c
astRingHom K) (minpoly Int μ)) (μ ^ m)
参数：hcop : Nat.Coprime m n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.minpoly_eq_pow_coprime`：minpoly_eq_pow_coprime {m : Nat}
 (hcop : Nat.Coprime m n) : minpoly Int μ = minpoly Int (μ ^ m)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0

--- 原说明 ---
If `m : ℕ` is coprime with `n`,
then the minimal polynomial of a primitive `n`-th root of unity `μ`
has `μ ^ m` as root.
-/
theorem pow_isRoot_minpoly {m : ℕ} (hcop : Nat.Coprime m n) :
    IsRoot (map (Int.castRingHom K) (minpoly ℤ μ)) (μ ^ m) := by
  simp only [minpoly_eq_pow_coprime h hcop, IsRoot.def, eval_map]
  exact minpoly.aeval ℤ (μ ^ m)

/-- `primitiveRoots n K` is a subset of the roots of the minimal polynomial of a primitive
`n`-th root of unity `μ`. -/
/-
**IsPrimitiveRoot.is_roots_of_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot
`。
形式化陈述：is_roots_of_minpoly [DecidableEq K] : primitiveRoots n K subseteq (map (In
t.castRingHom K) (minpoly Int μ)).roots.toFinset
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `primitiveRoots.congr_simp`：∀ (k k_1 : ℕ),   k = k_1 → ∀ (R : Type u_7) [
inst : CommRing R] [inst_1 : IsDomain R], primitiveRoots k R = primitiveRoots k_
1 R
· 使用定理 `primitiveRoots_zero`：primitiveRoots_zero : primitiveRoots 0 R = ∅
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPrimitiveRoot.isPrimitiveRoot_iff`：isPrimitiveRoot_iff {k : Nat} [NeZe
ro k] {ζ ξ : R} (h : IsPrimitiveRoot ζ k) : IsPrimitiveRoot ξ k ↔ exists i < k, 
i.Coprime k ∧ ζ ^ i = ξ
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.map_monic_ne_zero`：map_monic_ne_zero (hp : p.Monic) [Nontrivi
al S] : p.map f != 0
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsPrimitiveRoot.pow_isRoot_minpoly`：pow_isRoot_minpoly {m : Nat} (hcop :
 Nat.Coprime m n) : IsRoot (map (Int.castRingHom K) (minpoly Int μ)) (μ ^ m)

--- 原说明 ---
`primitiveRoots n K` is a subset of the roots of the minimal polynomial of a pri
mitive
`n`-th root of unity `μ`.
-/
theorem is_roots_of_minpoly [DecidableEq K] :
    primitiveRoots n K ⊆ (map (Int.castRingHom K) (minpoly ℤ μ)).roots.toFinset := by
  by_cases hn : n = 0; · simp_all
  have : NeZero n := ⟨hn⟩
  have hpos := Nat.pos_of_ne_zero hn
  intro x hx
  obtain ⟨m, _, hcop, rfl⟩ := (isPrimitiveRoot_iff h).1 ((mem_primitiveRoots hpos).1 hx)
  simp only [Multiset.mem_toFinset]
  convert! pow_isRoot_minpoly h hcop using 0
  rw [← mem_roots]
  exact map_monic_ne_zero <| minpoly.monic <| isIntegral h hpos

/-- The degree of the minimal polynomial of `μ` is at least `totient n`. -/
/-
**IsPrimitiveRoot.totient_le_degree_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：totient_le_degree_minpoly : Nat.totient n <= (minpoly Int μ).natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.card_primitiveRoots`：card_primitiveRoots {ζ : R} {k : Na
t} (h : IsPrimitiveRoot ζ k) : #(primitiveRoots k R) = φ k
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `IsPrimitiveRoot.is_roots_of_minpoly`：is_roots_of_minpoly [DecidableEq K]
 : primitiveRoots n K subseteq (map (Int.castRingHom K) (minpoly Int μ)).roots.t
oFinset
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
· 使用定理 `Polynomial.card_roots'`：card_roots' (p : R[X]) : Multiset.card p.roots <
= natDegree p
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p

--- 原说明 ---
The degree of the minimal polynomial of `μ` is at least `totient n`.
-/
theorem totient_le_degree_minpoly : Nat.totient n ≤ (minpoly ℤ μ).natDegree := by
  classical
  let P : ℤ[X] := minpoly ℤ μ
  -- minimal polynomial of `μ`
  let P_K : K[X] := map (Int.castRingHom K) P
  -- minimal polynomial of `μ` sent to `K[X]`
  calc
    n.totient = (primitiveRoots n K).card := h.card_primitiveRoots.symm
    _ ≤ P_K.roots.toFinset.card := Finset.card_le_card (is_roots_of_minpoly h)
    _ ≤ Multiset.card P_K.roots := Multiset.toFinset_card_le _
    _ ≤ P_K.natDegree := card_roots' _
    _ ≤ P.natDegree := natDegree_map_le

end IsDomain

end CommRing

end IsPrimitiveRoot

