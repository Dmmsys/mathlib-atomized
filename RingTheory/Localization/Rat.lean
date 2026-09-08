/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Localization.NumDen

/-!
# Ring-theoretic fractions in `ℚ`
-/

public section

namespace Rat

open IsFractionRing

/-
**Rat.isLocalizationIsInteger_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isLocalizationIsInteger_iff (q : Rat) : IsLocalization.IsInteger Int q ↔ q
 in Set.range Int.cast
参数：q : Rat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLocalizationIsInteger_iff (q : ℚ) :
    IsLocalization.IsInteger ℤ q ↔ q ∈ Set.range Int.cast := by
  simp [IsLocalization.IsInteger]
/-
**Rat.associated_num_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：associated_num_den (q : Rat) : Associated (IsFractionRing.num Int q) q.num
 ∧ Associated (IsFractionRing.den Int q : Int) q.den
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.num_den_unique`：num_den_unique (x : K) (n : A) (d : nonZe
roDivisors A) (pr : IsRelPrime n d) (h : IsLocalization.mk' K n d = x) : Associa
ted (num A x) n ∧ A…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associated_num_den (q : ℚ) :
    Associated (IsFractionRing.num ℤ q) q.num ∧ Associated (IsFractionRing.den ℤ q : ℤ) q.den :=
  num_den_unique ℤ q q.num ⟨q.den, by simp⟩
    (by simpa [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] using q.reduced)
    (by simp [Rat.num_div_den])
/-
**Rat.isFractionRingDen** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isFractionRingDen (q : Rat) : (IsFractionRing.den Int q : Int).natAbs = q.
den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Rat.associated_num_den`：associated_num_den (q : Rat) : Associated (IsFra
ctionRing.num Int q) q.num ∧ Associated (IsFractionRing.den Int q : Int) q.den
-/
theorem isFractionRingDen (q : ℚ) : (IsFractionRing.den ℤ q : ℤ).natAbs = q.den := by
  simpa [Int.associated_iff_natAbs] using q.associated_num_den.2
/-
**Rat.isFractionRingNum** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isFractionRingNum (q : Rat) : Associated (IsFractionRing.num Int q : Int) 
q.num
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Rat.associated_num_den`：associated_num_den (q : Rat) : Associated (IsFra
ctionRing.num Int q) q.num ∧ Associated (IsFractionRing.den Int q : Int) q.den
-/
theorem isFractionRingNum (q : ℚ) : Associated (IsFractionRing.num ℤ q : ℤ) q.num :=
  q.associated_num_den.1

end Rat

