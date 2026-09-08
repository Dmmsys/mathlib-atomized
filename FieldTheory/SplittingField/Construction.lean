/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `Polynomial.SplittingField f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `Polynomial.IsSplittingField.algEquiv`: Every splitting field of a polynomial `f` is isomorphic
  to `SplittingField f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `SplittingFieldAux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `SplittingField` is defined to be a quotient of a
`MvPolynomial` ring by the kernel of the obvious map into `SplittingFieldAux`. Because the
actual `SplittingField` will be a quotient of a `MvPolynomial`, it has nice instances on it.

-/

@[expose] public section

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

open scoped Classical in
/-- Non-computably choose an irreducible factor from a polynomial. -/
/-
**Polynomial.factor** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：factor (f : K[X]) : K[X]
参数：f : K[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-computably choose an irreducible factor from a polynomial.
-/
def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else X
/-
**Polynomial.irreducible_factor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_factor (f : K[X]) : Irreducible (factor f)
参数：f : K[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.factor.eq_1`：∀ {K : Type v} [inst : Field K] (f : Polynomial 
K),   f.factor = if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else 
Polynomial.X
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.irreducible_X`：irreducible_X : Irreducible (X : R[X])
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X

/-- See note [fact non-instances]. -/
/-
**Polynomial.fact_irreducible_factor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f))
参数：f : K[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.irreducible_factor`：irreducible_factor (f : K[X]) : Irreducib
le (factor f)

--- 原说明 ---
See note [fact non-instances].
-/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩

attribute [local instance] fact_irreducible_factor
/-
**Polynomial.factor_dvd_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f
参数：hf1 : ¬IsUnit f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Polynomial.factor.eq_1`：∀ {K : Type v} [inst : Field K] (f : Polynomial 
K),   f.factor = if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else 
Polynomial.X
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2
/-
**Polynomial.factor_dvd_of_degree_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree != 0) : factor f ∣ 
f
参数：hf : f.degree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.factor_dvd_of_not_isUnit`：factor_dvd_of_not_isUnit {f : K[X]}
 (hf1 : ¬IsUnit f) : factor f ∣ f
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_isUnit (mt degree_eq_zero_of_isUnit hf)
/-
**Polynomial.factor_dvd_of_natDegree_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：factor_dvd_of_natDegree_ne_zero {f : K[X]} (hf : f.natDegree != 0) : facto
r f ∣ f
参数：hf : f.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.factor_dvd_of_degree_ne_zero`：factor_dvd_of_degree_ne_zero {f
 : K[X]} (hf : f.degree != 0) : factor f ∣ f
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
-/
theorem factor_dvd_of_natDegree_ne_zero {f : K[X]} (hf : f.natDegree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt natDegree_eq_of_degree_eq_some hf)
/-
**Polynomial.isCoprime_iff_aeval_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isCoprime_iff_aeval_ne_zero (f g : K[X]) : IsCoprime f g ↔ forall {A : Typ
e v} [CommRing A] [IsDomain A] [Algebra K A] (a : A), aeval a f != 0 ∨ aeval a g
 != 0
参数：f g : K[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.aeval_ne_zero_of_isCoprime`：aeval_ne_zero_of_isCoprime {R} [C
ommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S] {p q : R[X]} (h : IsCop
rime p q) (s : S) : aeval s…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `isCoprime_of_dvd`：isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0)
) (H : forall z in nonunits R, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdjoinRoot.aeval_eq`：aeval_eq (p : R[X]) : aeval (root f) p = mk f p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `Polynomial.factor_dvd_of_not_isUnit`：factor_dvd_of_not_isUnit {f : K[X]}
 (hf1 : ¬IsUnit f) : factor f ∣ f
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isCoprime_iff_aeval_ne_zero (f g : K[X]) : IsCoprime f g ↔ ∀ {A : Type v} [CommRing A]
    [IsDomain A] [Algebra K A] (a : A), aeval a f ≠ 0 ∨ aeval a g ≠ 0 := by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hx _ => ?_⟩
  · replace h := @h K _ _ _ 0
    contrapose! h
    rw [h.left, h.right, map_zero, and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
    replace h := not_and_or.mpr <| h <| AdjoinRoot.root x.factor
    simp only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero,
      dvd_mul_of_dvd_left <| factor_dvd_of_not_isUnit hx, true_and, not_true] at h

/-- Divide a polynomial f by `X - C r` where `r` is a root of `f` in a bigger field extension. -/
/-
**Polynomial.removeFactor** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f)
参数：f : K[X]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))

--- 原说明 ---
Divide a polynomial f by `X - C r` where `r` is a root of `f` in a bigger field 
extension.
-/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))
/-
**Polynomial.X_sub_C_mul_removeFactor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_sub_C_mul_removeFactor (f : K[X]) (hf : f.natDegree != 0) : (X - C (Adjo
inRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f
参数：f : K[X]；hf : f.natDegree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
· 使用定理 `Polynomial.factor_dvd_of_natDegree_ne_zero`：factor_dvd_of_natDegree_ne_z
ero {f : K[X]} (hf : f.natDegree != 0) : factor f ∣ f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mul_divByMonic_eq_iff_isRoot`：mul_divByMonic_eq_iff_isRoot : 
(X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdjoinRoot.eval₂_root`：eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) =
 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem X_sub_C_mul_removeFactor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - C (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f := by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, zero_mul]
/-
**Polynomial.natDegree_removeFactor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree
 - 1
参数：f : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.removeFactor.eq_1`：∀ {K : Type v} [inst : Field K] (f : Polyn
omial K),   f.removeFactor = Polynomial.map (AdjoinRoot.of f.factor) f /ₘ (Polyn
omial.X - Polynomi…
· 使用定理 `Polynomial.natDegree_divByMonic`：natDegree_divByMonic (f : R[X]) {g : R[
X]} (hg : g.Monic) : natDegree (f /ₘ g) = natDegree f - natDegree g
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
-/
theorem natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [removeFactor, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_map, natDegree_X_sub_C]
/-
**Polynomial.natDegree_removeFactor'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_removeFactor' {f : K[X]} {n : Nat} (hfn : f.natDegree = n + 1) :
 f.removeFactor.natDegree = n
参数：hfn : f.natDegree = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_removeFactor`：natDegree_removeFactor (f : K[X]) : f
.removeFactor.natDegree = f.natDegree - 1
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
-/
theorem natDegree_removeFactor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) :
    f.removeFactor.natDegree = n := by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

It constructs the type, proves that is a field and algebra over the base field.

Uses recursion on the degree.
-/
/-
**Polynomial.SplittingFieldAuxAux** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：SplittingFieldAuxAux (n : Nat) : forall {K : Type u} [Field K], K[X] -> Σ 
(L : Type u) (_ : Field L), Algebra K L
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))

--- 原说明 ---
Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

It constructs the type, proves that is a field and algebra over the base field.

Uses recursion on the degree.
-/
def SplittingFieldAuxAux (n : ℕ) : ∀ {K : Type u} [Field K], K[X] →
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] →
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors. It is the type constructed in `SplittingFieldAuxAux`.
-/
/-
**Polynomial.SplittingFieldAux** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：SplittingFieldAux (n : Nat) {K : Type u} [Field K] (f : K[X]) : Type u
参数：n : Nat；f : K[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors. It is the type constructed in `SplittingFieldA
uxAux`.
-/
def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1
/-
**Polynomial.SplittingFieldAux.field** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Split
tingFieldAux`。
形式化陈述：(n : ℕ) → {K : Type u} → [inst : Field K] → (f : Polynomial K) → Field (Po
lynomial.SplittingFieldAux n f)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SplittingFieldAux.field (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Field (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.1
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Inhabited (SplittingFieldAux n f) :=
  ⟨0⟩
/-
**Polynomial.SplittingFieldAux.algebra** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Spl
ittingFieldAux`。
形式化陈述：(n : ℕ) → {K : Type u} → [inst : Field K] → (f : Polynomial K) → Algebra K
 (Polynomial.SplittingFieldAux n f)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SplittingFieldAux.algebra (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Algebra K (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.2

namespace SplittingFieldAux

/-
**Polynomial.SplittingFieldAux.succ** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splitt
ingFieldAux`。
形式化陈述：succ (n : Nat) (f : K[X]) : SplittingFieldAux (n + 1) f = SplittingFieldAu
x n f.removeFactor
参数：n : Nat；f : K[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ (n : ℕ) (f : K[X]) :
    SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl
/-
**Polynomial.SplittingFieldAux.algebra'''** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.
SplittingFieldAux`。
形式化陈述：algebra''' {n : Nat} {f : K[X]} : Algebra (AdjoinRoot f.factor) (Splitting
FieldAux n f.removeFactor)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
-/
instance algebra''' {n : ℕ} {f : K[X]} :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n _
/-
**Polynomial.SplittingFieldAux.algebra'** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Sp
littingFieldAux`。
形式化陈述：algebra' {n : Nat} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFi
eldAux n.succ f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra' {n : ℕ} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f) :=
  SplittingFieldAux.algebra'''
/-
**Polynomial.SplittingFieldAux.algebra''** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.S
plittingFieldAux`。
形式化陈述：algebra'' {n : Nat} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFa
ctor)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
-/
instance algebra'' {n : ℕ} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFactor) :=
  RingHom.toAlgebra (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor))
/-
**Polynomial.SplittingFieldAux.scalar_tower'** 是 Mathlib 中的一个实例，位于命名空间 `Polynomi
al.SplittingFieldAux`。
形式化陈述：scalar_tower' {n : Nat} {f : K[X]} : IsScalarTower K (AdjoinRoot f.factor)
 (SplittingFieldAux n f.removeFactor)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
-/
instance scalar_tower' {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
/-
**Polynomial.SplittingFieldAux.algebraMap_succ** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.SplittingFieldAux`。
形式化陈述：algebraMap_succ (n : Nat) (f : K[X]) : algebraMap K (SplittingFieldAux (n 
+ 1) f) = (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor)
).comp (AdjoinRoot.of f.factor)
参数：n : Nat；f : K[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_succ (n : ℕ) (f : K[X]) :
    algebraMap K (SplittingFieldAux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor)).comp
        (AdjoinRoot.of f.factor) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.SplittingFieldAux.splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Spli
ttingFieldAux`。
形式化陈述：∀ (n : ℕ) {K : Type u} [inst : Field K] (f : Polynomial K),   f.natDegree 
= n → (Polynomial.map (algebraMap K (Polynomial.SplittingFieldAux n f)) f).Split
s
参数：n : ℕ；f : Polynomial K；Polynomial.map (algebraMap K (Polynomial.SplittingFiel
dAux n f)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_degree_le_one`：∀ {R : Type u_1} [inst : DivisionSem
iring R] {f : Polynomial R}, f.degree ≤ 1 → f.Splits
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Polynomial.degree_map_le`：degree_map_le : degree (p.map f) <= degree p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.SplittingFieldAux.algebraMap_succ`：algebraMap_succ (n : Nat) 
(f : K[X]) : algebraMap K (SplittingFieldAux (n + 1) f) = (algebraMap (AdjoinRoo
t f.factor) (SplittingFieldAux n f…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.X_sub_C_mul_removeFactor`：X_sub_C_mul_removeFactor (f : K[X])
 (hf : f.natDegree != 0) : (X - C (AdjoinRoot.root f.factor)) * f.removeFactor =
 map (AdjoinRoot.of f.fac…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits
· 使用定理 `Polynomial.natDegree_removeFactor'`：natDegree_removeFactor' {f : K[X]} {
n : Nat} (hfn : f.natDegree = n + 1) : f.removeFactor.natDegree = n
-/
protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f)) :=
  Nat.recOn (motive := fun n => ∀ {K : Type u} [Field K], ∀ (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f))) n
    (fun {_} _ _ hf =>
      Splits.of_degree_le_one <| degree_map_le.trans
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    rw [algebraMap_succ, ← map_map,
      ← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    rw [Polynomial.map_mul]
    exact Splits.mul ((Splits.X_sub_C _).map _) (ih _ (natDegree_removeFactor' hf))

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.SplittingFieldAux.adjoin_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.SplittingFieldAux`。
形式化陈述：adjoin_rootSet (n : Nat) : forall {K : Type u} [Field K], forall (f : K[X]
) (_hfn : f.natDegree = n), Algebra.adjoin K (f.rootSet (SplittingFieldAux n f))
 = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `Subalgebra.range_le`：range_le : Set.range (algebraMap R A) <= S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.fact_irreducible_factor`：fact_irreducible_factor (f : K[X]) :
 Fact (Irreducible (factor f))
· 使用定理 `Polynomial.SplittingFieldAux.algebraMap_succ`：algebraMap_succ (n : Nat) 
(f : K[X]) : algebraMap K (SplittingFieldAux (n + 1) f) = (algebraMap (AdjoinRoo
t f.factor) (SplittingFieldAux n f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.X_sub_C_mul_removeFactor`：X_sub_C_mul_removeFactor (f : K[X])
 (hf : f.natDegree != 0) : (X - C (AdjoinRoot.root f.factor)) * f.removeFactor =
 map (AdjoinRoot.of f.fac…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Multiset.toFinset_add`：toFinset_add (s t : Multiset α) : (s + t).toFinse
t = s.toFinset union t.toFinset
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
（共 34 条，此处仅展示前 30 条）
-/
theorem adjoin_rootSet (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤ :=
  Nat.recOn (motive := fun n =>
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {_} _ _ _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree ≠ 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    classical
    rw [rootSet_def, aroots_def]
    rw [algebraMap_succ, ← map_map, ← X_sub_C_mul_removeFactor _ hndf, Polynomial.map_mul] at hmf0 ⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton, ← Set.image_singleton]
    simp only [SplittingFieldAux.succ]
    rw [← Algebra.adjoin_eq_adjoin_union K {AdjoinRoot.root f.factor}
      ((map (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor))
        f.removeFactor).roots.toFinset : Set (SplittingFieldAux n f.removeFactor))
      AdjoinRoot.adjoinRoot_eq_top, ← rootSet_def, ih _ (natDegree_removeFactor' hfn),
      Subalgebra.restrictScalars_top]
/-
**Polynomial.SplittingFieldAux.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.SplittingF
ieldAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : K[X]) : IsSplittingField K (SplittingFieldAux f.natDegree f) f :=
  ⟨SplittingFieldAux.splits _ _ rfl, SplittingFieldAux.adjoin_rootSet _ _ rfl⟩

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
@[stacks 09HV "The construction of the splitting field."]
/-
**Polynomial.SplittingField** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：SplittingField (f : K[X])
参数：f : K[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A splitting field of a polynomial.
-/
def SplittingField (f : K[X]) :=
  MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
deriving Inhabited

namespace SplittingField

variable (f : K[X])

variable {S : Type*} [DistribSMul S K] [IsScalarTower S K K] in
deriving instance SMul S for SplittingField f

/-
**Polynomial.SplittingField.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.SplittingFiel
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (SplittingField f) := inferInstanceAs <| CommRing (_ ⧸ _)

variable {R : Type*} [CommSemiring R] [Algebra R K] in
deriving instance Algebra R, IsScalarTower R K for SplittingField f
/-
**Polynomial.SplittingField.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.SplittingFiel
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra K f.SplittingField := inferInstance

/-- The algebra equivalence with `SplittingFieldAux`,
which we will use to construct the field structure. -/
/-
**Polynomial.SplittingField.algEquivSplittingFieldAux** 是 Mathlib 中的一个定义，位于命名空间 
`Polynomial.SplittingField`。
形式化陈述：algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFie
ldAux f.natDegree f
参数：f : K[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence with `SplittingFieldAux`,
which we will use to construct the field structure.
-/
def algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFieldAux f.natDegree f :=
  Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩
/-
**Polynomial.SplittingField.instGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Polynom
ial.SplittingField`。
形式化陈述：instGroupWithZero : GroupWithZero (SplittingField f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupWithZero : GroupWithZero (SplittingField f) :=
  let e := algEquivSplittingFieldAux f
  { inv := fun a ↦ e.symm (e a)⁻¹
    inv_zero := by simp
    mul_inv_cancel := fun a ha ↦ e.injective <| by simp [EmbeddingLike.map_ne_zero_iff.2 ha]
    __ := e.surjective.nontrivial }
/-
**Polynomial.SplittingField.instField** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Spli
ttingField`。
形式化陈述：instField : Field (SplittingField f) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField : Field (SplittingField f) where
  __ := (inferInstance : CommRing (SplittingField f))
  __ := instGroupWithZero f
  nnratCast q := algebraMap K _ q
  ratCast q := algebraMap K _ q
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by change algebraMap K _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  nnqsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]
/-
**Polynomial.SplittingField.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.S
plittingField`。
形式化陈述：instCharZero [CharZero K] : CharZero (SplittingField f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_injective_algebraMap`：charZero_of_injective_algebraMap [Comm
Semiring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A))
 [CharZero R] : CharZe…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance instCharZero [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective
/-
**Polynomial.SplittingField.instCharP** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Spli
ttingField`。
形式化陈述：instCharP (p : Nat) [CharP K p] : CharP (SplittingField f) p
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_algebraMap`：charP_of_injective_algebraMap [CommSemiri
ng R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (p : 
Nat) [CharP R p] : …
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance instCharP (p : ℕ) [CharP K p] : CharP (SplittingField f) p :=
  charP_of_injective_algebraMap (algebraMap K _).injective p
/-
**Polynomial.SplittingField.instExpChar** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Sp
littingField`。
形式化陈述：instExpChar (p : Nat) [ExpChar K p] : ExpChar (SplittingField f) p
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance instExpChar (p : ℕ) [ExpChar K p] : ExpChar (SplittingField f) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p
/-
**Polynomial.SplittingField._root_.Polynomial.IsSplittingField.splittingField** 
是 Mathlib 中的一个实例，位于命名空间 `Polynomial.SplittingField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm

@[stacks 09HU "Splitting part"]
/-
**Polynomial.SplittingField.splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splitti
ngField`。
形式化陈述：∀ {K : Type v} [inst : Field K] (f : Polynomial K), (Polynomial.map (algeb
raMap K f.SplittingField) f).Splits
参数：f : Polynomial K；Polynomial.map (algebraMap K f.SplittingField) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f
-/
protected theorem splits : Splits (f.map (algebraMap K (SplittingField f))) :=
  IsSplittingField.splits f.SplittingField f

variable [Algebra K L] (hb : Splits (f.map (algebraMap K L)))

/-- Embeds the splitting field into any other field that splits the polynomial. -/
/-
**Polynomial.SplittingField.lift** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Splitting
Field`。
形式化陈述：lift : SplittingField f ->ₐ[K] L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f

--- 原说明 ---
Embeds the splitting field into any other field that splits the polynomial.
-/
def lift : SplittingField f →ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb
/-
**Polynomial.SplittingField.adjoin_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.SplittingField`。
形式化陈述：adjoin_rootSet : Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f
-/
theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤ :=
  Polynomial.IsSplittingField.adjoin_rootSet _ f

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L)
variable [Algebra K L]
variable {K}

/-
**Polynomial.IsSplittingField.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.IsSplitting
Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f
/-
**Polynomial.IsSplittingField.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.IsSplitting
Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite K] (f : K[X]) : Finite f.SplittingField :=
  Module.finite_of_finite K
/-
**Polynomial.IsSplittingField.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.IsSplitting
Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : K[X]) : Module.IsTorsionFree K f.SplittingField :=
  inferInstance

/-- Any splitting field is isomorphic to `SplittingFieldAux f`. -/
/-
**Polynomial.IsSplittingField.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.IsS
plittingField`。
形式化陈述：algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField 
f
参数：f : K[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any splitting field is isomorphic to `SplittingFieldAux f`.
-/
def algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
  AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f) <|
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1

end IsSplittingField

end Polynomial

