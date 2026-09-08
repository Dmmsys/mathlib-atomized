/-
Copyright (c) 2025 María Inés de Frutos-Fernández & Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.FieldTheory.Finite.Valuation
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Ostrowski's theorem for `K(X)`

This file proves Ostrowski's theorem for the field of rational functions `K(X)`, where `K` is any
field: if `v` is a discrete valuation on `K(X)` which is trivial on elements of `K`, then `v` is
equivalent to either the `I`-adic valuation for some `I : HeightOneSpectrum K[X]`, or to the
valuation at infinity `FunctionField.inftyValuation K`.

## Main results
- `RatFunc.valuation_isEquiv_infty_or_adic`: Ostrowski's theorem for `K(X)`.
-/

@[expose] public noncomputable section


open Multiplicative WithZero

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation (RatFunc K) Γ}

namespace RatFunc

section Infinity

open Polynomial Valuation

/-
**RatFunc.valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X** 是 Math
lib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X {f : RatFunc
 K} [v.IsTrivialOn K] (hlt : 1 < v X) (hf : f != 0) : v f = v RatFunc.X ^ f.intD
egree
参数：hlt : 1 < v X；hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RatFunc.intDegree_div`：intDegree_div {x y : RatFunc K} (hx : x != 0) (hy
 : y != 0) : (x / y).intDegree = x.intDegree - y.intDegree
· 使用定理 `Valuation.map_div`：map_div {R : Type*} [DivisionRing R] (v : Valuation R
 Γ₀) : forall x y, v (x / y) = v x / v y
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.intDegree_polynomial`：intDegree_polynomial {p : K[X]} : intDegre
e (algebraMap K[X] K⟮X⟯ p) = natDegree p
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`
：valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (hlt : 1 < v RatFu
nc.X) {p : K[X]} (hp : p != 0) : v p = v RatFunc.X ^ p.natDeg…
-/
lemma valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X {f : RatFunc K}
    [v.IsTrivialOn K] (hlt : 1 < v X) (hf : f ≠ 0) : v f = v RatFunc.X ^ f.intDegree := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [intDegree_div (by grind only) (by grind only), v.map_div, zpow_sub₀ (ne_zero_of_lt hlt)]
    simp_rw [intDegree_polynomial, zpow_natCast, ← coePolynomial_eq_algebraMap]
    have hp : p ≠ 0 := by contrapose hf; simp [hf]
    rw [valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt hp,
      valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt hq]

variable [DecidableEq (RatFunc K)]
/-
**RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X** 是 Mathlib 中的一
个引理，位于命名空间 `RatFunc`。
形式化陈述：valuation_isEquiv_inftyValuation_of_one_lt_valuation_X [v.IsTrivialOn K] (
hlt : 1 < v X) : v.IsEquiv (inftyValuation K)
参数：hlt : 1 < v X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.isEquiv_iff_val_lt_one`：isEquiv_iff_val_lt_one : v.IsEquiv v' 
↔ forall {x}, v x < 1 ↔ v' x < 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.inftyValuation.X`：∀ (F : Type u_1) [inst : Field F] [inst_1 : De
cidableEq (RatFunc F)],   (RatFunc.inftyValuation F) RatFunc.X = WithZero.exp 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RatFunc.valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X`：v
aluation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X {f : RatFunc K} [v.
IsTrivialOn K] (hlt : 1 < v X) (hf : f != 0) : v f = v RatF…
· 使用定理 `RatFunc.instIsTrivialOnWithZeroMultiplicativeIntInftyValuation`：∀ (F : T
ype u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)], Valuation.IsTrivia
lOn F (RatFunc.inftyValuation F)
-/
lemma valuation_isEquiv_inftyValuation_of_one_lt_valuation_X [v.IsTrivialOn K] (hlt : 1 < v X) :
    v.IsEquiv (inftyValuation K) := by
  refine isEquiv_iff_val_lt_one.mpr fun {f} ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation K X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt hf,
      valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt' hf]
    grind [one_le_zpow_iff_right₀]

end Infinity

open IsDedekindDomain HeightOneSpectrum Set Valuation Polynomial

/-
**RatFunc.setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty** 是 Mathlib
 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial
] [v.IsTrivialOn K] (hle : v RatFunc.X <= 1) : {p : K[X] | v p < 1 ∧ p != 0}.Non
empty
参数：hle : v RatFunc.X <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Valuation.IsNontrivial.exists_lt_one`：∀ {K : Type u_7} [inst : DivisionR
ing K] {Γ₀ : Type u_8} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   {v : Valua
tion K Γ₀} [hv : v.IsNontr…
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Polynomial.valuation_le_one_of_valuation_X_le_one`：valuation_le_one_of_v
aluation_X_le_one (hle : v RatFunc.X <= 1) (p : K[X]) : v p <= 1
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTrivialOn K]
    (hle : v RatFunc.X ≤ 1) : {p : K[X] | v p < 1 ∧ p ≠ 0}.Nonempty := by
  obtain ⟨w, h0, h1⟩ := IsNontrivial.exists_lt_one (v := v)
  induction w using RatFunc.induction_on with
  | f p q =>
    simp only [ne_eq, _root_.div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or,
      map_div₀] at *
    have hor : ¬v ↑p = 1 ∨ ¬v ↑q = 1 := by rw [← not_and_or]; aesop
    suffices ∀ r : K[X], v (↑r) ≠ 1 → r ≠ 0 → {p : K[X] | v ↑p < 1 ∧ ¬p = 0}.Nonempty by
      exact Or.elim hor (fun hp ↦ this p hp h0.1) (fun hq ↦ this q hq h0.2)
    exact fun r hr hr0 ↦ ⟨r, lt_iff_le_and_ne.mpr
      ⟨Polynomial.valuation_le_one_of_valuation_X_le_one _ hle r, hr⟩, hr0⟩

@[deprecated (since := "2026-07-09")]
alias setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty :=
  setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty
/-
**RatFunc.one_le_valuation_factor** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma one_le_valuation_factor (hne : {p : K[X] | v p < 1 ∧ p ≠ 0}.Nonempty) {a b : K[X]}
    (hab : v ↑(a * b) < 1 ∧ a ≠ 0 ∧ b ≠ 0) (hπᵥ : degree_lt_wf.min _ hne = a * b)
    (hb : ¬IsUnit b) : 1 ≤ v ↑a := by
  set πᵥ := degree_lt_wf.min _ hne
  have hda : a.degree < πᵥ.degree := by
    have hbpos := degree_pos_of_ne_zero_of_nonunit hab.2.2 hb
    simp_rw [hπᵥ, degree_mul, degree_eq_natDegree hab.2.1, degree_eq_natDegree hab.2.2] at hbpos ⊢
    norm_cast
    simpa using hbpos
  have hlea := imp_not_comm.mp (degree_lt_wf.not_lt_min _) hda
  grind
/-
**RatFunc.irreducible_min_polynomial_valuation_lt_one_and_ne_zero** 是 Mathlib 中的
一个引理，位于命名空间 `RatFunc`。
形式化陈述：irreducible_min_polynomial_valuation_lt_one_and_ne_zero [v.IsTrivialOn K] 
(hne : {p : K[X] | v p < 1 ∧ p != 0}.Nonempty) : Irreducible (degree_lt_wf.min {
p : K[X] | v p < 1 ∧ p != 0} hne)
参数：hne : {p : K[X] | v p < 1 ∧ p != 0}.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `irreducible_iff`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irreducible
 p ↔ ¬IsUnit p ∧ ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.algebraMap_eq_C`：algebraMap_eq_C : algebraMap K K⟮X⟯ = C
· 使用定理 `RatFunc.algebraMap_C`：algebraMap_C (a : K) : algebraMap K[X] K⟮X⟯ (Polyn
omial.C a) = C a
· 使用定理 `RatFunc.coePolynomial.eq_1`：∀ {K : Type u} [inst : CommRing K] [inst_1 :
 IsDomain K] (P : Polynomial K),   ↑P = (algebraMap (Polynomial K) (RatFunc K)) 
P
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `_private.Mathlib.NumberTheory.RatFunc.Ostrowski.0.RatFunc.one_le_valuati
on_factor`：∀ {K : Type u_1} {Γ : Type u_2} [inst : Field K] [inst_1 : LinearOrde
redCommGroupWithZero Γ]   {v : Valuation (RatFunc K) Γ} (hne : {p | v ↑…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.coePolynomial.congr_simp`：∀ {K : Type u} [inst : CommRing K] [in
st_1 : IsDomain K] (P P_1 : Polynomial K), P = P_1 → ↑P = ↑P_1
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Right.one_le_mul`：Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 <=
 a) (hb : 1 <= b) : 1 <= a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
（共 33 条，此处仅展示前 30 条）
-/
lemma irreducible_min_polynomial_valuation_lt_one_and_ne_zero [v.IsTrivialOn K]
    (hne : {p : K[X] | v p < 1 ∧ p ≠ 0}.Nonempty) :
    Irreducible (degree_lt_wf.min {p : K[X] | v p < 1 ∧ p ≠ 0} hne) := by
  set πᵥ := degree_lt_wf.min _ hne
  have hπᵥ : v πᵥ < 1 ∧ πᵥ ≠ 0 := degree_lt_wf.min_mem _ hne
  refine irreducible_iff.mpr ⟨?_, fun a b hab ↦ ?_⟩
  · simp only [Polynomial.isUnit_iff, isUnit_iff_ne_zero]
    intro ⟨a, ha0, ha⟩
    rw [← ha, coePolynomial, algebraMap_C, ← algebraMap_eq_C] at hπᵥ
    grind
  · by_contra! H
    simp only [hab, ne_eq, mul_eq_zero, not_or] at hπᵥ
    have hva := one_le_valuation_factor hne hπᵥ hab H.2
    simp only [mul_comm a b, @and_comm (¬a = 0)] at hπᵥ hab
    have := Right.one_le_mul (one_le_valuation_factor hne hπᵥ hab H.1) hva
    simp only [coePolynomial_eq_algebraMap, map_mul] at hπᵥ this
    grind

section valuation_X_le_one

variable [v.IsNontrivial] [v.IsTrivialOn K] (hle : v RatFunc.X ≤ 1)

/-- A uniformizing element for the valuation `v`, as a polynomial in `K[X]`. -/
/-
**RatFunc.uniformizingPolynomial** 是 Mathlib 中的一个缩写定义，位于命名空间 `RatFunc`。
形式化陈述：uniformizingPolynomial : K[X]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RatFunc.setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty`：setO
fPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTri
vialOn K] (hle : v RatFunc.X <= 1) : {p : K[X] | v p < 1…

--- 原说明 ---
A uniformizing element for the valuation `v`, as a polynomial in `K[X]`.
-/
abbrev uniformizingPolynomial : K[X] :=
  WellFounded.min degree_lt_wf _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)

@[inherit_doc]
local notation "πᵥ" => uniformizingPolynomial hle
/-
**RatFunc.uniformizingPolynomial_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：uniformizingPolynomial_ne_zero : πᵥ != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用引理 `RatFunc.setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty`：setO
fPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTri
vialOn K] (hle : v RatFunc.X <= 1) : {p : K[X] | v p < 1…
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma uniformizingPolynomial_ne_zero : πᵥ ≠ 0 := by
  have := degree_lt_wf.min_mem _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)
  simp_all [uniformizingPolynomial]
/-
**RatFunc.valuation_uniformizingPolynomial_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Rat
Func`。
形式化陈述：valuation_uniformizingPolynomial_lt_one : v πᵥ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用引理 `RatFunc.setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty`：setO
fPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTri
vialOn K] (hle : v RatFunc.X <= 1) : {p : K[X] | v p < 1…
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
lemma valuation_uniformizingPolynomial_lt_one : v πᵥ < 1 := by
  simpa using! (degree_lt_wf.min_mem _
    (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)).1

open Ideal in
/-- The maximal ideal of `K[X]` generated by the `uniformizingPolynomial` for `v`. -/
/-
**RatFunc.valuationIdeal** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：valuationIdeal : HeightOneSpectrum K[X] where asIdeal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal ideal of `K[X]` generated by the `uniformizingPolynomial` for `v`.
-/
def valuationIdeal : HeightOneSpectrum K[X] where
  asIdeal := Submodule.span K[X] {πᵥ}
  isPrime := IsMaximal.isPrime (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_min_polynomial_valuation_lt_one_and_ne_zero
      (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)))
  ne_bot := by simpa using uniformizingPolynomial_ne_zero hle

@[inherit_doc]
local notation "Pᵥ" => RatFunc.valuationIdeal hle

section Associates

open EuclideanDomain in
/-
**RatFunc.valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_on
e** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one {p
 : K[X]} (hp : p != 0) : v (algebraMap K[X] (RatFunc K) p) = v (πᵥ ^ ((Associate
s.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors))
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RatFunc.setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty`：setO
fPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTri
vialOn K] (hle : v RatFunc.X <= 1) : {p : K[X] | v p < 1…
· 使用引理 `RatFunc.irreducible_min_polynomial_valuation_lt_one_and_ne_zero`：irreduc
ible_min_polynomial_valuation_lt_one_and_ne_zero [v.IsTrivialOn K] (hne : {p : K
[X] | v p < 1 ∧ p != 0}.Nonempty) : Irreducible (degr…
· 使用定理 `WfDvdMonoid.max_power_factor`：WfDvdMonoid.max_power_factor [CommMonoidWi
thZero α] [WfDvdMonoid α] {a₀ x : α} (h : a₀ != 0) (hx : Irreducible x) : exists
 (n : Nat) (a : α)…
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 53 条，此处仅展示前 30 条）
-/
lemma valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one {p : K[X]}
    (hp : p ≠ 0) :
    v (algebraMap K[X] (RatFunc K) p) = v (πᵥ ^ ((Associates.mk (Pᵥ).asIdeal).count
      (Associates.mk (Ideal.span {p})).factors)) := by
  set π := πᵥ
  have hne := setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle
  have hπirr : Irreducible π := irreducible_min_polynomial_valuation_lt_one_and_ne_zero hne
  obtain ⟨k, q, hnq, heq⟩ := WfDvdMonoid.max_power_factor hp hπirr
  have hπ : π ∈ _ := degree_lt_wf.min_mem _ hne
  simp only [ne_eq, mem_ofPred] at hπ
  nth_rw 1 [heq]
  simp only [map_mul, map_pow]
  suffices v (algebraMap K[X] (RatFunc K) q) = 1 by
    simp only [this, mul_one]
    congr
    exact (Ideal.count_associates_eq (irreducible_iff_prime.mp hπirr) hnq heq).symm
  rw [← mod_add_div q π, map_add]
  rw [← mod_eq_zero] at hnq
  suffices v (algebraMap K[X] (RatFunc K) (q % π)) = 1 ∧
      v (algebraMap K[X] (RatFunc K) (π * (q / π))) < 1 by
    obtain ⟨h₁, h₂⟩ := this
    rw [← h₁] at h₂ ⊢
    exact Valuation.map_add_eq_of_lt_left _ h₂
  constructor
  · rw [← coePolynomial_eq_algebraMap]
    have hnπ : q % π ∉ {p : K[X] | v ↑p < 1 ∧ p ≠ 0} :=
      imp_not_comm.mp (degree_lt_wf.not_lt_min _) (EuclideanDomain.remainder_lt q hπ.2)
    have := Polynomial.valuation_le_one_of_valuation_X_le_one _ hle (q % π)
    grind
  · simpa only [map_mul, ← coePolynomial_eq_algebraMap]
      using mul_lt_one_of_lt_of_le hπ.1 <| (q / π).valuation_le_one_of_valuation_X_le_one _ hle
/-
**RatFunc.exists_zpow_uniformizingPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`
。
形式化陈述：exists_zpow_uniformizingPolynomial {f : RatFunc K} (hf : f != 0) : exists 
(z : Int), v f = v πᵥ ^ z
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用引理 `RatFunc.uniformizingPolynomial_ne_zero`：uniformizingPolynomial_ne_zero :
 πᵥ != 0
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `RatFunc.valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X
_le_one`：valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one
 {p : K[X]} (hp : p != 0) : v (algebraMap K[X] (RatFunc K) p) = v (πᵥ…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
（共 32 条，此处仅展示前 30 条）
-/
lemma exists_zpow_uniformizingPolynomial {f : RatFunc K} (hf : f ≠ 0) :
    ∃ (z : ℤ), v f = v πᵥ ^ z := by
  have h0 : v πᵥ ≠ 0 := by simpa using uniformizingPolynomial_ne_zero hle
  induction f using RatFunc.induction_on with
  | f p q hq =>
    use (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors -
      (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {q})).factors
    simp only [map_div₀, map_pow, zpow_sub₀ h0, zpow_natCast,
      valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hq,
      valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle
        (p := p) (by aesop)]
/-
**RatFunc.uniformizingPolynomial_isUniformizer** 是 Mathlib 中的一个引理，位于命名空间 `RatFun
c`。
形式化陈述：uniformizingPolynomial_isUniformizer [hv : IsRankOneDiscrete v] : v.IsUnif
ormizer πᵥ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用引理 `RatFunc.uniformizingPolynomial_ne_zero`：uniformizingPolynomial_ne_zero :
 πᵥ != 0
· 使用定理 `Valuation.IsUniformizer.eq_1`：∀ {Γ : Type u_1} [inst : LinearOrderedComm
GroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation A Γ)   [hv : v.
IsRankOneDiscrete]…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用定理 `Valuation.IsRankOneDiscrete.instIsCyclicSubtypeUnitsMemSubgroupValueGrou
pOfClass`：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u
_2} [inst_1 : Ring A] (v : Valuation A Γ)   [v.IsRankOneDiscrete], IsC…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator`：valueGroup
_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = generator v
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_unique`：genLTOne_unique {g : G}
 (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne
· 使用定理 `Units.val_lt_val`：val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α
) < b ↔ a < b
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用引理 `RatFunc.valuation_uniformizingPolynomial_lt_one`：valuation_uniformizingP
olynomial_lt_one : v πᵥ < 1
（共 75 条，此处仅展示前 30 条）
-/
lemma uniformizingPolynomial_isUniformizer [hv : IsRankOneDiscrete v] :
    v.IsUniformizer πᵥ := by
  have h0 : v πᵥ ≠ 0 := by simpa using uniformizingPolynomial_ne_zero hle
  rw [IsUniformizer, ← hv.valueGroup_genLTOne_eq_generator, ← h0.isUnit.unit_spec, Units.val_inj]
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
  · rw [← Units.val_lt_val, h0.isUnit.unit_spec, Units.val_one]
    exact valuation_uniformizingPolynomial_lt_one hle
  · ext γ
    simp only [coePolynomial_eq_algebraMap, MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq,
      map_eq_zero, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨a, ha, b, hab⟩ ↦ ?_⟩
    · use 1, one_ne_zero, πᵥ ^ k
      simp only [← Units.val_inj, Units.val_zpow_eq_zpow_val] at hk
      simp [← hk]
    · obtain ⟨ka, hka⟩ := exists_zpow_uniformizingPolynomial hle ha
      obtain ⟨kb, hkb⟩ := exists_zpow_uniformizingPolynomial hle (f := b) (by aesop)
      rw [MonoidWithZeroHom.coe_ofClass, hka, hkb] at hab
      use kb - ka
      have : v ↑πᵥ ^ ka ≠ 0 := zpow_ne_zero _ h0
      simp [zpow_sub, ← Units.val_inj, ← coePolynomial_eq_algebraMap, field, ← hab]
/-
**RatFunc.valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one** 是 Mathli
b 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one [IsRankOneDisc
rete v] : v.IsEquiv ((Pᵥ).valuation (RatFunc K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.isEquiv_iff_val_le_one`：isEquiv_iff_val_le_one : v.IsEquiv v' 
↔ forall {x}, v x <= 1 ↔ v' x <= 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
（共 61 条，此处仅展示前 30 条）
-/
lemma valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one [IsRankOneDiscrete v] :
    v.IsEquiv ((Pᵥ).valuation (RatFunc K)) := by
  rw [isEquiv_iff_val_le_one]
  intro f
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · induction f using RatFunc.induction_on with
    | f p q hq0 =>
      have hp0 : p ≠ 0 := by simp_all
      set pi := πᵥ with hpi_def
      have hpi : v.IsUniformizer (pi : RatFunc K) := uniformizingPolynomial_isUniformizer hle
      simp only [map_div₀, valuation_of_algebraMap, intValuation_def, exp_neg, if_neg hp0,
        if_neg hq0, div_inv_eq_mul]
      rw [valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hp0,
        valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hq0]
      simp_all [div_le_one₀, inv_mul_le_one₀,
        (pow_le_pow_iff_right_of_lt_one₀ (by simp_all) (IsRankOneDiscrete.generator_lt_one v))]

end Associates

end valuation_X_le_one

/-
**RatFunc.adicValuation_not_isEquiv_infty_valuation** 是 Mathlib 中的一个引理，位于命名空间 `R
atFunc`。
形式化陈述：adicValuation_not_isEquiv_infty_valuation [DecidableEq (RatFunc K)] (p : I
sDedekindDomain.HeightOneSpectrum K[X]) : ¬ (p.valuation (RatFunc K)).IsEquiv (i
nftyValuation K)
参数：RatFunc K；p : IsDedekindDomain.HeightOneSpectrum K[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1
· 使用定理 `RatFunc.inftyValuation.X`：∀ (F : Type u_1) [inst : Field F] [inst_1 : De
cidableEq (RatFunc F)],   (RatFunc.inftyValuation F) RatFunc.X = WithZero.exp 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.log_lt_iff_lt_exp`：log_lt_iff_lt_exp (hx : x != 0) : log x < a 
↔ x < exp a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `WithZero.log_one`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.log 1 
= 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma adicValuation_not_isEquiv_infty_valuation [DecidableEq (RatFunc K)]
    (p : IsDedekindDomain.HeightOneSpectrum K[X]) :
    ¬ (p.valuation (RatFunc K)).IsEquiv (inftyValuation K) := by
  simp only [isEquiv_iff_val_le_one]
  push Not
  refine ⟨X, .inl ⟨p.valuation_le_one _, ?_⟩⟩
  rw [inftyValuation.X, ← log_lt_iff_lt_exp one_ne_zero, log_one]
  exact zero_lt_one
/-
**RatFunc.adicValuation_ne_inftyValuation** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：adicValuation_ne_inftyValuation [DecidableEq (RatFunc K)] (p : IsDedekindD
omain.HeightOneSpectrum K[X]) : p.valuation (RatFunc K) != inftyValuation K
参数：RatFunc K；p : IsDedekindDomain.HeightOneSpectrum K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Valuation.IsEquiv.refl`：refl : v.IsEquiv v
· 使用引理 `RatFunc.adicValuation_not_isEquiv_infty_valuation`：adicValuation_not_isE
quiv_infty_valuation [DecidableEq (RatFunc K)] (p : IsDedekindDomain.HeightOneSp
ectrum K[X]) : ¬ (p.valuation (RatFunc …
-/
lemma adicValuation_ne_inftyValuation [DecidableEq (RatFunc K)]
   (p : IsDedekindDomain.HeightOneSpectrum K[X]) :
    p.valuation (RatFunc K) ≠ inftyValuation K := by
  by_contra h
  exact absurd Valuation.IsEquiv.refl (h ▸ adicValuation_not_isEquiv_infty_valuation p)

section Discrete

variable [IsRankOneDiscrete v]

section IsTrivialOn

variable [v.IsTrivialOn K]

/-
**RatFunc.valuation_isEquiv_adic_of_valuation_X_le_one** 是 Mathlib 中的一个引理，位于命名空间
 `RatFunc`。
形式化陈述：valuation_isEquiv_adic_of_valuation_X_le_one (hle : v X <= 1) : exists (u 
: HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _)
参数：hle : v X <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用引理 `RatFunc.valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one`：val
uation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one [IsRankOneDiscrete v] :
 v.IsEquiv ((Pᵥ).valuation (RatFunc K))
-/
lemma valuation_isEquiv_adic_of_valuation_X_le_one (hle : v X ≤ 1) :
    ∃ (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _) :=
  ⟨_, valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one hle⟩

/-- **Ostrowski's Theorem** for `K(X)` with `K` any field:
A discrete valuation of rank 1 that is trivial on `K` is equivalent either to the valuation
at infinity or to the `p`-adic valuation for a unique maximal ideal `p` of `K[X]`. -/
/-
**RatFunc.valuation_isEquiv_infty_or_adic** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：valuation_isEquiv_infty_or_adic [DecidableEq (RatFunc K)] : Xor (v.IsEquiv
 (RatFunc.inftyValuation K)) (exists! (u : HeightOneSpectrum K[X]), v.IsEquiv (u
.valuation _))
参数：RatFunc K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X`：valuatio
n_isEquiv_inftyValuation_of_one_lt_valuation_X [v.IsTrivialOn K] (hlt : 1 < v X)
 : v.IsEquiv (inftyValuation K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Valuation.IsEquiv.trans`：trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v
₃) : v₁.IsEquiv v₃
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
· 使用引理 `RatFunc.adicValuation_not_isEquiv_infty_valuation`：adicValuation_not_isE
quiv_infty_valuation [DecidableEq (RatFunc K)] (p : IsDedekindDomain.HeightOneSp
ectrum K[X]) : ¬ (p.valuation (RatFunc …
· 使用引理 `RatFunc.valuation_isEquiv_adic_of_valuation_X_le_one`：valuation_isEquiv_
adic_of_valuation_X_le_one (hle : v X <= 1) : exists (u : HeightOneSpectrum K[X]
), v.IsEquiv (u.valuation _)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation`：eq
_of_valuation_isEquiv_valuation {p q : HeightOneSpectrum R} (hpq : (valuation K 
p).IsEquiv (valuation K q)) : p = q

--- 原说明 ---
**Ostrowski's Theorem** for `K(X)` with `K` any field:
A discrete valuation of rank 1 that is trivial on `K` is equivalent either to th
e valuation
at infinity or to the `p`-adic valuation for a unique maximal ideal `p` of `K[X]
`.
-/
theorem valuation_isEquiv_infty_or_adic [DecidableEq (RatFunc K)] :
    Xor (v.IsEquiv (RatFunc.inftyValuation K))
      (∃! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _)) := by
  rcases lt_or_ge 1 (v X) with hlt | hge
  /- Infinity case -/
  · have hv := valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
    refine .inl ⟨hv, ?_⟩
    simp only [ExistsUnique, not_exists, not_and, not_forall]
    intro pw hw
    exact absurd (hw.symm.trans hv) (adicValuation_not_isEquiv_infty_valuation pw)
  /- Prime case -/
  · obtain ⟨pw, hw⟩ := valuation_isEquiv_adic_of_valuation_X_le_one hge
    exact .inr ⟨⟨pw, hw, fun pw' hw' ↦ eq_of_valuation_isEquiv_valuation (hw'.symm.trans hw)⟩,
      fun hv ↦ absurd (hw.symm.trans hv) (adicValuation_not_isEquiv_infty_valuation pw)⟩
/-
**RatFunc.valuation_isEquiv_adic_of_not_isEquiv_infty** 是 Mathlib 中的一个引理，位于命名空间 
`RatFunc`。
形式化陈述：valuation_isEquiv_adic_of_not_isEquiv_infty [DecidableEq (RatFunc K)] (hni
 : ¬ v.IsEquiv (RatFunc.inftyValuation K)) : exists! (u : HeightOneSpectrum K[X]
), v.IsEquiv (u.valuation _)
参数：RatFunc K；hni : ¬ v.IsEquiv (RatFunc.inftyValuation K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Xor.or`：∀ {a b : Prop}, Xor a b → a ∨ b
· 使用定理 `RatFunc.valuation_isEquiv_infty_or_adic`：valuation_isEquiv_infty_or_adic
 [DecidableEq (RatFunc K)] : Xor (v.IsEquiv (RatFunc.inftyValuation K)) (exists!
 (u : HeightOneSpectrum K[X])…
-/
lemma valuation_isEquiv_adic_of_not_isEquiv_infty [DecidableEq (RatFunc K)]
    (hni : ¬ v.IsEquiv (RatFunc.inftyValuation K)) :
    ∃! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _) :=
  valuation_isEquiv_infty_or_adic.or.resolve_left hni

end IsTrivialOn

end Discrete

end RatFunc

end

