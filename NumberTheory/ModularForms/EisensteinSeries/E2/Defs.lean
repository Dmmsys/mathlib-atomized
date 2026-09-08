/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups
  SummationFilter Real

@[expose] public noncomputable section

namespace EisensteinSeries

/-- This is an auxiliary summand used to define the Eisenstein series `G2`. -/
/-
**EisensteinSeries.e2Summand** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：e2Summand (m : Int) (z : ℍ) : Complex
参数：m : Int；z : ℍ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary summand used to define the Eisenstein series `G2`.
-/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' n, eisSummand 2 ![m, n] z
/-
**EisensteinSeries.e2Summand_summable** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSerie
s`。
形式化陈述：e2Summand_summable (m : Int) (z : ℍ) : Summable (fun n => eisSummand 2 ![m
, n] z)
参数：m : Int；z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `EisensteinSeries.linear_right_summable`：linear_right_summable (z : Compl
ex) (c : Int) {k : Int} (hk : 2 <= k) : Summable fun d : Int => ((c * z + d) ^ k
)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n ↦ eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]

@[simp]
/-
**EisensteinSeries.e2Summand_zero_eq_two_riemannZeta_two** 是 Mathlib 中的一个引理，位于命名
空间 `EisensteinSeries`。
形式化陈述：e2Summand_zero_eq_two_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * rieman
nZeta 2
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even`：two_mul_riemannZeta_eq_
tsum_int_inv_pow_of_even {k : Nat} (hk : 2 <= k) (hk2 : Even k) : 2 * riemannZet
a k = ∑' (n : Int), ((n : Complex) ^ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma e2Summand_zero_eq_two_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  simpa [e2Summand, eisSummand] using!
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by grind) (by simp)).symm
/-
**EisensteinSeries.e2Summand_even** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：e2Summand_even (z : ℍ) : (e2Summand · z).Even
参数：z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_comp_neg`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : Topol
ogicalSpace α] {β : Type u_4} [inst_2 : InvolutiveNeg β]   (f : β → α), ∑' (d : 
β),…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 54 条，此处仅展示前 30 条）
-/
lemma e2Summand_even (z : ℍ) : (e2Summand · z).Even := by
  intro n
  simp only [e2Summand, ← tsum_comp_neg (fun a ↦ eisSummand 2 ![-n, a] z)]
  apply tsum_congr (fun b ↦ ?_)
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_cast [Int.cast_neg]
  ring

/-- The Eisenstein series of weight `2` and level `1` defined as the conditional sum
of `m` in `[N,N]` of `e2Summand m`. This sum over symmetric intervals is handy in showing it is
Summable. -/
/-
**EisensteinSeries.G2** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：G2 : ℍ -> Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Eisenstein series of weight `2` and level `1` defined as the conditional sum
of `m` in `[N,N]` of `e2Summand m`. This sum over symmetric intervals is handy i
n showing it is
Summable.
-/
def G2 : ℍ → ℂ := fun z ↦ ∑'[symmetricIcc ℤ] m, e2Summand m z

/-- The normalised Eisenstein series of weight `2` and level `1`.
Defined as `(1 / 2 * ζ(2)) * G2 `. -/
/-
**EisensteinSeries.E2** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：E2 : ℍ -> Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalised Eisenstein series of weight `2` and level `1`.
Defined as `(1 / 2 * ζ(2)) * G2 `.
-/
def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) • G2

/-- This function measures the defect in `G2` being a modular form. -/
/-
**EisensteinSeries.D2** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：D2 (γ : SL(2, Int)) : ℍ -> Complex
参数：γ : SL(2, Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This function measures the defect in `G2` being a modular form.
-/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z ↦ (2 * π * I * γ 1 0) / (denom γ z)

@[simp]
/-
**EisensteinSeries.D2_one** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：D2_one : D2 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `UpperHalfPlane.denom_one`：denom_one : denom 1 z = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma D2_one : D2 1 = 0 := by
  ext z
  simp [D2]
/-
**EisensteinSeries.denom_aux** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma denom_aux (A B : SL(2, ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
    (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  have h0 := Matrix.two_mul_expl A.1 B.1
  simp only [Fin.isValue, coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, ModularGroup.denom_apply,
    Matrix.det_fin_two B.1, Int.cast_sub, ← map_mul, h0.2.2.2]
  ring

local notation "φ" => Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
/-
**EisensteinSeries.D2_mul** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：D2_mul (A B : SL(2, Int)) : D2 (A * B) = (D2 A) ∣[(2 : Int)] B + D2 B
参数：A B : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ModularForm.SL_slash_def`：SL_slash_def (γ : SL(2, Int)) : f ∣[k] γ = fun
 τ => f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs.0.Ei
sensteinSeries.denom_aux`：∀ (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : Upp
erHalfPlane),   ↑(↑(A * B) 1 0) *       UpperHalfPlane.denom (Matrix.SpecialLine
arGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `UpperHalfPlane.specialLinearGroup_apply`：specialLinearGroup_apply {R : T
ype*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : g • z = mk (((algeb
raMap R Real (g 0 0) : Comple…
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
（共 101 条，此处仅展示前 30 条）
-/
lemma D2_mul (A B : SL(2, ℤ)) : D2 (A * B) = (D2 A) ∣[(2 : ℤ)] B + D2 B := by
  ext z
  simp only [D2, mul_assoc, coe_mul, map_mul, ← mul_div, SL_slash_def,
    ModularGroup.sl_moeb, Int.reduceNeg, zpow_neg, Pi.add_apply, ← mul_add, mul_eq_mul_left_iff,
    I_ne_zero, or_false, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero]
  have hd : (A.1 * B.1) 1 0 * denom (φ B) z - B 1 0 * denom (φ A * φ B) z = A 1 0 := by
    simpa [sub_eq_iff_eq_add] using denom_aux A B z
  have : denom A (num B z / denom B z) = denom A ↑(B • z) := by
    simp [specialLinearGroup_apply, denom, num]
  rw [(by intros; field_simp : ∀ {a b c d f e : ℂ} (he : e ≠ 0), a / b =
    c / d * (e ^ (2 : ℤ))⁻¹ + f / e ↔ a * e ^ 2 / b = c / d + e * f) (denom_ne_zero B z)]
  simp only [pow_two, ← mul_assoc, denom_cocycle A B z.im_ne_zero, this,
    ModularGroup.sl_moeb, ← hd]
  field_simp [denom_ne_zero A (toGL (φ B) • z)]
  ring
/-
**EisensteinSeries.D2_inv** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：D2_inv (A) : (D2 A) ∣[(2 : Int)] A⁻¹ = -D2 A⁻¹
参数：A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `EisensteinSeries.D2_one`：D2_one : D2 1 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EisensteinSeries.D2_mul`：D2_mul (A B : SL(2, Int)) : D2 (A * B) = (D2 A)
 ∣[(2 : Int)] B + D2 B
-/
lemma D2_inv (A) : (D2 A) ∣[(2 : ℤ)] A⁻¹ = -D2 A⁻¹ := by
  simpa [eq_neg_iff_add_eq_zero] using (D2_mul A A⁻¹).symm
/-
**EisensteinSeries.D2_T** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：D2_T : D2 ModularGroup.T = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma D2_T : D2 ModularGroup.T = 0 := by
  ext z
  simp [D2, ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/-
**EisensteinSeries.D2_S** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：D2_S (z : ℍ) : D2 ModularGroup.S z = 2 * π * I / z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma D2_S (z : ℍ) : D2 ModularGroup.S z = 2 * π * I / z := by
  simp [D2, ModularGroup.S, ModularGroup.denom_apply]

end EisensteinSeries

