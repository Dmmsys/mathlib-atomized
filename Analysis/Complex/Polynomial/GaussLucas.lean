/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Gauss-Lucas Theorem

In this file we prove Gauss-Lucas Theorem:
the roots of the derivative of a nonconstant complex polynomial
are included in the convex hull of the roots of the polynomial.
-/

@[expose] public section
open scoped Polynomial ComplexConjugate

namespace Polynomial

/-- Given a polynomial `P` of positive degree and a root `z` of its derivative,
`derivRootWeight P z w` gives the weight of a root `w` of `P` in a convex combination
that is equal to `z`. -/
/-
**Polynomial.derivRootWeight** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：derivRootWeight (P : Complex[X]) (z w : Complex) : Real
参数：P : Complex[X]；z w : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial `P` of positive degree and a root `z` of its derivative,
`derivRootWeight P z w` gives the weight of a root `w` of `P` in a convex combin
ation
that is equal to `z`.
-/
noncomputable def derivRootWeight (P : ℂ[X]) (z w : ℂ) : ℝ :=
  if P.eval z = 0 then (Pi.single z 1 : ℂ → ℝ) w
  else P.rootMultiplicity w / ‖z - w‖ ^ 2
/-
**Polynomial.derivRootWeight_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：derivRootWeight_nonneg (P : Complex[X]) (z w : Complex) : 0 <= derivRootWe
ight P z w
参数：P : Complex[X]；z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
theorem derivRootWeight_nonneg (P : ℂ[X]) (z w : ℂ) : 0 ≤ derivRootWeight P z w := by
  simp only [derivRootWeight, Pi.single, Function.update_apply]
  split_ifs <;> first | positivity | simp

variable {P : ℂ[X]} {z : ℂ}

/-- The sum of the weights `derivRootWeight P z w` of all the roots `w` of `P` is positive,
provided that `P` is not a constant polynomial. -/
/-
**Polynomial.sum_derivRootWeight_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_derivRootWeight_pos (hP : 0 < degree P) (z : Complex) : 0 < ∑ w in P.r
oots.toFinset, derivRootWeight P z w
参数：hP : 0 < degree P；z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Multiset.toFinset_nonempty`：toFinset_nonempty : s.toFinset.Nonempty ↔ s 
!= 0
· 使用定理 `Polynomial.Splits.roots_ne_zero`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree ≠ 0 → f.roots ≠ 0
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of the weights `derivRootWeight P z w` of all the roots `w` of `P` is po
sitive,
provided that `P` is not a constant polynomial.
-/
theorem sum_derivRootWeight_pos (hP : 0 < degree P) (z : ℂ) :
    0 < ∑ w ∈ P.roots.toFinset, derivRootWeight P z w := by
  have hP₀ : P ≠ 0 := by rintro rfl; simp at hP
  by_cases hPz : P.eval z = 0
  · simp [derivRootWeight, hPz, hP₀]
  · simp only [derivRootWeight, if_neg hPz]
    apply Finset.sum_pos
    · intro w hw
      apply div_pos (by simp_all)
      suffices z ≠ w by simpa [sq_pos_iff, sub_eq_zero]
      rintro rfl
      simp_all
    · rw [Multiset.toFinset_nonempty]
      apply Splits.roots_ne_zero (IsAlgClosed.splits _)
      rwa [← pos_iff_ne_zero, natDegree_pos_iff_degree_pos]

/-- *Gauss-Lucas Theorem*: if $P$ is a nonconstant polynomial with complex coefficients,
then all zeros of $P'$ belong to the convex hull of the set of zeros of $P$.

This version provides explicit formulas for the coefficients of the convex combination.
See also `rootSet_derivative_subset_convexHull_rootSet` below.
-/
/-
**Polynomial.eq_centerMass_of_eval_derivative_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：eq_centerMass_of_eval_derivative_eq_zero (hP : 0 < P.degree) (hz : P.deriv
ative.eval z = 0) : z = P.roots.toFinset.centerMass (P.derivRootWeight z) id
参数：hP : 0 < P.degree；hz : P.derivative.eval z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.derivRootWeight.eq_1`：∀ (P : Polynomial ℂ) (z w : ℂ),   P.der
ivRootWeight z w =     if Polynomial.eval z P = 0 then Pi.single z 1 w else ↑(Po
lynomial.rootMultipli…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
*Gauss-Lucas Theorem*: if $P$ is a nonconstant polynomial with complex coefficie
nts,
then all zeros of $P'$ belong to the convex hull of the set of zeros of $P$.

This version provides explicit formulas for the coefficients of the convex combi
nation.
See also `rootSet_derivative_subset_convexHull_rootSet` below.
-/
theorem eq_centerMass_of_eval_derivative_eq_zero (hP : 0 < P.degree)
    (hz : P.derivative.eval z = 0) :
    z = P.roots.toFinset.centerMass (P.derivRootWeight z) id := by
  set weight : ℂ → ℝ := P.derivRootWeight z
  set s := P.roots.toFinset
  suffices ∑ x ∈ s, weight x • (z - x) = 0 by calc
    z = s.centerMass weight fun _ ↦ z := by
      rw [Finset.centerMass, ← Finset.sum_smul, inv_smul_smul₀]
      exact (sum_derivRootWeight_pos hP z).ne'
    _ = s.centerMass weight (z - ·) + s.centerMass weight id := by
      simp only [Finset.centerMass, ← smul_add, ← Finset.sum_add_distrib, id, sub_add_cancel]
    _ = s.centerMass weight id := by
      simp only [add_eq_right, Finset.centerMass, this, smul_zero]
  by_cases hzP : P.eval z = 0
  · simp only [weight, derivRootWeight, if_pos hzP]
    rw [Finset.sum_eq_single z] <;> simp_all
  calc
    ∑ x ∈ s, weight x • (z - x) = conj (∑ x ∈ s, P.rootMultiplicity x • (1 / (z - x))) := by
      simp only [map_sum, weight, derivRootWeight, if_neg hzP]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have : z - x ≠ 0 := by
        rw [sub_ne_zero]
        rintro rfl
        simp_all [s]
      simp [← Complex.conj_mul', field]
    _ = conj (P.roots.map fun x ↦ 1 / (z - x)).sum := by
      simp only [Finset.sum_multiset_map_count, P.count_roots, s]
    _ = 0 := by
      rw [← (IsAlgClosed.splits _).eval_derivative_div_eval_of_ne_zero hzP]
      simp [hz]

/-- *Gauss-Lucas Theorem*: if $P$ is a nonconstant polynomial with complex coefficients,
then all zeros of $P'$ belong to the convex hull of the set of zeros of $P$.

See also `eq_centerMass_of_eval_derivative_eq_zero`
for a version that provides explicit coefficients of the convex combination.
-/
/-
**Polynomial.rootSet_derivative_subset_convexHull_rootSet** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：rootSet_derivative_subset_convexHull_rootSet (h₀ : 0 < P.degree) : P.deriv
ative.rootSet Complex subseteq convexHull Real (P.rootSet Complex)
参数：h₀ : 0 < P.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_centerMass_of_eval_derivative_eq_zero`：eq_centerMass_of_ev
al_derivative_eq_zero (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) : z = P
.roots.toFinset.centerMass (P.derivRootWe…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.coe_aeval_eq_eval`：coe_aeval_eq_eval (r : R) : (aeval r : R[X
] -> R) = eval r
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.sum_derivRootWeight_pos`：sum_derivRootWeight_pos (hP : 0 < de
gree P) (z : Complex) : 0 < ∑ w in P.roots.toFinset, derivRootWeight P z w

--- 原说明 ---
*Gauss-Lucas Theorem*: if $P$ is a nonconstant polynomial with complex coefficie
nts,
then all zeros of $P'$ belong to the convex hull of the set of zeros of $P$.

See also `eq_centerMass_of_eval_derivative_eq_zero`
for a version that provides explicit coefficients of the convex combination.
-/
theorem rootSet_derivative_subset_convexHull_rootSet (h₀ : 0 < P.degree) :
    P.derivative.rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ) := by
  intro z hz
  rw [mem_rootSet, coe_aeval_eq_eval] at hz
  rw [eq_centerMass_of_eval_derivative_eq_zero h₀ hz.2]
  apply Finset.centerMass_mem_convexHull
  · simp [derivRootWeight_nonneg]
  · apply sum_derivRootWeight_pos h₀
  · simp [mem_rootSet]

end Polynomial

