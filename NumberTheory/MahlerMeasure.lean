/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Pi.Interval
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Mahler measure of integer polynomials

The main purpose of this file is to prove some facts about the Mahler measure of integer
polynomials, in particular Northcott's Theorem for the Mahler measure.

## Main results
- `Polynomial.finite_mahlerMeasure_le`: Northcott's Theorem: the set of integer polynomials of
  degree at most `n` and Mahler measure at most `B` is finite.
- `Polynomial.card_mahlerMeasure_le_prod`: an upper bound on the number of integer polynomials
  of degree at most `n` and Mahler measure at most `B`.
- `Polynomial.cyclotomic_mahlerMeasure_eq_one`: the Mahler measure of a cyclotomic polynomial is 1.
- `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one`: if an integer polynomial has Mahler measure equal
  to 1, then all its complex nonzero roots are roots of unity.
- `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`: if an integer non-constant polynomial has
  Mahler measure equal to 1 and is not a multiple of X, then it is divisible by a cyclotomic
  polynomial.
-/

public section

namespace Polynomial

open Int

/-
**Polynomial.one_le_mahlerMeasure_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：one_le_mahlerMeasure_of_ne_zero {p : Int[X]} (hp : p != 0) : 1 <= (p.map (
castRingHom Complex)).mahlerMeasure
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.one_le_abs`：one_le_abs {z : Int} (h₀ : z != 0) : 1 <= |z|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用引理 `Polynomial.leadingCoeff_le_mahlerMeasure`：leadingCoeff_le_mahlerMeasure 
(p : Complex[X]) : ‖p.leadingCoeff‖ <= p.mahlerMeasure
-/
lemma one_le_mahlerMeasure_of_ne_zero {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ (p.map (castRingHom ℂ)).mahlerMeasure := by
  apply le_trans _ (p.map (castRingHom ℂ)).leadingCoeff_le_mahlerMeasure
  rw [leadingCoeff_map_of_injective (castRingHom ℂ).injective_int, eq_intCast]
  norm_cast
  exact one_le_abs <| leadingCoeff_ne_zero.mpr hp

section Northcott

variable (n : ℕ) (B₁ B₂ : Fin (n + 1) → ℝ)

/-- The set of polynomials whose coefficients are bounded between `B₁` and `B₂`. This
construction is used as part of our proof of Northcott's theorem. -/
/-
**Polynomial.boxPoly** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：boxPoly : Set Int[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of polynomials whose coefficients are bounded between `B₁` and `B₂`. Thi
s
construction is used as part of our proof of Northcott's theorem.
-/
def boxPoly : Set ℤ[X] := {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}
/-
**Polynomial.ncard_boxPoly** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ncard_boxPoly : (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_congr'`：ncard_congr' {S : Set α} {T : Set β} (f : S ≃ T) : Set
.ncard S = Set.ncard T
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ceil_le`：ceil_le : ⌈a⌉ <= z ↔ a <= z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Int.le_floor`：le_floor : z <= ⌊a⌋ ↔ (z : α) <= a
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Polynomial.ofFn_natDegree_lt`：ofFn_natDegree_lt {n : Nat} (h : 1 <= n) (
v : Fin n -> R) : (ofFn n v).natDegree < n
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Polynomial.ofFn_coeff_eq_val_of_lt`：ofFn_coeff_eq_val_of_lt {n i : Nat} 
(v : Fin n -> R) (hi : i < n) : (ofFn n v).coeff i = v ⟨i, hi⟩
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
-/
theorem ncard_boxPoly : (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat := by
  trans Set.ncard (α := Fin (n + 1) → ℤ) (Finset.Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋))
  · refine Set.ncard_congr' ⟨fun p ↦ ⟨toFn (n + 1) p, ?_⟩, fun p ↦ ⟨ofFn (n + 1) p, ?_⟩, ?_, ?_⟩
    · have prop := p.property.2
      simpa using ⟨fun i ↦ ceil_le.mpr (prop i).1, fun i ↦ le_floor.mpr (prop i).2⟩
    · refine ⟨Nat.le_of_lt_succ <| ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i ↦ ?_⟩
      have prop := Finset.mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    · grind [boxPoly, ofFn_comp_toFn_eq_id_of_natDegree_lt]
    · grind [toFn_comp_ofFn_eq_id]
  · norm_cast
    grind [Pi.card_Icc, card_Icc]

@[deprecated (since := "2026-02-02")]
alias card_eq_of_natDegree_le_of_coeff_le := ncard_boxPoly

open NNReal
/-
**Polynomial.card_mahlerMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_mahlerMeasure (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ∧
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  have h_card :
      Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    simp_rw [norm_eq_abs, abs_le]
    rw [← boxPoly, ncard_boxPoly]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ ↦ ?_
    zify
    rw [toNat_of_nonneg (by positivity), ← natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ⊆
      {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (castRingHom ℂ)).coeff d‖ by aesop]
    apply le_trans <| (p.map (castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : ℤ[X]| p.natDegree ≤ n ∧
      ∀ (i : Fin (n + 1)), ‖p.coeff ↑i‖ ≤ ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card, Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩

/-- **Northcott's Theorem:** the set of integer polynomials of degree at most `n` and
Mahler measure at most `B` is finite. -/
/-
**Polynomial.finite_mahlerMeasure_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：finite_mahlerMeasure_le (n : Nat) (B : Real>=0) : Set.Finite {p : Int[X] |
 p.natDegree <= n ∧ (p.map (castRingHom Complex)).mahlerMeasure <= B}
参数：n : Nat；B : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.NumberTheory.MahlerMeasure.0.Polynomial.card_mahlerMeas
ure`：∀ (n : ℕ) (B : NNReal),   {p | p.natDegree ≤ n ∧ (Polynomial.map (Int.castR
ingHom ℂ) p).mahlerMeasure ≤ ↑B}.Finite ∧     {p | p.natDegree ≤ …

--- 原说明 ---
**Northcott's Theorem:** the set of integer polynomials of degree at most `n` an
d
Mahler measure at most `B` is finite.
-/
theorem finite_mahlerMeasure_le (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} :=
  (card_mahlerMeasure n B).1

/-- An upper bound on the number of integer polynomials of degree at most `n` and Mahler measure at
most `B`. -/
/-
**Polynomial.card_mahlerMeasure_le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_mahlerMeasure_le_prod (n : Nat) (B : Real>=0) : Set.ncard {p : Int[X]
 | p.natDegree <= n ∧ (p.map (castRingHom Complex)).mahlerMeasure <= B} <= ∏ i :
 Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1)
参数：n : Nat；B : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.NumberTheory.MahlerMeasure.0.Polynomial.card_mahlerMeas
ure`：∀ (n : ℕ) (B : NNReal),   {p | p.natDegree ≤ n ∧ (Polynomial.map (Int.castR
ingHom ℂ) p).mahlerMeasure ≤ ↑B}.Finite ∧     {p | p.natDegree ≤ …

--- 原说明 ---
An upper bound on the number of integer polynomials of degree at most `n` and Ma
hler measure at
most `B`.
-/
theorem card_mahlerMeasure_le_prod (n : ℕ) (B : ℝ≥0) :
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := (card_mahlerMeasure n B).2

end Northcott

section Cyclotomic

/-- The Mahler measure of a cyclotomic polynomial is 1. -/
/-
**Polynomial.cyclotomic_mahlerMeasure_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：cyclotomic_mahlerMeasure_eq_one {R : Type*} [CommRing R] [Algebra R Comple
x] (n : Nat) : ((cyclotomic n R).map (algebraMap R Complex)).mahlerMeasure = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.mahlerMeasure_one`：mahlerMeasure_one : (1 : Complex[X]).mahle
rMeasure = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsPrimitiveRoot.norm'_eq_one`：∀ {ζ : ℂ} {n : ℕ}, IsPrimitiveRoot ζ n → n
 ≠ 0 → ‖ζ‖ = 1
· 使用定理 `isPrimitiveRoot_of_mem_primitiveRoots`：isPrimitiveRoot_of_mem_primitiveR
oots {ζ : R} (h : ζ in primitiveRoots k R) : IsPrimitiveRoot ζ k
· 使用引理 `Multiset.prod_eq_one`：prod_eq_one (h : forall x in s, x = (1 : M)) : s.p
rod = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`：mahlerMeasure_e
q_leadingCoeff_mul_prod_roots (p : Complex[X]) : p.mahlerMeasure = ‖p.leadingCoe
ff‖ * (p.roots.map (fun a => max 1 ‖a‖)).prod
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.cyclotomic.roots_eq_primitiveRoots_val`：∀ {R : Type u_1} [ins
t : CommRing R] {n : ℕ} [inst_1 : IsDomain R] [NeZero ↑n],   (Polynomial.cycloto
mic n R).roots = (primitiveRoots n R).v…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The Mahler measure of a cyclotomic polynomial is 1.
-/
theorem cyclotomic_mahlerMeasure_eq_one {R : Type*} [CommRing R] [Algebra R ℂ] (n : ℕ) :
    ((cyclotomic n R).map (algebraMap R ℂ)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  have : NeZero n := ⟨hn⟩
  suffices ∏ x ∈ primitiveRoots n ℂ, max 1 ‖x‖ = 1 by
    simpa [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n ℂ,
      Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  suffices ∀ x ∈ primitiveRoots n ℂ, ‖x‖ ≤ 1 from Multiset.prod_eq_one (by simpa)
  intro _ hz
  exact (IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn).le

variable {p : ℤ[X]} (h : (p.map (castRingHom ℂ)).mahlerMeasure = 1)

include h in
/-
**Polynomial.norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个引理
，位于命名空间 `Polynomial`。
形式化陈述：norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one : ‖(p.map (castRingHom Co
mplex)).leadingCoeff‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Polynomial.leadingCoeff_le_mahlerMeasure`：leadingCoeff_le_mahlerMeasure 
(p : Complex[X]) : ‖p.leadingCoeff‖ <= p.mahlerMeasure
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one :
    ‖(p.map (castRingHom ℂ)).leadingCoeff‖ = 1 := by
  rcases eq_or_ne p 0 with _ | hp
  · simp_all
  have h_ineq := h ▸ (leadingCoeff_le_mahlerMeasure <| p.map (castRingHom ℂ))
  rw [leadingCoeff_map_of_injective (castRingHom ℂ).injective_int, eq_intCast] at ⊢ h_ineq
  norm_cast at ⊢ h_ineq
  grind [leadingCoeff_eq_zero]

include h in
/-
**Polynomial.abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个引理，
位于命名空间 `Polynomial`。
形式化陈述：abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one : |p.leadingCoeff| = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one`：norm_leadin
gCoeff_eq_one_of_mahlerMeasure_eq_one : ‖(p.map (castRingHom Complex)).leadingCo
eff‖ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
-/
lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one : |p.leadingCoeff| = 1 := by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  rw [leadingCoeff_map_of_injective (castRingHom ℂ).injective_int, eq_intCast] at this
  norm_cast at this

variable {z : ℂ} (hz₀ : z ≠ 0) (hz : z ∈ p.aroots ℂ)

include hz h in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex roots are integral
over ℤ. -/
/-
**Polynomial.isIntegral_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：isIntegral_of_mahlerMeasure_eq_one : IsIntegral Int z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] {a b : α}, |a| = |b| ↔ a = b ∨ a = -b
· 使用引理 `Polynomial.abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one`：abs_leadingC
oeff_eq_one_of_mahlerMeasure_eq_one : |p.leadingCoeff| = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.ediv_neg`：∀ (a b : ℤ), a / -b = -(a / b)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
If an integer polynomial has Mahler measure equal to 1, then all its complex roo
ts are integral
over ℤ.
-/
theorem isIntegral_of_mahlerMeasure_eq_one : IsIntegral ℤ z := by
  have : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp <|
    abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have : (C (1 / p.leadingCoeff) * p).Monic := by aesop (add safe (by simp [Monic.def]))
  grind [IsIntegral, RingHom.IsIntegralElem, mem_roots', IsRoot.def, eval₂_mul, eval_map]

set_option linter.style.whitespace false in -- manual alignment is not recognised
open Multiset in
include h hz in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex roots have norm at
most 1. -/
/-
**Polynomial.norm_root_le_one_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个引理，位于命名空间 
`Polynomial`。
形式化陈述：norm_root_le_one_of_mahlerMeasure_eq_one : ‖z‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `Multiset.mem_le_prod_of_one_le`：Multiset.mem_le_prod_of_one_le [ZeroLEOn
eClass β] {f : α -> β} (h1 : forall a : α, 1 <= f a) {s : Multiset α} {a : α} (h
a : a in s) : f a <=…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
If an integer polynomial has Mahler measure equal to 1, then all its complex roo
ts have norm at
most 1.
-/
lemma norm_root_le_one_of_mahlerMeasure_eq_one : ‖z‖ ≤ 1 := by
  calc
  ‖z‖ ≤ max 1 ‖z‖ := le_max_right 1 ‖z‖
  _   ≤ ((p.map (castRingHom ℂ)).roots.map (fun a ↦ max 1 ‖a‖)).prod :=
        mem_le_prod_of_one_le (fun a ↦ le_max_left 1 ‖a‖) hz
  _   ≤ 1 := by grind [prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff,
        norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one]

open IntermediateField in
include hz₀ hz h in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex nonzero roots are
roots of unity. -/
/-
**Polynomial.pow_eq_one_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：pow_eq_one_of_mahlerMeasure_eq_one : exists n, 0 < n ∧ z ^ n = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `Polynomial.isIntegral_of_mahlerMeasure_eq_one`：isIntegral_of_mahlerMeasu
re_eq_one : IsIntegral Int z
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `NumberField.Embeddings.pow_eq_one_of_norm_le_one`：pow_eq_one_of_norm_le_
one {x : K} (hx₀ : x != 0) (hxi : IsIntegral Int x) (hx : forall φ : K ->+* A, ‖
φ x‖ <= 1) : exists (n : Nat) (_ : 0 <…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `IntermediateField.coe_isIntegral_iff`：IntermediateField.coe_isIntegral_i
ff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L] {x
 : S} : IsIntegral R (x : …
· 使用引理 `Polynomial.norm_root_le_one_of_mahlerMeasure_eq_one`：norm_root_le_one_of
_mahlerMeasure_eq_one : ‖z‖ <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If an integer polynomial has Mahler measure equal to 1, then all its complex non
zero roots are
roots of unity.
-/
theorem pow_eq_one_of_mahlerMeasure_eq_one : ∃ n, 0 < n ∧ z ^ n = 1 := by
/- We want to use `NumberField.Embeddings.pow_eq_one_of_norm_le_one` but it can only be applied to
elements of number fields. We thus first construct the number field `K` obtained by adjoining `z`
to `ℚ`.
-/
  let K := ℚ⟮z⟯
  let : NumberField K := {
    to_charZero := ℚ⟮z⟯.charZero,
    to_finiteDimensional := adjoin.finiteDimensional
      (isIntegral_of_mahlerMeasure_eq_one h hz).tower_top }
-- `y` is `z` as an element of `K`
  let y : K := ⟨z, mem_adjoin_simple_self ℚ z⟩
  suffices ∃ (n : ℕ) (_ : 0 < n), y ^ n = 1 by
    obtain ⟨n, hn₀, hn₁⟩ := this
    exact ⟨n, hn₀, congrArg (algebraMap K ℂ) hn₁⟩
  refine NumberField.Embeddings.pow_eq_one_of_norm_le_one (x := y) K ℂ (Subtype.coe_ne_coe.mp hz₀)
    (coe_isIntegral_iff.mp <| isIntegral_of_mahlerMeasure_eq_one h hz)
    fun φ ↦ norm_root_le_one_of_mahlerMeasure_eq_one h ?_
  rw [mem_aroots] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have H (ψ : K →+* ℂ) : ψ ((aeval y) p) = (aeval (ψ y)) p := by
    conv_rhs => rw [← map_id (p := p)]
    exact p.map_aeval_eq_aeval_map (by ext; simp) y
  rw [← H, map_eq_zero_iff _ φ.injective,
    ← map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ↥K ℂ), H]
  exact hz.2

include h hz₀ hz in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex nonzero roots are
roots of unity. -/
/-
**Polynomial.isPrimitiveRoot_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：isPrimitiveRoot_of_mahlerMeasure_eq_one : exists n, 0 < n ∧ IsPrimitiveRoo
t z n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one`：pow_eq_one_of_mahlerMeasu
re_eq_one : exists n, 0 < n ∧ z ^ n = 1
· 使用引理 `IsPrimitiveRoot.exists_pos`：exists_pos {k : Nat} (hζ : ζ ^ k = 1) (hk : 
k != 0) : exists k' > 0, IsPrimitiveRoot ζ k'

--- 原说明 ---
If an integer polynomial has Mahler measure equal to 1, then all its complex non
zero roots are
roots of unity.
-/
theorem isPrimitiveRoot_of_mahlerMeasure_eq_one : ∃ n, 0 < n ∧ IsPrimitiveRoot z n := by
  obtain ⟨_, _, hz_pow⟩ := pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz
  exact IsPrimitiveRoot.exists_pos hz_pow (by omega)

include h in
/-- If an integer non-constant polynomial has Mahler measure equal to 1 and is not a multiple of
`X`, then it is divisible by a cyclotomic polynomial. -/
/-
**Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：cyclotomic_dvd_of_mahlerMeasure_eq_one (hX : ¬ X ∣ p) (hpdeg : p.degree !=
 0) : exists n, 0 < n ∧ cyclotomic n Int ∣ p
参数：hX : ¬ X ∣ p；hpdeg : p.degree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_map_eq_of_injective`：degree_map_eq_of_injective {f : R
 ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).degree = p.d
egree
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_zero_eq_aeval_zero`：coeff_zero_eq_aeval_zero (p : R[X])
 : p.coeff 0 = aeval 0 p
· 使用定理 `Polynomial.eval_zero_map`：eval_zero_map (f : R ->+* S) (p : R[X]) : (p.m
ap f).eval 0 = f (p.eval 0)
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Polynomial.isPrimitiveRoot_of_mahlerMeasure_eq_one`：isPrimitiveRoot_of_m
ahlerMeasure_eq_one : exists n, 0 < n ∧ IsPrimitiveRoot z n
· 使用定理 `Polynomial.cyclotomic_eq_minpoly`：cyclotomic_eq_minpoly {n : Nat} {K : T
ype*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : 
cyclotomic n Int = min…
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `Polynomial.isIntegral_of_mahlerMeasure_eq_one`：isIntegral_of_mahlerMeasu
re_eq_one : IsIntegral Int z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…

--- 原说明 ---
If an integer non-constant polynomial has Mahler measure equal to 1 and is not a
 multiple of
`X`, then it is divisible by a cyclotomic polynomial.
-/
theorem cyclotomic_dvd_of_mahlerMeasure_eq_one (hX : ¬ X ∣ p) (hpdeg : p.degree ≠ 0) :
    ∃ n, 0 < n ∧ cyclotomic n ℤ ∣ p := by
  have hpdegC : (p.map (castRingHom ℂ)).degree ≠ 0 := by
    rwa [p.degree_map_eq_of_injective (castRingHom ℂ).injective_int]
  obtain ⟨z, _⟩ := Splits.exists_eval_eq_zero (IsAlgClosed.splits <| p.map (castRingHom ℂ))
    hpdegC
  have hz₀ : z ≠ 0 := by
    contrapose hX
    simp_all [X_dvd_iff, coeff_zero_eq_aeval_zero]
  have h_z_root : z ∈ p.aroots ℂ := by aesop
  obtain ⟨m, h_m_pos, h_prim⟩ := isPrimitiveRoot_of_mahlerMeasure_eq_one h hz₀ h_z_root
  use m, h_m_pos
  rw [cyclotomic_eq_minpoly h_prim h_m_pos]
  apply minpoly.isIntegrallyClosed_dvd <| isIntegral_of_mahlerMeasure_eq_one h h_z_root
  exact (mem_aroots.mp h_z_root).2

end Cyclotomic

end Polynomial

