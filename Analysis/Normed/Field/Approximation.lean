/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Approximate roots and polynomials in a normed field

In this file, we prove several approximation lemmas on a normed field.

## Main results
- `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` :  **Continuity of Roots.**
Let `f` and `g` be two monic polynomials such that `g` splits. If the coefficients of two
polynomials `f` and `g` are sufficiently close, then every root of `f` has a corresponding root
of `g` nearby.

- `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` : Let `K` be a
dense subfield of a normed field `L`. Every monic polynomial in `L` can be approximated by
a monic polynomial in `K` of the same degree.

## TODO
Use the fact that `f.discr` is polynomial of the coefficients of `f` to show that
every polynomial `f` can be approximated by a *separable* polynomial. This result can be used
to show that the completion a separably closed field is algebraically closed, upgrading the
current theorem `IsAlgClosed.of_denseRange`.

## Tags
Approximation, polynomial, normed field, continuity of roots
-/

public section

variable {K L : Type*}

namespace Polynomial

section ContinuityOfRoots

variable [NormedField K] [NormedField L] [NormedAlgebra K L] {f g : Polynomial K}
  {f g : Polynomial K} {ε : ℝ}

/-- **Continuity of Roots.** Let `f` and `g` be two monic polynomials with `g` splits.
If the coefficients of two polynomials `f` and `g` are sufficiently close, then every root of `f`
has a corresponding root of `g` nearby. -/
/-
**Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：exists_roots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : K} (ha : f
.eval a = 0) (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree) 
(hcoeff : forall i : Nat, ‖g.coeff i - f.coeff i‖ < ε) (hg : g.Splits) : exists 
b in g.roots, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : Real)⁻¹ * max ‖
a‖ 1
参数：hε : 0 < ε；ha : f.eval a = 0；hfm : f.Monic；hgm : g.Monic；hdeg : g.natDegree =
 f.natDegree；hcoeff : forall i : Nat, ‖g.coeff i - f.coeff i‖ < ε；hg : g.Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_hom'`：prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M 
N] [MonoidHomClass F M N] (f : F) (g : ι -> M) : (s.map fun i => f <| g i).prod 
= f (s.m…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MulRingSeminormClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} [inst : NonAssocRing α] [inst_1 : Se
miring β]   [inst_2 : PartialOrder …
· 使用定理 `MulRingNormClass.toMulRingSeminormClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : NonAssocRing α} {inst_1 : Semiring
 β}   {inst_2 : PartialOrder …
· 使用定理 `Polynomial.Splits.eval_eq_prod_roots_of_monic`：∀ {R : Type u_1} [inst : 
CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic → ∀ (
x : R), Polynomial.eval x f = (Mult…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.as_sum_range'`：as_sum_range' (p : R[X]) (n : Nat) (hn : p.nat
Degree < n) : p = ∑ i in range n, monomial i (coeff p i)
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Polynomial.natDegree_sub_le`：natDegree_sub_le (p q : R[X]) : natDegree (
p - q) <= max (natDegree p) (natDegree q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
（共 127 条，此处仅展示前 30 条）

--- 原说明 ---
**Continuity of Roots.** Let `f` and `g` be two monic polynomials with `g` split
s.
If the coefficients of two polynomials `f` and `g` are sufficiently close, then 
every root of `f`
has a corresponding root of `g` nearby.
-/
theorem exists_roots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : K} (ha : f.eval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) (hg : g.Splits) :
    ∃ b ∈ g.roots, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  -- Let `a` be a root of `f`. To show there exists a root `b` of `g` such that `‖a - b‖` is small,
  -- it suffices to show that `∏ (b ∈ g.roots) ‖a - b‖` is small.
  suffices this : (g.roots.map fun x => ‖a - x‖).prod <
      ((f.natDegree + 1) * ε) * (max ‖a‖ 1) ^ (f.natDegree : ℝ) by
    by_contra! h
    have := Multiset.prod_map_le_prod_map₀ (fun b ↦ ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ *
        (‖a‖ ⊔ 1)) (fun b ↦ ‖a - b‖) (by intros; positivity) h
    simp only [Multiset.map_const', hg.natDegree_eq_card_roots.symm ▸ hdeg, Multiset.prod_replicate,
      mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : ((f.natDegree + 1) * ε) > 0).le] at this
    rw [inv_mul_cancel₀, Real.rpow_one] at this
    · linarith
    · simp only [ne_eq, Nat.cast_eq_zero, hfm, Monic.natDegree_eq_zero]
      intro h
      simp [h] at ha
  -- `∏ (b ∈ g.roots) ‖a - b‖ = ‖g(a)‖ = ‖(g - f)(a)‖` is small since every
  -- coefficient of `‖g - f‖` is small.
  calc
  _ = (g.roots.map (fun x ↦ NormedField.toMulRingNorm K (a - x))).prod := rfl
  _ = ‖(g.roots.map (fun x ↦ a - x)).prod‖ := by
    rw [g.roots.prod_hom' (NormedField.toMulRingNorm K) (fun x : K ↦ a - x)]
    rfl
  _ = ‖g.eval a‖ := by
    congr
    rw [hg.eval_eq_prod_roots_of_monic hgm]
  _ ≤ ‖g.eval a - f.eval a‖ + ‖f.eval a‖ := by
    convert! norm_add_le (g.eval a - f.eval a) (f.eval a)
    simp
  _ = ‖(∑ i ∈ Finset.range (g.natDegree + 1), C (g.coeff i - f.coeff i) * X ^ i).eval a‖ := by
    rw [← eval_sub]
    simp only [ha, norm_zero, add_zero]
    rw [(g - f).as_sum_range' (g.natDegree + 1)]
    · congr
      simp [← C_mul_X_pow_eq_monomial]
    · simpa [hdeg, Nat.lt_succ_iff] using g.natDegree_sub_le f
  _ ≤ ∑ i ∈ Finset.range (g.natDegree + 1), ‖(g.coeff i - f.coeff i) * a ^ i‖ := by
    have := norm_sum_le (Finset.range (g.natDegree + 1))
        (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).eval a)
    simpa [eval_mul, eval_finsetSum] using this
    -- The following tactic does not work here:
    -- simpa [eval_mul, eval_finsetSum] using norm_sum_le (Finset.range (g.natDegree + 1))
    --     (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).eval a)
  _ < _ := by
    rw [hdeg]
    convert!
      Finset.sum_lt_sum_of_nonempty (g := fun i ↦ ε * (‖a‖ ⊔ 1) ^ ↑f.natDegree)
        (Finset.nonempty_range_add_one) ?_
    · simp [mul_assoc]
    · simp only [Finset.mem_range, norm_mul, norm_pow]
      intro i hi
      apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
      · simpa [← map_sub] using hcoeff i
      · refine (pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ 1) i).trans ?_
        exact pow_le_pow_right₀ (le_max_right ‖a‖ 1) (Nat.le_of_lt_succ hi)
      all_goals positivity

/-- **Continuity of Roots.** A variation of
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` allowing roots of `g` lives in a
field extension. -/
/-
**Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial`。
形式化陈述：exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : L} (ha : 
f.aeval a = 0) (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree
) (hcoeff : forall i : Nat, ‖g.coeff i - f.coeff i‖ < ε) (hg : (g.map (algebraMa
p K L)).Splits) : exists b in g.aroots L, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f
.natDegree : Real)⁻¹ * max ‖a‖ 1
参数：hε : 0 < ε；ha : f.aeval a = 0；hfm : f.Monic；hgm : g.Monic；hdeg : g.natDegree 
= f.natDegree；hcoeff : forall i : Nat, ‖g.coeff i - f.coeff i‖ < ε；hg : (g.map (
algebraMap K L)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`：exists_roots_n
orm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : K} (ha : f.eval a = 0) (hfm : 
f.Monic) (hgm : g.Monic) (hdeg : g.natDegree =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α

--- 原说明 ---
**Continuity of Roots.** A variation of
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` allowing roots of `g`
 lives in a
field extension.
-/
theorem exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : L} (ha : f.aeval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) (hg : (g.map (algebraMap K L)).Splits) :
    ∃ b ∈ g.aroots L, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  obtain ⟨b, h1, h2⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (f := f.map (algebraMap K L)) (by simpa using ha) (hfm.map _) (hgm.map _)
      (by simpa using hdeg) (by simpa [← map_sub] using hcoeff) hg
  use b, h1
  simpa using h2

end ContinuityOfRoots

section Approximation

variable [Field K] [NormedField L] [Algebra K L]

/-- If `K` is a dense subfield of `L`, then every monic polynomial in `L` can be
approximated by a monic polynomial in `K` of the same degree. -/
/-
**Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt*
* 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt (hd : D
enseRange (algebraMap K L)) {f : Polynomial L} (hf : f.Monic) {ε : Real} (hε : ε
 > 0) : exists g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ forall n 
: Nat, ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε
参数：hd : DenseRange (algebraMap K L)；hf : f.Monic；hε : ε > 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Polynomial.natDegree_add_eq_left_of_natDegree_lt`：natDegree_add_eq_left_
of_natDegree_lt (h : natDegree q < natDegree p) : natDegree (p + q) = natDegree 
p
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is a dense subfield of `L`, then every monic polynomial in `L` can be
approximated by a monic polynomial in `K` of the same degree.
-/
theorem exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    (hd : DenseRange (algebraMap K L)) {f : Polynomial L} (hf : f.Monic) {ε : ℝ} (hε : ε > 0) :
    ∃ g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ ∀ n : ℕ,
    ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε := by
  by_cases h : f.natDegree = 0
  · use 1
    rw [hf.natDegree_eq_zero.mp]
    · simp only [monic_one, natDegree_one, Polynomial.map_one, sub_self, norm_zero, hε,
      implies_true, and_self]
    · exact h
  choose c hc using fun i ↦ Metric.denseRange_iff.mp hd (f.coeff i) ε hε
  have hdeg : (C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i).natDegree
      = f.natDegree := by
    calc
      _ = (C (1 : K) * X ^ f.natDegree).natDegree := by
        apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
        simp only [map_one, one_mul, natDegree_pow, natDegree_X, mul_one]
        rw [← Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)]
        apply Polynomial.natDegree_sum_le_of_forall_le
        refine fun i hi ↦ (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        simpa [Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)] using hi
      _ = f.natDegree := by
        simp
  use C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i
  refine ⟨?_, hdeg.symm, fun n ↦ ?_⟩
  · rw [Monic, leadingCoeff, hdeg]
    simp
  · rcases lt_trichotomy n f.natDegree with h | h | h
    · simpa [h, ne_of_lt h, ← dist_eq_norm_sub'] using hc n
    · simp [h, hf, hε]
    · simp [not_lt_of_gt h, ne_of_gt h, coeff_eq_zero_of_natDegree_lt h, hε]

end Approximation

end Polynomial

