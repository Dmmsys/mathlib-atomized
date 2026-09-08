/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Data.Finset.Interval
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gagliardo-Nirenberg-Sobolev inequality

In this file we prove the Gagliardo-Nirenberg-Sobolev inequality.
This states that for compactly supported `C¹`-functions between finite-dimensional vector spaces,
we can bound the `L^p`-norm of `u` by the `L^q` norm of the derivative of `u`.
The bound is up to a constant that is independent of the function `u`.
Let `n` be the dimension of the domain.

The main step in the proof, which we dubbed the "grid-lines lemma" below, is a complicated
inductive argument that involves manipulating an `n+1`-fold iterated integral and a product of
`n+2` factors. In each step, one pushes one of the integral inside (all but one of)
the factors of the product using Hölder's inequality. The precise formulation of the induction
hypothesis (`MeasureTheory.GridLines.T_insert_le_T_lmarginal_singleton`) is tricky,
and none of the 5 sources we referenced stated it.

In the formalization we use the operation `MeasureTheory.lmarginal` to work with the iterated
integrals, and use `MeasureTheory.lmarginal_insert'` to conveniently push one of the integrals
inside. The Hölder's inequality step is done using `ENNReal.lintegral_mul_prod_norm_pow_le`.

The conclusions of the main results below are an estimation up to a constant multiple.
We don't really care about this constant, other than that it only depends on some pieces of data,
typically `E`, `μ`, `p` and sometimes also the codomain of `u` or the support of `u`.
We state these constants as separate definitions.

## Main results

* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`:
  The bound holds for `1 ≤ p`, `0 < n` and `q⁻¹ = p⁻¹ - n⁻¹`
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`:
  The bound holds when `1 ≤ p < n`, `0 ≤ q` and `p⁻¹ - n⁻¹ ≤ q⁻¹`.
  Note that in this case the constant depends on the support of `u`.

Potentially also useful:
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`: this is the inequality for `q = 1`.
  In this version, the codomain can be an arbitrary Banach space.
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`: in this version,
  the codomain is assumed to be a Hilbert space, without restrictions on its dimension.
-/

@[expose] public section

open scoped ENNReal NNReal
open Set Function Finset MeasureTheory Measure Filter

noncomputable section

variable {ι : Type*}

local prefix:max "#" => Fintype.card

/-! ## The grid-lines lemma -/

variable {A : ι → Type*} [∀ i, MeasurableSpace (A i)]
  (μ : ∀ i, Measure (A i))

namespace MeasureTheory

section DecidableEq

variable [DecidableEq ι]

namespace GridLines

/-- The "grid-lines operation" (not a standard name) which is central in the inductive proof of the
Sobolev inequality.

For a finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, a finite set `s` of
indices from `ι`, and a (later assumed nonnegative) real number `p`, this operation acts on a
function `f` from `Π i, A i` into the extended nonnegative reals.  The operation is to partially
integrate, in the `s` co-ordinates, the function whose value at `x : Π i, A i` is obtained by
multiplying a certain power of `f` with the product, for each co-ordinate `i` in `s`, of a certain
power of the integral of `f` along the "grid line" in the `i` direction through `x`.

We are most interested in this operation when the set `s` is the universe in `ι`, but as a proxy for
"induction on dimension" we define it for a general set `s` of co-ordinates: the `s`-grid-lines
operation on a function `f` which is constant along the co-ordinates in `sᶜ` is morally (that is, up
to type-theoretic nonsense) the same thing as the universe-grid-lines operation on the associated
function on the "lower-dimensional" space `Π i : s, A i`. -/
/-
**MeasureTheory.GridLines.T** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.GridLines`。
形式化陈述：T (p : Real) (f : (forall i, A i) -> Real>=0∞) (s : Finset ι) : (forall i,
 A i) -> Real>=0∞
参数：p : Real；f : (forall i, A i) -> Real>=0∞；s : Finset ι。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "grid-lines operation" (not a standard name) which is central in the inducti
ve proof of the
Sobolev inequality.

For a finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, a 
finite set `s` of
indices from `ι`, and a (later assumed nonnegative) real number `p`, this operat
ion acts on a
function `f` from `Π i, A i` into the extended nonnegative reals.  The operation
 is to partially
integrate, in the `s` co-ordinates, the function whose value at `x : Π i, A i` i
s obtained by
multiplying a certain power of `f` with the product, for each co-ordinate `i` in
 `s`, of a certain
power of the integral of `f` along the "grid line" in the `i` direction through 
`x`.

We are most interested in this operation when the set `s` is the universe in `ι`
, but as a proxy for
"induction on dimension" we define it for a general set `s` of co-ordinates: the
 `s`-grid-lines
operation on a function `f` which is constant along the co-ordinates in `sᶜ` is 
morally (that is, up
to type-theoretic nonsense) the same thing as the universe-grid-lines operation 
on the associated
function on the "lower-dimensional" space `Π i : s, A i`.
-/
def T (p : ℝ) (f : (∀ i, A i) → ℝ≥0∞) (s : Finset ι) : (∀ i, A i) → ℝ≥0∞ :=
  ∫⋯∫⁻_s, f ^ (1 - (s.card - 1 : ℝ) * p) * ∏ i ∈ s, (∫⋯∫⁻_{i}, f ∂μ) ^ p ∂μ

variable {p : ℝ}
/-
**MeasureTheory.GridLines.T_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.GridLi
nes`。
形式化陈述：∀ {ι : Type u_1} {A : ι → Type u_2} [inst : (i : ι) → MeasurableSpace (A i
)] (μ : (i : ι) → MeasureTheory.Measure (A i))   [inst_1 : DecidableEq ι] {p : ℝ
} [inst_2 : Fintype ι] [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)]   (f : ((i :
 ι) → A i) → ENNReal) (x : (i : ι) → A i),   MeasureTheory.GridLines.T μ p f Fin
set.univ x =     ∫⁻ (x : (i : ι) → A i),       f x ^ (1 - (↑(Fintype.card ι) - 1
) * p) *         ∏ i, (∫⁻ (t : A i), f (Function.update x i t) ∂μ i) ^ p ∂Measur
eTheory.Measure.pi μ
参数：i : ι；A i；μ : (i : ι) → MeasureTheory.Measure (A i)；i : ι；μ i；f : ((i : ι) → 
A i) → ENNReal；x : (i : ι) → A i；x : (i : ι) → A i；1 - (↑(Fintype.card ι) - 1) *
 p；∫⁻ (t : A i), f (Function.update x i t) ∂μ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lmarginal.congr_simp`：∀ {δ : Type u_1} {X : δ → Type u_3} 
[inst : (i : δ) → MeasurableSpace (X i)] {inst_1 : DecidableEq δ}   [inst_2 : De
cidableEq δ] (μ μ_1 : (i…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.lmarginal_singleton`：lmarginal_singleton (f : (forall i, X
 i) -> Real>=0∞) (i : δ) : ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x
 i xᵢ) ∂μ i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lmarginal_univ`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst 
: (i : δ) → MeasurableSpace (X i)] {μ : (i : δ) → MeasureTheory.Measure (X i)}  
 [inst_1 : Decidab…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma T_univ [Fintype ι] [∀ i, SigmaFinite (μ i)] (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f univ x =
    ∫⁻ (x : ∀ i, A i), (f x ^ (1 - (#ι - 1 : ℝ) * p)
    * ∏ i : ι, (∫⁻ t : A i, f (update x i t) ∂(μ i)) ^ p) ∂(.pi μ) := by
  simp [T, lmarginal_singleton]
/-
**MeasureTheory.GridLines.T_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.GridL
ines`。
形式化陈述：∀ {ι : Type u_1} {A : ι → Type u_2} [inst : (i : ι) → MeasurableSpace (A i
)] (μ : (i : ι) → MeasureTheory.Measure (A i))   [inst_1 : DecidableEq ι] {p : ℝ
} (f : ((i : ι) → A i) → ENNReal) (x : (i : ι) → A i),   MeasureTheory.GridLines
.T μ p f ∅ x = f x ^ (1 + p)
参数：i : ι；A i；μ : (i : ι) → MeasureTheory.Measure (A i)；f : ((i : ι) → A i) → ENN
Real；x : (i : ι) → A i；1 + p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lmarginal.congr_simp`：∀ {δ : Type u_1} {X : δ → Type u_3} 
[inst : (i : δ) → MeasurableSpace (X i)] {inst_1 : DecidableEq δ}   [inst_2 : De
cidableEq δ] (μ μ_1 : (i…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lmarginal_empty`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst
 : (i : δ) → MeasurableSpace (X i)] (μ : (i : δ) → MeasureTheory.Measure (X i)) 
  [inst_1 : Decidab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma T_empty (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f ∅ x = f x ^ (1 + p) := by
  simp [T]

/-- The main inductive step in the grid-lines lemma for the Gagliardo-Nirenberg-Sobolev inequality.

The grid-lines operation `GridLines.T` on a nonnegative function on a finitary product type is
less than or equal to the grid-lines operation of its partial integral in one co-ordinate
(the latter intuitively considered as a function on a space "one dimension down"). -/
/-
**MeasureTheory.GridLines.T_insert_le_T_lmarginal_singleton** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.GridLines`。
形式化陈述：T_insert_le_T_lmarginal_singleton [forall i, SigmaFinite (μ i)] (hp₀ : 0 <
= p) (s : Finset ι) (hp : (s.card : Real) * p <= 1) (i : ι) (hi : i ∉ s) {f : (f
orall i, A i) -> Real>=0∞} (hf : Measurable f) : T μ p f (insert i s) <= T μ p (
∫⋯∫⁻_{i}, f ∂μ) s
参数：μ i；hp₀ : 0 <= p；s : Finset ι；hp : (s.card : Real) * p <= 1；i : ι；hi : i ∉ s；
forall i, A i；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `MeasureTheory.lmarginal_insert'`：lmarginal_insert' (f : (forall i, X i) 
-> Real>=0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s) : ∫⋯∫⁻_insert i s, f ∂μ = 
∫⋯∫⁻_s, (fun x => ∫⁻ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
The main inductive step in the grid-lines lemma for the Gagliardo-Nirenberg-Sobo
lev inequality.

The grid-lines operation `GridLines.T` on a nonnegative function on a finitary p
roduct type is
less than or equal to the grid-lines operation of its partial integral in one co
-ordinate
(the latter intuitively considered as a function on a space "one dimension down"
).
-/
theorem T_insert_le_T_lmarginal_singleton [∀ i, SigmaFinite (μ i)] (hp₀ : 0 ≤ p) (s : Finset ι)
    (hp : (s.card : ℝ) * p ≤ 1)
    (i : ι) (hi : i ∉ s) {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    T μ p f (insert i s) ≤ T μ p (∫⋯∫⁻_{i}, f ∂μ) s := by
  /- The proof is a tricky computation that relies on Hölder's inequality at its heart.
  The left-hand-side is an `|s|+1`-times iterated integral. Let `xᵢ` denote the `i`-th variable.
  We first push the integral over the `i`-th variable as the
  innermost integral. This is done in a single step with `MeasureTheory.lmarginal_insert'`,
  but in fact hides a repeated application of Fubini's theorem.
  The integrand is a product of `|s|+2` factors, in `|s|+1` of them we integrate over one
  additional variable. We split off the factor that integrates over `xᵢ`,
  and apply Hölder's inequality to the remaining factors (whose powers sum exactly to 1).
  After reordering factors, and combining two factors into one we obtain the right-hand side. -/
  calc T μ p f (insert i s)
      = ∫⋯∫⁻_insert i s,
            f ^ (1 - (s.card : ℝ) * p) * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) ^ p ∂μ := by
          -- unfold `T` and reformulate the exponents
          simp_rw [T, card_insert_of_notMem hi]
          congr!
          push_cast
          ring
    _ = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ (t : A i),
            (f (update x i t) ^ (1 - (s.card : ℝ) * p)
            * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) (update x i t) ^ p) ∂(μ i)) ∂μ := by
          -- pull out the integral over `xᵢ`
          rw [lmarginal_insert' _ _ hi]
          · simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
          · change Measurable (fun x ↦ _)
            simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
            refine (hf.pow_const _).mul <| Finset.measurable_fun_prod _ ?_
            exact fun _ _ ↦ hf.lmarginal μ |>.pow_const _
    _ ≤ T μ p (∫⋯∫⁻_{i}, f ∂μ) s := lmarginal_mono (s := s) (fun x ↦ ?_)
  -- The remainder of the computation happens within an `|s|`-fold iterated integral
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
  set X := update x i
  have hF₁ : ∀ {j : ι}, Measurable fun t ↦ (∫⋯∫⁻_{j}, f ∂μ) (X t) :=
    fun {_} ↦ hf.lmarginal μ |>.comp <| measurable_update _
  have hF₀ : Measurable fun t ↦ f (X t) := hf.comp <| measurable_update _
  let k : ℝ := s.card
  have hk' : 0 ≤ 1 - k * p := by linarith only [hp]
  calc ∫⁻ t, f (X t) ^ (1 - k * p)
          * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p ∂(μ i)
      = ∫⁻ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) ^ p * (f (X t) ^ (1 - k * p)
          * ∏ j ∈ s, ((∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p)) ∂(μ i) := by
              -- rewrite integrand so that `(∫⋯∫⁻_insert i s, f ∂μ) ^ p` comes first
              clear_value X
              congr! 2 with t
              simp_rw [prod_insert hi]
              ring_nf
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ∫⁻ t, f (X t) ^ (1 - k * p) * ∏ j ∈ s, ((∫⋯∫⁻_{j}, f ∂μ) (X t)) ^ p ∂(μ i) := by
              -- pull out this constant factor
              have : ∀ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) = (∫⋯∫⁻_{i}, f ∂μ) x := by
                intro t
                rw [lmarginal_update_of_mem]
                exact Iff.mpr Finset.mem_singleton rfl
              simp_rw [this]
              rw [lintegral_const_mul]
              exact (hF₀.pow_const _).mul <| Finset.measurable_fun_prod _ fun _ _ ↦ hF₁.pow_const _
    _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ((∫⁻ t, f (X t) ∂μ i) ^ (1 - k * p)
          * ∏ j ∈ s, (∫⁻ t, (∫⋯∫⁻_{j}, f ∂μ) (X t) ∂μ i) ^ p) := by
              -- apply Hölder's inequality
              gcongr
              apply ENNReal.lintegral_mul_prod_norm_pow_le
              · exact hF₀.aemeasurable
              · intros
                exact hF₁.aemeasurable
              · simp only [sum_const, nsmul_eq_mul]
                ring
              · exact hk'
              · exact fun _ _ ↦ hp₀
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ((∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - k * p) * ∏ j ∈ s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p) := by
              -- absorb the newly-created integrals into `∫⋯∫`
              congr! 2
              · rw [lmarginal_singleton]
              refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ ({j} : Finset ι) := by
                simp only [Finset.mem_singleton] at hj ⊢
                exact fun h ↦ hi (h ▸ hj)
              rw [lmarginal_insert _ hf hi']
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ (p + (1 - k * p)) * ∏ j ∈ s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p := by
              -- combine two `(∫⋯∫⁻_insert i s, f ∂μ) x` terms
              rw [ENNReal.rpow_add_of_nonneg]
              · ring
              · exact hp₀
              · exact hk'
    _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - (s.card - 1 : ℝ) * p) *
          ∏ j ∈ s, (∫⋯∫⁻_{j}, (∫⋯∫⁻_{i}, f ∂μ) ∂μ) x ^ p := by
              -- identify the result with the RHS integrand
              congr! 2 with j hj
              · ring
              · congr! 1
                rw [← lmarginal_union μ f hf]
                · congr
                  rw [Finset.union_comm]
                  rfl
                · rw [Finset.disjoint_singleton]
                  exact fun h ↦ hi (h ▸ hj)

/-- Auxiliary result for the grid-lines lemma.  Given a nonnegative function on a finitary product
type indexed by `ι`, and a set `s` in `ι`, consider partially integrating over the variables in
`sᶜ` and performing the "grid-lines operation" (see `GridLines.T`) to the resulting function in the
variables `s`.  This theorem states that this operation decreases as the number of grid-lines taken
increases. -/
/-
**MeasureTheory.GridLines.T_lmarginal_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.GridLines`。
形式化陈述：T_lmarginal_antitone [Fintype ι] [forall i, SigmaFinite (μ i)] (hp₀ : 0 <=
 p) (hp : (#ι - 1 : Real) * p <= 1) {f : (forall i, A i) -> Real>=0∞} (hf : Meas
urable f) : Antitone (fun s => T μ p (∫⋯∫⁻_sᶜ, f ∂μ) s)
参数：μ i；hp₀ : 0 <= p；hp : (#ι - 1 : Real) * p <= 1；forall i, A i；hf : Measurable 
f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.antitone_iff_forall_insert_le`：antitone_iff_forall_insert_le : An
titone f ↔ forall s ⦃a⦄, a ∉ s -> f (insert a s) <= f s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lmarginal_union`：lmarginal_union (f : (forall i, X i) -> R
eal>=0∞) (hf : Measurable f) (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_
s, ∫⋯∫⁻_t, f ∂μ ∂μ
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `Finset.notMem_compl`：notMem_compl : a ∉ sᶜ ↔ a in s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.insert_compl_insert`：insert_compl_insert (ha : a ∉ s) : insert a 
(insert a s)ᶜ = sᶜ
· 使用定理 `MeasureTheory.GridLines.T_insert_le_T_lmarginal_singleton`：T_insert_le_T
_lmarginal_singleton [forall i, SigmaFinite (μ i)] (hp₀ : 0 <= p) (s : Finset ι)
 (hp : (s.card : Real) * p <= 1) (i : ι) (hi : …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Finset.card_add_card_compl`：Finset.card_add_card_compl [DecidableEq α] [
Fintype α] (s : Finset α) : #s + #sᶜ = Fintype.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary result for the grid-lines lemma.  Given a nonnegative function on a fi
nitary product
type indexed by `ι`, and a set `s` in `ι`, consider partially integrating over t
he variables in
`sᶜ` and performing the "grid-lines operation" (see `GridLines.T`) to the result
ing function in the
variables `s`.  This theorem states that this operation decreases as the number 
of grid-lines taken
increases.
-/
theorem T_lmarginal_antitone [Fintype ι] [∀ i, SigmaFinite (μ i)]
    (hp₀ : 0 ≤ p) (hp : (#ι - 1 : ℝ) * p ≤ 1) {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    Antitone (fun s ↦ T μ p (∫⋯∫⁻_sᶜ, f ∂μ) s) := by
  -- Reformulate (by induction): a function is decreasing on `Finset ι` if it decreases under the
  -- insertion of any element to any set.
  rw [Finset.antitone_iff_forall_insert_le]
  intro s i hi
  -- apply the lemma designed to encapsulate the inductive step
  convert! T_insert_le_T_lmarginal_singleton μ hp₀ s ?_ i hi (hf.lmarginal μ) using 2
  · rw [← lmarginal_union μ f hf]
    · rw [← insert_compl_insert hi]
      rfl
    rw [Finset.disjoint_singleton_left, notMem_compl]
    exact mem_insert_self i s
  · -- the main nontrivial point is to check that an exponent `p` satisfying `0 ≤ p` and
    -- `(#ι - 1) * p ≤ 1` is in the valid range for the inductive-step lemma
    refine le_trans ?_ hp
    gcongr
    suffices (s.card : ℝ) + 1 ≤ #ι by linarith
    rw [← card_add_card_compl s]
    norm_cast
    gcongr
    have hi' : sᶜ.Nonempty := ⟨i, by rwa [Finset.mem_compl]⟩
    rwa [← card_pos] at hi'

end GridLines

/-- The "grid-lines lemma" (not a standard name), stated with a general parameter `p` as the
exponent.  Compare with `lintegral_prod_lintegral_pow_le`.

For any finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, for any
nonnegative real number `p` such that `(#ι - 1) * p ≤ 1`, for any function `f` from `Π i, A i` into
the extended nonnegative reals, we consider an associated "grid-lines quantity", the integral of an
associated function from `Π i, A i` into the extended nonnegative reals.  The value of this function
at `x : Π i, A i` is obtained by multiplying a certain power of `f` with the product, for each
co-ordinate `i`, of a certain power of the integral of `f` along the "grid line" in the `i`
direction through `x`.

This lemma bounds the Lebesgue integral of the grid-lines quantity by a power of the Lebesgue
integral of `f`. -/
/-
**MeasureTheory.lintegral_mul_prod_lintegral_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：lintegral_mul_prod_lintegral_pow_le [Fintype ι] [forall i, SigmaFinite (μ 
i)] {p : Real} (hp₀ : 0 <= p) (hp : (#ι - 1 : Real) * p <= 1) {f : (forall i : ι
, A i) -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ^ (1 - (#ι - 1 : Real) * p) 
* ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ p ∂.pi μ <= (∫⁻ x, f x ∂.pi μ) ^ (1 + p
)
参数：μ i；hp₀ : 0 <= p；hp : (#ι - 1 : Real) * p <= 1；forall i : ι, A i；hf : Measura
ble f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_of_isEmpty`：lintegral_of_isEmpty {α} [Measurable
Space α] [IsEmpty α] (μ : Measure α) (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `MeasureTheory.GridLines.T.congr_simp`：∀ {ι : Type u_1} {A : ι → Type u_2
} [inst : (i : ι) → MeasurableSpace (A i)]   (μ μ_1 : (i : ι) → MeasureTheory.Me
asure (A i)),   μ = μ_1 → …
· 使用定理 `Finset.compl_univ`：compl_univ : (univ : Finset α)ᶜ = ∅
· 使用定理 `MeasureTheory.lmarginal_empty`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst
 : (i : δ) → MeasurableSpace (X i)] (μ : (i : δ) → MeasureTheory.Measure (X i)) 
  [inst_1 : Decidab…
· 使用定理 `MeasureTheory.GridLines.T_univ`：∀ {ι : Type u_1} {A : ι → Type u_2} [ins
t : (i : ι) → MeasurableSpace (A i)] (μ : (i : ι) → MeasureTheory.Measure (A i))
   [inst_1 : Decidab…
· 使用定理 `Finset.compl_empty`：compl_empty : (∅ : Finset α)ᶜ = univ
· 使用定理 `MeasureTheory.lmarginal_univ`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst 
: (i : δ) → MeasurableSpace (X i)] {μ : (i : δ) → MeasureTheory.Measure (X i)}  
 [inst_1 : Decidab…
· 使用定理 `MeasureTheory.GridLines.T_empty`：∀ {ι : Type u_1} {A : ι → Type u_2} [in
st : (i : ι) → MeasurableSpace (A i)] (μ : (i : ι) → MeasureTheory.Measure (A i)
)   [inst_1 : Decidab…
· 使用定理 `MeasureTheory.GridLines.T_lmarginal_antitone`：T_lmarginal_antitone [Fint
ype ι] [forall i, SigmaFinite (μ i)] (hp₀ : 0 <= p) (hp : (#ι - 1 : Real) * p <=
 1) {f : (forall i, A i) -> Real>=…

--- 原说明 ---
The "grid-lines lemma" (not a standard name), stated with a general parameter `p
` as the
exponent.  Compare with `lintegral_prod_lintegral_pow_le`.

For any finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, 
for any
nonnegative real number `p` such that `(#ι - 1) * p ≤ 1`, for any function `f` f
rom `Π i, A i` into
the extended nonnegative reals, we consider an associated "grid-lines quantity",
 the integral of an
associated function from `Π i, A i` into the extended nonnegative reals.  The va
lue of this function
at `x : Π i, A i` is obtained by multiplying a certain power of `f` with the pro
duct, for each
co-ordinate `i`, of a certain power of the integral of `f` along the "grid line"
 in the `i`
direction through `x`.

This lemma bounds the Lebesgue integral of the grid-lines quantity by a power of
 the Lebesgue
integral of `f`.
-/
theorem lintegral_mul_prod_lintegral_pow_le
    [Fintype ι] [∀ i, SigmaFinite (μ i)] {p : ℝ} (hp₀ : 0 ≤ p)
    (hp : (#ι - 1 : ℝ) * p ≤ 1) {f : (∀ i : ι, A i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ^ (1 - (#ι - 1 : ℝ) * p) * ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ p ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ (1 + p) := by
  cases isEmpty_or_nonempty (∀ i, A i)
  · simp
  inhabit ∀ i, A i
  have H : (∅ : Finset ι) ≤ Finset.univ := Finset.empty_subset _
  simpa [lmarginal_univ] using GridLines.T_lmarginal_antitone μ hp₀ hp hf H default

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
/-- Special case of the grid-lines lemma `lintegral_mul_prod_lintegral_pow_le`, taking the extremal
exponent `p = (#ι - 1)⁻¹`. -/
/-
**MeasureTheory.lintegral_prod_lintegral_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：lintegral_prod_lintegral_pow_le [Fintype ι] [forall i, SigmaFinite (μ i)] 
{p : Real} (hp : Real.HolderConjugate #ι p) {f} (hf : Measurable f) : ∫⁻ x, ∏ i,
 (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ ((1 : Real) / (#ι - 1 : Real)) ∂.pi μ <= (∫⁻ 
x, f x ∂.pi μ) ^ p
参数：μ i；hp : Real.HolderConjugate #ι p；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Real.HolderTriple.lt`：lt : r < p
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
Special case of the grid-lines lemma `lintegral_mul_prod_lintegral_pow_le`, taki
ng the extremal
exponent `p = (#ι - 1)⁻¹`.
-/
theorem lintegral_prod_lintegral_pow_le [Fintype ι] [∀ i, SigmaFinite (μ i)]
    {p : ℝ} (hp : Real.HolderConjugate #ι p)
    {f} (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ p := by
  have : Nontrivial ι :=
    Fintype.one_lt_card_iff_nontrivial.mp (by exact_mod_cast hp.lt)
  have h0 : (1 : ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have h1 : (0 : ℝ) < #ι - 1 := by linarith
  have h2 : 0 ≤ ((1 : ℝ) / (#ι - 1 : ℝ)) := by positivity
  have h3 : (#ι - 1 : ℝ) * ((1 : ℝ) / (#ι - 1 : ℝ)) ≤ 1 := by field_simp; rfl
  have h4 : p = 1 + 1 / (↑#ι - 1) := by simp [field]; rw [mul_comm, hp.sub_one_mul_conj]
  rw [h4]
  convert lintegral_mul_prod_lintegral_pow_le μ h2 h3 hf
  field_simp
  simp

end DecidableEq

/-! ## The Gagliardo-Nirenberg-Sobolev inequality -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on `ℝⁿ`, for `n ≥ 2`.  (More literally we encode `ℝⁿ` as
`ι → ℝ` where `n := #ι` is finite and at least 2.)  Then the Lebesgue integral of the pointwise
expression `|u x| ^ (n / (n - 1))` is bounded above by the `n / (n - 1)`-th power of the Lebesgue
integral of the Fréchet derivative of `u`.

For a basis-free version, see `lintegral_pow_le_pow_lintegral_fderiv`. -/
/-
**MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv_aux** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：lintegral_pow_le_pow_lintegral_fderiv_aux [Fintype ι] {p : Real} (hp : Rea
l.HolderConjugate #ι p) {u : (ι -> Real) -> F} (hu : ContDiff Real 1 u) (h2u : H
asCompactSupport u) : ∫⁻ x, ‖u x‖ₑ ^ p <= (∫⁻ x, ‖fderiv Real u x‖ₑ) ^ p
参数：hp : Real.HolderConjugate #ι p；ι -> Real；hu : ContDiff Real 1 u；h2u : HasComp
actSupport u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Real.HolderTriple.lt`：lt : r < p
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 135 条，此处仅展示前 30 条）

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
compactly-supported function `u` on `ℝⁿ`, for `n ≥ 2`.  (More literally we encod
e `ℝⁿ` as
`ι → ℝ` where `n := #ι` is finite and at least 2.)  Then the Lebesgue integral o
f the pointwise
expression `|u x| ^ (n / (n - 1))` is bounded above by the `n / (n - 1)`-th powe
r of the Lebesgue
integral of the Fréchet derivative of `u`.

For a basis-free version, see `lintegral_pow_le_pow_lintegral_fderiv`.
-/
theorem lintegral_pow_le_pow_lintegral_fderiv_aux [Fintype ι]
    {p : ℝ} (hp : Real.HolderConjugate #ι p)
    {u : (ι → ℝ) → F} (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) :
    ∫⁻ x, ‖u x‖ₑ ^ p ≤ (∫⁻ x, ‖fderiv ℝ u x‖ₑ) ^ p := by
  classical
  /- For a function `f` in one variable and `t ∈ ℝ` we have
  `|f(t)| = `|∫_{-∞}^t Df(s)∂s| ≤ ∫_ℝ |Df(s)| ∂s` where we use the fundamental theorem of calculus.
  For each `x ∈ ℝⁿ` we let `u` vary in one of the `n` coordinates and apply the inequality above.
  By taking the product over these `n` factors, raising them to the power `(n-1)⁻¹` and integrating,
  we get the inequality `∫ |u| ^ (n/(n-1)) ≤ ∫ x, ∏ i, (∫ xᵢ, |Du(update x i xᵢ)|)^(n-1)⁻¹`.
  The result then follows from the grid-lines lemma. -/
  have : (1 : ℝ) ≤ ↑#ι - 1 := by
    have hι : (2 : ℝ) ≤ #ι := by exact_mod_cast hp.lt
    linarith
  calc ∫⁻ x, ‖u x‖ₑ ^ p
      = ∫⁻ x, (‖u x‖ₑ ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        -- a little algebraic manipulation of the exponent
        congr! 2 with x
        rw [← ENNReal.rpow_mul, hp.conjugate_eq]
        field_simp
    _ = ∫⁻ x, ∏ _i : ι, ‖u x‖ₑ ^ (1 / (#ι - 1 : ℝ)) := by
        -- express the left-hand integrand as a product of identical factors
        congr! 2 with x
        simp_rw [prod_const]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, ‖fderiv ℝ u (update x i xᵢ)‖ₑ) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := ?_
    _ ≤ (∫⁻ x, ‖fderiv ℝ u x‖ₑ) ^ p := by
        -- apply the grid-lines lemma
        apply lintegral_prod_lintegral_pow_le _ hp
        fun_prop
  -- we estimate |u x| using the fundamental theorem of calculus.
  gcongr with x i
  calc ‖u x‖ₑ
    _ ≤ ∫⁻ xᵢ in Iic (x i), ‖deriv (u ∘ update x i) xᵢ‖ₑ := by
        apply le_trans (by simp) (HasCompactSupport.enorm_le_lintegral_Ici_deriv _ _ _)
        · exact hu.comp (by convert! contDiff_update 1 x i)
        · exact h2u.comp_isClosedEmbedding (isClosedEmbedding_update x i)
    _ ≤ ∫⁻ xᵢ, ‖fderiv ℝ u (update x i xᵢ)‖ₑ := ?_
  gcongr with y
  · exact Measure.restrict_le_self
  -- bound the derivative which appears
  calc ‖deriv (u ∘ update x i) y‖ₑ = ‖fderiv ℝ u (update x i y) (deriv (update x i) y)‖ₑ := by
        rw [fderiv_comp_deriv _ (hu.differentiable one_ne_zero).differentiableAt
          (hasDerivAt_update x i y).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i y)‖ₑ * ‖deriv (update x i) y‖ₑ := ContinuousLinearMap.le_opENorm _ _
    _ ≤ ‖fderiv ℝ u (update x i y)‖ₑ := by simp [deriv_update, Pi.enorm_single]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]

open Module

/-- The constant factor occurring in the conclusion of `lintegral_pow_le_pow_lintegral_fderiv`.
It only depends on `E`, `μ` and `p`.
It is determined by the ratio of the measures on `E` and `ℝⁿ` and
the operator norm of a chosen equivalence `E ≃ ℝⁿ` (raised to suitable powers involving `p`). -/
irreducible_def lintegralPowLePowLIntegralFDerivConst (p : ℝ) : ℝ≥0 := by
  let ι := Fin (finrank ℝ E)
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by
    rw [finrank_fintype_fun_eq_card, Fintype.card_fin (finrank ℝ E)]
  let e : E ≃L[ℝ] ι → ℝ := ContinuousLinearEquiv.ofFinrankEq this
  let c := addHaarScalarFactor μ ((volume : Measure (ι → ℝ)).map e.symm)
  exact (c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p) * (c ^ p)⁻¹

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n ≥ 2`, equipped
with Haar measure. Then the Lebesgue integral of the pointwise expression
`|u x| ^ (n / (n - 1))` is bounded above by a constant times the `n / (n - 1)`-th power of the
Lebesgue integral of the Fréchet derivative of `u`. -/
/-
**MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：lintegral_pow_le_pow_lintegral_fderiv {u : E -> F} (hu : ContDiff Real 1 u
) (h2u : HasCompactSupport u) {p : Real} (hp : Real.HolderConjugate (finrank Rea
l E) p) : ∫⁻ x, ‖u x‖ₑ ^ p ∂μ <= lintegralPowLePowLIntegralFDerivConst μ p * (∫⁻
 x, ‖fderiv Real u x‖ₑ ∂μ) ^ p
参数：hu : ContDiff Real 1 u；h2u : HasCompactSupport u；hp : Real.HolderConjugate (f
inrank Real E) p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Real.HolderTriple.nonneg`：nonneg : 0 <= p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `ContinuousLinearEquiv.isAddHaarMeasure_map`：∀ {E : Type u_3} {F : Type u
_4} {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [i
nst_2 : AddCommGroup E] [inst_3 …
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
（共 97 条，此处仅展示前 30 条）

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n ≥ 
2`, equipped
with Haar measure. Then the Lebesgue integral of the pointwise expression
`|u x| ^ (n / (n - 1))` is bounded above by a constant times the `n / (n - 1)`-t
h power of the
Lebesgue integral of the Fréchet derivative of `u`.
-/
theorem lintegral_pow_le_pow_lintegral_fderiv {u : E → F}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : ℝ} (hp : Real.HolderConjugate (finrank ℝ E) p) :
    ∫⁻ x, ‖u x‖ₑ ^ p ∂μ ≤
      lintegralPowLePowLIntegralFDerivConst μ p * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂μ) ^ p := by
  /- We reduce to the case where `E` is `ℝⁿ`, for which we have already proved the result using
  an explicit basis in `MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv_aux`.
  This proof is not too hard, but takes quite some steps, reasoning about the equivalence
  `e : E ≃ ℝⁿ`, relating the measures on each sides of the equivalence,
  and estimating the derivative using the chain rule. -/
  set C := lintegralPowLePowLIntegralFDerivConst μ p
  let ι := Fin (finrank ℝ E)
  have hιcard : #ι = finrank ℝ E := Fintype.card_fin (finrank ℝ E)
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by simp [hιcard]
  let e : E ≃L[ℝ] ι → ℝ := ContinuousLinearEquiv.ofFinrankEq this
  have hp : Real.HolderConjugate #ι p := by rwa [hιcard]
  have h0p : 0 ≤ p := hp.symm.nonneg
  let c := addHaarScalarFactor μ ((volume : Measure (ι → ℝ)).map e.symm)
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure ..
  have h2c : μ = c • ((volume : Measure (ι → ℝ)).map e.symm) := isAddLeftInvariant_eq_smul ..
  have h3c : (c : ℝ≥0∞) ≠ 0 := by simp_rw [ne_eq, ENNReal.coe_eq_zero, hc.ne', not_false_eq_true]
  have h0C : C = (c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p) * (c ^ p)⁻¹ := by
    simp_rw [c, ι, C, e, lintegralPowLePowLIntegralFDerivConst]
  have hC : C * c ^ p = c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p := by
    rw [h0C, inv_mul_cancel_right₀ (NNReal.rpow_pos hc).ne']
  simp only [h2c, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
  let v : (ι → ℝ) → F := u ∘ e.symm
  have hv : ContDiff ℝ 1 v := hu.comp e.symm.contDiff
  have h2v : HasCompactSupport v := h2u.comp_homeomorph e.symm.toHomeomorph
  have :=
  calc ∫⁻ x, ‖u x‖ₑ ^ p ∂(volume : Measure (ι → ℝ)).map e.symm
      = ∫⁻ y, ‖v y‖ₑ ^ p := by
        refine lintegral_map ?_ e.symm.continuous.measurable
        borelize F
        exact hu.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const _
    _ ≤ (∫⁻ y, ‖fderiv ℝ v y‖ₑ) ^ p := lintegral_pow_le_pow_lintegral_fderiv_aux hp hv h2v
    _ = (∫⁻ y, ‖(fderiv ℝ u (e.symm y)).comp (fderiv ℝ e.symm y)‖ₑ) ^ p := by
        congr! with y
        apply fderiv_comp _ (hu.differentiable one_ne_zero _)
        exact e.symm.differentiableAt
    _ ≤ (∫⁻ y, ‖fderiv ℝ u (e.symm y)‖ₑ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖ₑ) ^ p := by
        gcongr with y
        rw [e.symm.fderiv]
        apply ContinuousLinearMap.opENorm_comp_le
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖ₑ * ∫⁻ y, ‖fderiv ℝ u (e.symm y)‖ₑ) ^ p := by
        rw [lintegral_mul_const, mul_comm]
        fun_prop
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p : ℝ≥0) * (∫⁻ y, ‖fderiv ℝ u (e.symm y)‖ₑ) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h0p, enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ h0p]
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p : ℝ≥0)
        * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂(volume : Measure (ι → ℝ)).map e.symm) ^ p := by
        congr
        rw [lintegral_map _ e.symm.continuous.measurable]
        fun_prop
  rw [← ENNReal.mul_le_mul_iff_right h3c ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, ← hC,
    ENNReal.coe_mul] at this
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0p, ← mul_assoc, ← ENNReal.coe_rpow_of_ne_zero hc.ne']
  exact this

/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_one`.
It only depends on `E`, `μ` and `p`. -/
irreducible_def eLpNormLESNormFDerivOneConst (p : ℝ) : ℝ≥0 :=
  lintegralPowLePowLIntegralFDerivConst μ p ^ p⁻¹

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n ≥ 2`, equipped
with Haar measure. Then the `Lᵖ` norm of `u`, where `p := n / (n - 1)`, is bounded above by
a constant times the `L¹` norm of the Fréchet derivative of `u`. -/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：eLpNorm_le_eLpNorm_fderiv_one {u : E -> F} (hu : ContDiff Real 1 u) (h2u :
 HasCompactSupport u) {p : Real>=0} (hp : NNReal.HolderConjugate (finrank Real E
) p) : eLpNorm u p μ <= eLpNormLESNormFDerivOneConst μ p * eLpNorm (fderiv Real 
u) 1 μ
参数：hu : ContDiff Real 1 u；h2u : HasCompactSupport u；hp : NNReal.HolderConjugate 
(finrank Real E) p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `NNReal.HolderConjugate.coe`：∀ {p q : NNReal}, p.HolderConjugate q → (↑p)
.HolderConjugate ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `MeasureTheory.eLpNormLESNormFDerivOneConst_def`：∀ {E : Type u_5} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E]  
 [inst_3 : BorelSpace E] [inst_4 : F…
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral`：eLpNorm_nnreal_pow_eq_lin
tegral {f : α -> ε} {p : Real>=0} (hp : p != 0) : eLpNorm f p μ ^ (p : Real) = ∫
⁻ x, ‖f x‖ₑ ^ (p : Real) ∂μ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.pos`：pos : 0 < p
· 使用定理 `NNReal.HolderConjugate.symm`：∀ {p q : NNReal}, p.HolderConjugate q → q.H
olderConjugate p
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv`：lintegral_pow_le_po
w_lintegral_fderiv {u : E -> F} (hu : ContDiff Real 1 u) (h2u : HasCompactSuppor
t u) {p : Real} (hp : Real.HolderConjugat…

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n ≥ 
2`, equipped
with Haar measure. Then the `Lᵖ` norm of `u`, where `p := n / (n - 1)`, is bound
ed above by
a constant times the `L¹` norm of the Fréchet derivative of `u`.
-/
theorem eLpNorm_le_eLpNorm_fderiv_one {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : ℝ≥0} (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * eLpNorm (fderiv ℝ u) 1 μ := by
  have h0p : 0 < (p : ℝ) := hp.coe.symm.pos
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ENNReal.rpow_le_rpow_iff h0p, ENNReal.mul_rpow_of_nonneg _ _ h0p.le,
    ← ENNReal.coe_rpow_of_nonneg _ h0p.le, eLpNormLESNormFDerivOneConst, ← NNReal.rpow_mul,
    eLpNorm_nnreal_pow_eq_lintegral hp.symm.pos.ne',
    inv_mul_cancel₀ h0p.ne', NNReal.rpow_one]
  exact lintegral_pow_le_pow_lintegral_fderiv μ hu h2u hp.coe

/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of_eq_inner`.
It only depends on `E`, `μ` and `p`. -/
/-
**MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst** 是 Mathlib 中的一个定义，位于命名空间 `Me
asureTheory`。
形式化陈述：eLpNormLESNormFDerivOfEqInnerConst (p : Real) : Real>=0
参数：p : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of
_eq_inner`.
It only depends on `E`, `μ` and `p`.
-/
def eLpNormLESNormFDerivOfEqInnerConst (p : ℝ) : ℝ≥0 :=
  let n := finrank ℝ E
  eLpNormLESNormFDerivOneConst μ (NNReal.conjExponent n) * (p * (n - 1) / (n - p)).toNNReal

variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n`, equipped
with Haar measure, let `1 ≤ p < n` and let `p'⁻¹ := p⁻¹ - n⁻¹`.
Then the `Lᵖ'` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a Hilbert space.
-/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：eLpNorm_le_eLpNorm_fderiv_of_eq_inner {u : E -> F'} (hu : ContDiff Real 1 
u) (h2u : HasCompactSupport u) {p p' : Real>=0} (hp : 1 <= p) (hn : 0 < finrank 
Real E) (hp' : (p' : Real)⁻¹ = p⁻¹ - (finrank Real E : Real)⁻¹) : eLpNorm u p' μ
 <= eLpNormLESNormFDerivOfEqInnerConst μ p * eLpNorm (fderiv Real u) p μ
参数：hu : ContDiff Real 1 u；h2u : HasCompactSupport u；hp : 1 <= p；hn : 0 < finrank
 Real E；hp' : (p' : Real)⁻¹ = p⁻¹ - (finrank Real E : Real)⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 235 条，此处仅展示前 30 条）

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n`, 
equipped
with Haar measure, let `1 ≤ p < n` and let `p'⁻¹ := p⁻¹ - n⁻¹`.
Then the `Lᵖ'` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a Hilbert space.
-/
theorem eLpNorm_le_eLpNorm_fderiv_of_eq_inner {u : E → F'}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm u p' μ ≤ eLpNormLESNormFDerivOfEqInnerConst μ p * eLpNorm (fderiv ℝ u) p μ := by
  /- Here we derive the GNS-inequality for `p ≥ 1` from the version with `p = 1`.
  For `p > 1` we apply the previous version to the function `|u|^γ` for a suitably chosen `γ`.
  The proof requires that `x ↦ |x|^p` is smooth in the codomain, so we require that it is a
  Hilbert space. -/
  by_cases hp'0 : p' = 0
  · simp [hp'0]
  set n := finrank ℝ E
  let n' := NNReal.conjExponent n
  have h2p : (p : ℝ) < n := by
    have : 0 < p⁻¹ - (n : ℝ)⁻¹ :=
      NNReal.coe_lt_coe.mpr (pos_iff_ne_zero.mpr (inv_ne_zero hp'0)) |>.trans_eq hp'
    rwa [NNReal.coe_inv, sub_pos,
      inv_lt_inv₀ _ (zero_lt_one.trans_le (NNReal.coe_le_coe.mpr hp))] at this
    exact_mod_cast hn
  have h0n : 2 ≤ n := Nat.succ_le_of_lt <| Nat.one_lt_cast.mp <| hp.trans_lt h2p
  have hn : NNReal.HolderConjugate n n' := .conjExponent (by norm_cast)
  have h1n : 1 ≤ (n : ℝ≥0) := hn.lt.le
  have h2n : (0 : ℝ) < n - 1 := by simp_rw [sub_pos]; exact hn.coe.lt
  have hnp : (0 : ℝ) < n - p := by simp_rw [sub_pos]; exact h2p
  rcases hp.eq_or_lt with rfl | hp
  -- the case `p = 1`
  · convert! eLpNorm_le_eLpNorm_fderiv_one μ hu h2u hn using 2
    · suffices (p' : ℝ) = n' by simpa using this
      rw [← inv_inj, hp']
      simp [field, n', NNReal.conjExponent, *]
    · norm_cast
      simp_rw [n', n, eLpNormLESNormFDerivOfEqInnerConst]
      simp only [n, NNReal.coe_one] at hnp
      field_simp
      simp
  -- the case `p > 1`
  let q := Real.conjExponent p
  have hq : Real.HolderConjugate p q := .conjExponent hp
  have h0p : p ≠ 0 := zero_lt_one.trans hp |>.ne'
  have h1p : (p : ℝ) ≠ 1 := hq.lt.ne'
  have h3p : (p : ℝ) - 1 ≠ 0 := sub_ne_zero_of_ne h1p
  have h2q : 1 / n' - 1 / q = 1 / p' := by
    simp_rw -zeta [one_div, hp']
    rw [← hq.one_sub_inv, ← hn.coe.one_sub_inv, sub_sub_sub_cancel_left]
    simp only [NNReal.coe_natCast, NNReal.coe_inv]
  let γ : ℝ≥0 := .mk (p * (n - 1) / (n - p)) (by positivity)
  have h0γ : (γ : ℝ) = p * (n - 1) / (n - p) := rfl
  have h1γ : 1 < (γ : ℝ) := by
    rwa [h0γ, one_lt_div hnp, mul_sub, mul_one, sub_lt_sub_iff_right, lt_mul_iff_one_lt_left]
    exact hn.coe.pos
  have h2γ : γ * n' = p' := by
    rw [← NNReal.coe_inj, ← inv_inj, hp', NNReal.coe_mul, h0γ, hn.coe.conjugate_eq]
    simp [field]
  have h3γ : (γ - 1) * q = p' := by
    rw [← inv_inj, hp', h0γ, hq.conjugate_eq]
    have : (p : ℝ) * (n - 1) - (n - p) = n * (p - 1) := by ring
    simp [field, this]
  have h4γ : (γ : ℝ) ≠ 0 := (zero_lt_one.trans h1γ).ne'
  by_cases h3u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ = 0
  · rw [eLpNorm_nnreal_eq_lintegral hp'0, h3u, ENNReal.zero_rpow_of_pos] <;> positivity
  have h4u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ ≠ ∞ := by
    refine lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
      ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp'0) ?_ |>.ne
    rw [← eLpNorm_nnreal_eq_eLpNorm' hp'0]
    exact hu.continuous.memLp_of_hasCompactSupport (μ := μ) h2u |>.eLpNorm_lt_top
  have h5u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ 0 :=
    ENNReal.rpow_pos (pos_iff_ne_zero.mpr h3u) h4u |>.ne'
  have h6u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ ∞ := by finiteness
  have h7u := hu.continuous -- for fun_prop
  let v : E → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := hu.norm_rpow h1γ
  have h2v : HasCompactSupport v := h2u.norm.rpow_const h4γ
  set C := eLpNormLESNormFDerivOneConst μ n'
  have :=
  calc (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / (n' : ℝ)) = eLpNorm v n' μ := by
        rw [← h2γ, eLpNorm_nnreal_eq_lintegral hn.symm.pos.ne']
        simp (discharger := positivity) [v, Real.enorm_rpow_of_nonneg, ENNReal.rpow_mul]
    _ ≤ C * eLpNorm (fderiv ℝ v) 1 μ := eLpNorm_le_eLpNorm_fderiv_one μ hv h2v hn
    _ = C * ∫⁻ x, ‖fderiv ℝ v x‖ₑ ∂μ := by rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ C * γ * ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ ∂μ := by
      rw [mul_assoc, ← lintegral_const_mul γ]
      · gcongr
        simp_rw [← mul_assoc]
        exact enorm_fderiv_norm_rpow_le (hu.differentiable one_ne_zero) h1γ
      dsimp [enorm]
      fun_prop
    _ ≤ C * γ * ((∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) *
        (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ))) := by
        gcongr
        convert!
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ (.symm <| .conjExponent <| show 1 < (p : ℝ) from hp)
            ?_ ?_ using 5
        · simp [γ, n, q, ← ENNReal.rpow_mul, ← h3γ]
        · borelize F'
          fun_prop
        · fun_prop
    _ = C * γ * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
      (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) := by ring
  calc
    eLpNorm u p' μ
      = (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / (p' : ℝ)) := eLpNorm_nnreal_eq_lintegral hp'0
    _ ≤ C * γ * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
      rwa [← h2q, ENNReal.rpow_sub _ _ h3u h4u, ENNReal.div_le_iff h5u h6u]
    _ = eLpNormLESNormFDerivOfEqInnerConst μ p * eLpNorm (fderiv ℝ u) (↑p) μ := by
      suffices (C : ℝ) * γ = eLpNormLESNormFDerivOfEqInnerConst μ p by
        rw [eLpNorm_nnreal_eq_lintegral h0p]
        congr
        norm_cast at this ⊢
      simp_rw [eLpNormLESNormFDerivOfEqInnerConst, γ]
      refold_let n n' C
      rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal', mul_eq_mul_left_iff, eq_comm,
        max_eq_left_iff]
      left
      positivity

variable (F) in
/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of_eq`.
It only depends on `E`, `F`, `μ` and `p`. -/
irreducible_def SNormLESNormFDerivOfEqConst [FiniteDimensional ℝ F] (p : ℝ) : ℝ≥0 :=
  let F' := EuclideanSpace ℝ <| Fin <| finrank ℝ F
  let e : F ≃L[ℝ] F' := toEuclidean
  ‖(e.symm : F' →L[ℝ] F)‖₊ * eLpNormLESNormFDerivOfEqInnerConst μ p * ‖(e : F →L[ℝ] F')‖₊

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n`, equipped
with Haar measure, let `1 < p < n` and let `p'⁻¹ := p⁻¹ - n⁻¹`.
Then the `Lᵖ'` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

This is the version where the codomain of `u` is a finite-dimensional normed space.
-/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：eLpNorm_le_eLpNorm_fderiv_of_eq [FiniteDimensional Real F] {u : E -> F} (h
u : ContDiff Real 1 u) (h2u : HasCompactSupport u) {p p' : Real>=0} (hp : 1 <= p
) (hn : 0 < finrank Real E) (hp' : (p' : Real)⁻¹ = p⁻¹ - (finrank Real E : Real)
⁻¹) : eLpNorm u p' μ <= SNormLESNormFDerivOfEqConst F μ p * eLpNorm (fderiv Real
 u) p μ
参数：hu : ContDiff Real 1 u；h2u : HasCompactSupport u；hp : 1 <= p；hn : 0 < finrank
 Real E；hp' : (p' : Real)⁻¹ = p⁻¹ - (finrank Real E : Real)⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
· 使用定理 `HasCompactSupport.comp_left`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u
_5} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {g : β → γ
} {f : α → β}, Ha…
· 使用定理 `ContinuousLinearEquiv.map_zero`：map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M
₁) = 0
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`：eLpNorm_le_eLpNorm_
fderiv_of_eq_inner {u : E -> F'} (hu : ContDiff Real 1 u) (h2u : HasCompactSuppo
rt u) {p p' : Real>=0} (hp : 1 <= p) (hn …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_comp`：fderiv_comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) 
(hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fd
e…
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `ContDiff.differentiable`：ContDiff.differentiable (h : ContDiff 𝕜 n f) (h
n : n != 0) : Differentiable 𝕜 f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {F : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul`：eLpNorm_le_nn
real_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0} (h : fora
llᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.le_opNNNorm`：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E)
 : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n`, 
equipped
with Haar measure, let `1 < p < n` and let `p'⁻¹ := p⁻¹ - n⁻¹`.
Then the `Lᵖ'` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

This is the version where the codomain of `u` is a finite-dimensional normed spa
ce.
-/
theorem eLpNorm_le_eLpNorm_fderiv_of_eq [FiniteDimensional ℝ F]
    {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm u p' μ ≤ SNormLESNormFDerivOfEqConst F μ p * eLpNorm (fderiv ℝ u) p μ := by
  /- Here we reduce the GNS-inequality with a Hilbert space as codomain to the case with a
  finite-dimensional normed space as codomain, by transferring the result along the equivalence
  `F ≃ ℝᵐ`. -/
  let F' := EuclideanSpace ℝ <| Fin <| finrank ℝ F
  let e : F ≃L[ℝ] F' := toEuclidean
  let C₁ : ℝ≥0 := ‖(e.symm : F' →L[ℝ] F)‖₊
  let C : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst μ p
  let C₂ : ℝ≥0 := ‖(e : F →L[ℝ] F')‖₊
  let v := e ∘ u
  have hv : ContDiff ℝ 1 v := e.contDiff.comp hu
  have h2v : HasCompactSupport v := h2u.comp_left e.map_zero
  have := eLpNorm_le_eLpNorm_fderiv_of_eq_inner μ hv h2v hp hn hp'
  have h4v : ∀ x, ‖fderiv ℝ v x‖ ≤ C₂ * ‖fderiv ℝ u x‖ := fun x ↦ calc
    ‖fderiv ℝ v x‖
      = ‖(fderiv ℝ e (u x)).comp (fderiv ℝ u x)‖ := by
      rw [fderiv_comp x e.differentiableAt (hu.differentiable one_ne_zero x)]
    _ ≤ ‖fderiv ℝ e (u x)‖ * ‖fderiv ℝ u x‖ :=
      (fderiv ℝ e (u x)).opNorm_comp_le (fderiv ℝ u x)
    _ = C₂ * ‖fderiv ℝ u x‖ := by simp_rw [e.fderiv, C₂, coe_nnnorm]
  calc eLpNorm u p' μ
      = eLpNorm (e.symm ∘ v) p' μ := by simp_rw [v, Function.comp_def, e.symm_apply_apply]
    _ ≤ C₁ • eLpNorm v p' μ := by
      apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      exact Eventually.of_forall (fun x ↦ (e.symm : F' →L[ℝ] F).le_opNNNorm _)
    _ = C₁ * eLpNorm v p' μ := rfl
    _ ≤ C₁ * C * eLpNorm (fderiv ℝ v) p μ := by rw [mul_assoc]; gcongr
    _ ≤ C₁ * C * (C₂ * eLpNorm (fderiv ℝ u) p μ) := by
      gcongr; exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall h4v) p
    _ = SNormLESNormFDerivOfEqConst F μ p * eLpNorm (fderiv ℝ u) p μ := by
      simp_rw [C₂, C₁, C, e, SNormLESNormFDerivOfEqConst]
      push_cast
      simp_rw [mul_assoc]


variable (F) in
/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of_le`.
It only depends on `F`, `μ`, `s`, `p` and `q`. -/
irreducible_def eLpNormLESNormFDerivOfLeConst [FiniteDimensional ℝ F] (s : Set E) (p q : ℝ≥0) :
    ℝ≥0 :=
  let p' : ℝ≥0 := (p⁻¹ - (finrank ℝ E : ℝ≥0)⁻¹)⁻¹
  (μ s).toNNReal ^ (1 / q - 1 / p' : ℝ) * SNormLESNormFDerivOfEqConst F μ p


/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
function `u` supported in a bounded set `s` in a normed space `E` of finite dimension
`n`, equipped with Haar measure, and let `1 < p < n` and `0 < q ≤ (p⁻¹ - (finrank ℝ E : ℝ)⁻¹)⁻¹`.
Then the `L^q` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a finite-dimensional normed space.
-/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：eLpNorm_le_eLpNorm_fderiv_of_le [FiniteDimensional Real F] {u : E -> F} {s
 : Set E} (hu : ContDiff Real 1 u) (h2u : u.support subseteq s) {p q : Real>=0} 
(hp : 1 <= p) (h2p : p < finrank Real E) (hpq : p⁻¹ - (finrank Real E : Real)⁻¹ 
<= (q : Real)⁻¹) (hs : Bornology.IsBounded s) : eLpNorm u q μ <= eLpNormLESNormF
DerivOfLeConst F μ s p q * eLpNorm (fderiv Real u) p μ
参数：hu : ContDiff Real 1 u；h2u : u.support subseteq s；hp : 1 <= p；h2p : p < finra
nk Real E；hpq : p⁻¹ - (finrank Real E : Real)⁻¹ <= (q : Real)⁻¹；hs : Bornology.I
sBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `MeasureTheory.eLpNormLESNormFDerivOfLeConst.congr_simp`：∀ (F : Type u_6)
 [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] {E : Type u_7} [inst_2
 : NormedAddCommGroup E]   [inst_3 : NormedS…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
function `u` supported in a bounded set `s` in a normed space `E` of finite dime
nsion
`n`, equipped with Haar measure, and let `1 < p < n` and `0 < q ≤ (p⁻¹ - (finran
k ℝ E : ℝ)⁻¹)⁻¹`.
Then the `L^q` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a finite-dimensional normed space.
-/
theorem eLpNorm_le_eLpNorm_fderiv_of_le [FiniteDimensional ℝ F]
    {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u) (h2u : u.support ⊆ s)
    {p q : ℝ≥0} (hp : 1 ≤ p) (h2p : p < finrank ℝ E)
    (hpq : p⁻¹ - (finrank ℝ E : ℝ)⁻¹ ≤ (q : ℝ)⁻¹)
    (hs : Bornology.IsBounded s) :
    eLpNorm u q μ ≤ eLpNormLESNormFDerivOfLeConst F μ s p q * eLpNorm (fderiv ℝ u) p μ := by
  by_cases hq0 : q = 0
  · simp [hq0]
  let p' : ℝ≥0 := (p⁻¹ - (finrank ℝ E : ℝ≥0)⁻¹)⁻¹
  have hp' : p'⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹ := by
    rw [inv_inv, NNReal.coe_sub]
    · simp
    · gcongr
  have : (q : ℝ≥0∞) ≤ p' := by
    have H : (p' : ℝ)⁻¹ ≤ (↑q)⁻¹ := trans hp' hpq
    norm_cast at H ⊢
    rwa [inv_le_inv₀] at H
    · have : 0 < p⁻¹ - (finrank ℝ E : ℝ≥0)⁻¹ := by
        simp only [tsub_pos_iff_lt]
        gcongr
      positivity
    · positivity
  set t := (μ s).toNNReal ^ (1 / q - 1 / p' : ℝ)
  let C := SNormLESNormFDerivOfEqConst F μ p
  calc eLpNorm u q μ
      = eLpNorm u q (μ.restrict s) := by rw [eLpNorm_restrict_eq_of_support_subset h2u]
    _ ≤ eLpNorm u p' (μ.restrict s) * t := by
        convert! eLpNorm_le_eLpNorm_mul_rpow_measure_univ this hu.continuous.aestronglyMeasurable
        rw [ENNReal.coe_rpow_of_nonneg]
        · simp [ENNReal.coe_toNNReal hs.measure_lt_top.ne]
        · rw [one_div, one_div]
          norm_cast
          rw [hp']
          simpa using hpq
    _ = eLpNorm u p' μ * t := by rw [eLpNorm_restrict_eq_of_support_subset h2u]
    _ ≤ (C * eLpNorm (fderiv ℝ u) p μ) * t := by
        have h2u' : HasCompactSupport u := by
          apply HasCompactSupport.of_support_subset_isCompact hs.isCompact_closure
          exact h2u.trans subset_closure
        rel [eLpNorm_le_eLpNorm_fderiv_of_eq μ hu h2u' hp (mod_cast h2p.pos) hp']
    _ = eLpNormLESNormFDerivOfLeConst F μ s p q * eLpNorm (fderiv ℝ u) p μ := by
      simp_rw [eLpNormLESNormFDerivOfLeConst, ENNReal.coe_mul]; ring

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
function `u` supported in a bounded set `s` in a normed space `E` of finite dimension
`n`, equipped with Haar measure, and let `1 < p < n`.
Then the `Lᵖ` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a finite-dimensional normed space.
-/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：eLpNorm_le_eLpNorm_fderiv [FiniteDimensional Real F] {u : E -> F} {s : Set
 E} (hu : ContDiff Real 1 u) (h2u : u.support subseteq s) {p : Real>=0} (hp : 1 
<= p) (h2p : p < finrank Real E) (hs : Bornology.IsBounded s) : eLpNorm u p μ <=
 eLpNormLESNormFDerivOfLeConst F μ s p p * eLpNorm (fderiv Real u) p μ
参数：hu : ContDiff Real 1 u；h2u : u.support subseteq s；hp : 1 <= p；h2p : p < finra
nk Real E；hs : Bornology.IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`：eLpNorm_le_eLpNorm_fderiv
_of_le [FiniteDimensional Real F] {u : E -> F} {s : Set E} (hu : ContDiff Real 1
 u) (h2u : u.support subseteq s) {p…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `inv_nonneg_of_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_
1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a → 0 ≤ a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)

--- 原说明 ---
The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously diffe
rentiable
function `u` supported in a bounded set `s` in a normed space `E` of finite dime
nsion
`n`, equipped with Haar measure, and let `1 < p < n`.
Then the `Lᵖ` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a finite-dimensional normed space.
-/
theorem eLpNorm_le_eLpNorm_fderiv [FiniteDimensional ℝ F]
    {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u) (h2u : u.support ⊆ s)
    {p : ℝ≥0} (hp : 1 ≤ p) (h2p : p < finrank ℝ E) (hs : Bornology.IsBounded s) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOfLeConst F μ s p p * eLpNorm (fderiv ℝ u) p μ := by
  refine eLpNorm_le_eLpNorm_fderiv_of_le μ hu h2u hp h2p ?_ hs
  norm_cast
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  positivity

end MeasureTheory

