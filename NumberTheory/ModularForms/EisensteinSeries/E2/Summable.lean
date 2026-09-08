/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Summability of E2

We collect here lemmas about the summability of the Eisenstein series `E2` that will be used to
prove how it transforms under the slash action.

## Main Results

The key results concern the difference between two different orders of summation for the
telescoping series `∑_{m,n} (1/(mz + n) - 1/(mz + n + 1))`:

1. **`tsum_symmetricIco_tsum_sub_eq`**: Summing first over `n` (in symmetric intervals), then `m`:
   `∑'[symmetricIco] n : ℤ, ∑' m : ℤ, (1/(mz+n) - 1/(mz+n+1)) = -2πi/z`

2. **`tsum_tsum_symmetricIco_sub_eq`**: Summing first over `m`, then `n` (in symmetric intervals):
   `∑' m : ℤ, ∑'[symmetricIco] n : ℤ, (1/(mz+n) - 1/(mz+n+1)) = 0`

The difference `-2πi/z` between these two orderings is precisely the correction term
`D2` that appears in the transformation formula for `G2` under the action of `S`.

## Proof Strategy

1. For fixed `m ≠ 0`, the inner sum over `n` telescopes to zero (each term cancels with its
   neighbor), establishing the first identity.

2. For fixed `n`, the inner sum over `m` can be computed using the cotangent series expansion.
   As `n → ±∞` in symmetric intervals, these sums contribute `-2πi/z`.

-/

open UpperHalfPlane hiding I σ

open Filter Complex Finset SummationFilter

open scoped Interval Real Topology Nat ArithmeticFunction.sigma

@[expose] public noncomputable section

namespace EisensteinSeries

variable (z : ℍ)

local notation "𝕢" z:100 => cexp (2 * π * I * z)

/-
**EisensteinSeries.G2_partial_sum_eq** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma G2_partial_sum_eq (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    2 * riemannZeta 2 + ∑ m ∈ range N, -8 * π ^ 2 *
      ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', smul_add,
    nsmul_eq_mul, Nat.cast_zero, e2Summand_zero_eq_two_riemannZeta_two]
  ring_nf
  simp only [e2Summand, eisSummand, add_comm, Nat.cast_add, Nat.cast_one, Fin.isValue,
    Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_comm, mul_sum]
  congr with a
  have H2 := qExpansion_identity_pnat (k := 1) (by grind)
    ⟨(a + 1) * z, by simpa [show 0 < ((a + 1) : ℝ) by positivity] using z.2⟩
  simp only [add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one] at H2
  simp_rw [zpow_ofNat, H2, ← tsum_mul_left, ← tsum_neg, ← exp_nsmul]
  refine tsum_congr fun b ↦ ?_
  ring_nf
  grind [I_sq, exp_add]
/-
**EisensteinSeries.aux_G2_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_G2_tendsto : Tendsto
    (fun N ↦ ∑ m ∈ range N, -8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ))) := by
  have : -8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) =
      ∑' m : ℕ, (-8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d ↦ ∑' c : ℕ+, c ^ 1 * 𝕢 z ^ (d * c : ℕ))] at this
    simp [← tsum_mul_left, ← this]
  rw [this]
  refine (Summable.mul_left _ ?_).hasSum.comp tendsto_finset_range
  rw [← summable_pnat_iff_summable_succ (f := fun b ↦ ∑' c : ℕ+, c * 𝕢 z ^ (b * c : ℕ))]
  apply (summable_prod_mul_pow 1 (norm_exp_two_pi_I_lt_one z)).prod.congr
  simp [← exp_nsmul]
/-
**EisensteinSeries.hasSum_e2Summand_symmetricIcc** 是 Mathlib 中的一个引理，位于命名空间 `Eise
nsteinSeries`。
形式化陈述：hasSum_e2Summand_symmetricIcc : HasSum (e2Summand · z) (2 * riemannZeta 2 
- 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)) (symmetricIcc Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `SummationFilter.symmetricIcc_eq_map_Icc_nat`：symmetricIcc_eq_map_Icc_nat
 : (symmetricIcc Int).filter = atTop.map (fun N : Nat => Icc (-(N : Int)) N)
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.G2_partial_sum_eq`：∀ (z : UpperHalfPlane) (N : ℕ),   ∑ m ∈ Fi
nset.Icc (-↑N) ↑N, EisensteinSeries.e2Summand m z =     2 * riemannZeta 2 +     
  ∑ m ∈ Finset.ran…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.aux_G2_tendsto`：∀ (z : UpperHalfPlane),   Filter.Tendsto     
(fun N =>       ∑ m ∈ Finset.range N,         -8 * ↑Real.pi ^ 2 * ∑' (n : ℕ+), ↑
↑n * Complex.ex…
-/
lemma hasSum_e2Summand_symmetricIcc : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIcc ℤ) := by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using! (aux_G2_tendsto z).const_add _
/-
**EisensteinSeries.summable_e2Summand_symmetricIcc** 是 Mathlib 中的一个引理，位于命名空间 `Ei
sensteinSeries`。
形式化陈述：summable_e2Summand_symmetricIcc : Summable (e2Summand · z) (symmetricIcc I
nt)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.hasSum_e2Summand_symmetricIcc`：hasSum_e2Summand_symmetr
icIcc : HasSum (e2Summand · z) (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1
 n * 𝕢 z ^ (n : Nat)) (symmetricIcc …
-/
lemma summable_e2Summand_symmetricIcc : Summable (e2Summand · z) (symmetricIcc ℤ) :=
  (hasSum_e2Summand_symmetricIcc z).summable
/-
**EisensteinSeries.G2_eq_tsum_cexp** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：G2_eq_tsum_cexp : G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 
n * 𝕢 z ^ (n : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotSymmetricIcc`：∀ (G : Type u_1) [inst : Neg G] [
inst_1 : Preorder G] [inst_2 : LocallyFiniteOrder G] [Filter.atTop.NeBot],   (Su
mmationFilter.symmetricIcc …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EisensteinSeries.hasSum_e2Summand_symmetricIcc`：hasSum_e2Summand_symmetr
icIcc : HasSum (e2Summand · z) (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1
 n * 𝕢 z ^ (n : Nat)) (symmetricIcc …
-/
lemma G2_eq_tsum_cexp : G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) :=
  (hasSum_e2Summand_symmetricIcc z).tsum_eq

/-- The q-expansion of the normalised weight-2 Eisenstein series:
`E₂(z) = 1 - 24 ∑_{n≥1} σ₁(n) qⁿ`. -/
/-
**EisensteinSeries.E2_eq_tsum_cexp** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：E2_eq_tsum_cexp : E2 z = 1 - 24 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `riemannZeta_two`：riemannZeta_two : riemannZeta 2 = (π : Complex) ^ 2 / 6
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用引理 `EisensteinSeries.G2_eq_tsum_cexp`：G2_eq_tsum_cexp : G2 z = 2 * riemannZe
ta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
The q-expansion of the normalised weight-2 Eisenstein series:
`E₂(z) = 1 - 24 ∑_{n≥1} σ₁(n) qⁿ`.
-/
lemma E2_eq_tsum_cexp : E2 z = 1 - 24 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) := by
  simp [E2, G2_eq_tsum_cexp, riemannZeta_two]
  field

/-- The `q`-expansion of `E2` as a `HasSum` over `ℕ`. -/
/-
**EisensteinSeries.hasSum_qExpansion_E2** 是 Mathlib 中的一个定理，位于命名空间 `EisensteinSer
ies`。
形式化陈述：hasSum_qExpansion_E2 : HasSum (fun m : Nat => (if m = 0 then 1 else -24 * 
σ 1 m : Complex) • 𝕢 z ^ m) (E2 z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `EisensteinSeries.summable_sigma_mul_cexp_pow`：EisensteinSeries.summable_
sigma_mul_cexp_pow {k : Nat} (hk : 1 <= k) (z : ℍ) : Summable fun n : Nat => (σ 
(k - 1) n : Complex) * cexp (2 * π…
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasSum_nat_add_iff'`：∀ {G : Type u_2} [inst : AddCommGroup G] {g : G} [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G}   (k : ℕ), Has
Sum (fun …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `EisensteinSeries.E2_eq_tsum_cexp`：E2_eq_tsum_cexp : E2 z = 1 - 24 * ∑' n
 : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)
· 使用定理 `tsum_pnat_eq_tsum_succ`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {f : ℕ → M},   ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1)
· 使用定理 `tsum_mul_left`：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] 
x, f x
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The `q`-expansion of `E2` as a `HasSum` over `ℕ`.
-/
theorem hasSum_qExpansion_E2 :
    HasSum (fun m : ℕ ↦ (if m = 0 then 1 else -24 * σ 1 m : ℂ) • 𝕢 z ^ m) (E2 z) := by
  have hS : Summable fun n : ℕ ↦ σ 1 (n + 1) * 𝕢 z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (k := 2) (one_le_two) z)
  rw [← hasSum_nat_add_iff' 1]
  convert! (hS.mul_left (-24)).hasSum using 1
  · ext : 1
    simp [mul_assoc]
  · rw [E2_eq_tsum_cexp, tsum_pnat_eq_tsum_succ (f := fun n ↦ σ 1 n * 𝕢 z ^ n), tsum_mul_left]
    simp

/-- `E2` is bounded at `i∞`. -/
/-
**EisensteinSeries.isBoundedAtImInfty_E2** 是 Mathlib 中的一个定理，位于命名空间 `EisensteinSe
ries`。
形式化陈述：isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion`：isBoundedAtImInf
ty_of_hasSum_qExpansion {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h) (hf
 : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `EisensteinSeries.hasSum_qExpansion_E2`：hasSum_qExpansion_E2 : HasSum (fu
n m : Nat => (if m = 0 then 1 else -24 * σ 1 m : Complex) • 𝕢 z ^ m) (E2 z)

--- 原说明 ---
`E2` is bounded at `i∞`.
-/
theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos fun τ ↦ by
    simpa only [Function.Periodic.qParam, ofReal_one, div_one] using hasSum_qExpansion_E2 (z := τ)
/-
**EisensteinSeries.tendsto_e2Summand_atTop_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 `
EisensteinSeries`。
形式化陈述：tendsto_e2Summand_atTop_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tendsto_zero_of_even_summable_symmetricIcc`：∀ {F : Type u_2} [i
nst : NormedAddCommGroup F] [NormSMulClass ℤ F] {f : ℤ → F},   Summable f (Summa
tionFilter.symmetricIcc ℤ) → Function.Eve…
· 使用定理 `RCLike.instNormSMulClassInt`：∀ {K : Type u_1} [inst : RCLike K], NormSMu
lClass ℤ K
· 使用引理 `EisensteinSeries.summable_e2Summand_symmetricIcc`：summable_e2Summand_sym
metricIcc : Summable (e2Summand · z) (symmetricIcc Int)
· 使用引理 `EisensteinSeries.e2Summand_even`：e2Summand_even (z : ℍ) : (e2Summand · z
).Even
-/
lemma tendsto_e2Summand_atTop_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0) :=
  (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)
/-
**EisensteinSeries.hasSum_e2Summand_symmetricIco** 是 Mathlib 中的一个引理，位于命名空间 `Eise
nsteinSeries`。
形式化陈述：hasSum_e2Summand_symmetricIco : HasSum (e2Summand · z) (2 * riemannZeta 2 
- 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)) (symmetricIco Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.hasSum_symmetricIco_of_hasSum_symmetricIcc`：∀ {α : Type u_1} {f :
 ℤ → α} [inst : AddCommGroup α] [inst_1 : TopologicalSpace α] [ContinuousAdd α] 
{a : α},   HasSum f a (SummationFilter.…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.hasSum_e2Summand_symmetricIcc`：hasSum_e2Summand_symmetr
icIcc : HasSum (e2Summand · z) (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1
 n * 𝕢 z ^ (n : Nat)) (symmetricIcc …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用引理 `EisensteinSeries.tendsto_e2Summand_atTop_nhds_zero`：tendsto_e2Summand_at
Top_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0)
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
-/
lemma hasSum_e2Summand_symmetricIco : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIco ℤ) := by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop
/-
**EisensteinSeries.summable_e2Summand_symmetricIco** 是 Mathlib 中的一个引理，位于命名空间 `Ei
sensteinSeries`。
形式化陈述：summable_e2Summand_symmetricIco : Summable (e2Summand · z) (symmetricIco I
nt)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.hasSum_e2Summand_symmetricIco`：hasSum_e2Summand_symmetr
icIco : HasSum (e2Summand · z) (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1
 n * 𝕢 z ^ (n : Nat)) (symmetricIco …
-/
lemma summable_e2Summand_symmetricIco : Summable (e2Summand · z) (symmetricIco ℤ) :=
  (hasSum_e2Summand_symmetricIco z).summable
/-
**EisensteinSeries.G2_eq_tsum_symmetricIco** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstein
Series`。
形式化陈述：G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco Int] m, e2Summand m z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EisensteinSeries.G2.eq_1`：∀ (z : UpperHalfPlane),   EisensteinSeries.G2 
z = ∑'[SummationFilter.symmetricIcc ℤ] (m : ℤ), EisensteinSeries.e2Summand m z
· 使用定理 `SummationFilter.tsum_symmetricIcc_eq_tsum_symmetricIco`：∀ {α : Type u_1}
 {f : ℤ → α} [inst : AddCommGroup α] [inst_1 : TopologicalSpace α] [ContinuousAd
d α] [T2Space α],   Summable f (SummationFil…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用引理 `EisensteinSeries.summable_e2Summand_symmetricIcc`：summable_e2Summand_sym
metricIcc : Summable (e2Summand · z) (symmetricIcc Int)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用引理 `EisensteinSeries.tendsto_e2Summand_atTop_nhds_zero`：tendsto_e2Summand_at
Top_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0)
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
-/
lemma G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco ℤ] m, e2Summand m z := by
  rw [G2, tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

section Auxiliary

open ModularGroup

variable (z : ℍ)

/-
**EisensteinSeries.one_div_linear_sub_one_div_linear_eq** 是 Mathlib 中的一个引理，位于命名空
间 `EisensteinSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma one_div_linear_sub_one_div_linear_eq (a b m : ℤ) (hm : m ≠ 0 ∨ (a ≠ 0 ∧ b ≠ 0)) :
    1 / ((m : ℂ) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · grind [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
  · simpa using linear_ne_zero z (cd := ![m, a]) (by aesop)
  · simpa using linear_ne_zero z (cd := ![m, b]) (by aesop)
/-
**EisensteinSeries.summable_left_one_div_linear_sub_one_div_linear** 是 Mathlib 中
的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：summable_left_one_div_linear_sub_one_div_linear (a b : Int) : Summable fun
 m : Int => 1 / (m * (z : Complex) + a) - 1 / (m * z + b)
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `EisensteinSeries.summable_linear_left_mul_linear_left`：summable_linear_l
eft_mul_linear_left {z : Complex} (hz : z != 0) (c₁ c₂ : Int) : Summable fun n :
 Int => ((n * z + c₁) * (n * z + c₂))⁻¹
· 使用定理 `UpperHalfPlane.ne_zero`：ne_zero (z : ℍ) : (z : Complex) != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.summable_compl_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCo
mmGroup α] [inst_1 : TopologicalSpace α] [IsTopologicalAddGroup α]   {f : β → α}
 (s : Finset β)…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
-/
lemma summable_left_one_div_linear_sub_one_div_linear (a b : ℤ) :
    Summable fun m : ℤ ↦ 1 / (m * (z : ℂ) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left (b - a : ℂ) (summable_linear_left_mul_linear_left (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr (fun m ↦ ?_)
  grind [one_div_linear_sub_one_div_linear_eq z a b m (by grind)]
/-
**EisensteinSeries.summable_right_one_div_linear_sub_one_div_linear_succ** 是 Mat
hlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：summable_right_one_div_linear_sub_one_div_linear_succ (m : Int) : Summable
 fun b : Int => 1 / (m * (z : Complex) + b) - 1 / (m * z + b + 1)
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.summable_linear_right_add_one_mul_linear_right`：summabl
e_linear_right_add_one_mul_linear_right (z : Complex) (c₁ c₂ : Int) : Summable f
un n : Int => ((c₁ * z + n + 1) * (c₂ * z + n))⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.summable_compl_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCo
mmGroup α] [inst_1 : TopologicalSpace α] [IsTopologicalAddGroup α]   {f : β → α}
 (s : Finset β)…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.one_div_linear_sub_one_div_linear_eq`：∀ (z : UpperHalfPlane) 
(a b m : ℤ),   m ≠ 0 ∨ a ≠ 0 ∧ b ≠ 0 → 1 / (↑m * ↑z + ↑a) - 1 / (↑m * ↑z + ↑b) =
 (↑b - ↑a) * (1 / ((↑m * ↑z + ↑a) * (…
-/
lemma summable_right_one_div_linear_sub_one_div_linear_succ (m : ℤ) :
    Summable fun b : ℤ ↦ 1 / (m * (z : ℂ) + b) - 1 / (m * z + b + 1) := by
  have := summable_linear_right_add_one_mul_linear_right z m m
  rw [← Finset.summable_compl_iff (s := {0, -1})] at *
  apply this.congr (fun b ↦ ?_)
  simpa [add_assoc, mul_comm] using
    (one_div_linear_sub_one_div_linear_eq z b (b + 1) m (by grind)).symm

/- Acting by `S` (which sends `z` to `-z ⁻¹`) swaps the sums and pulls out a factor of
`(z ^ 2)⁻¹`. -/
/-
**EisensteinSeries.aux_sum_Ico_S_identity** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinS
eries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Acting by `S` (which sends `z` to `-z ⁻¹`) swaps the sums and pulls out a factor
 of
`(z ^ 2)⁻¹`.
-/
private lemma aux_sum_Ico_S_identity (N : ℕ) :
    ((z : ℂ) ^ 2)⁻¹ * (∑ x ∈ Ico (-N : ℤ) N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : ℤ), ∑ x ∈ Ico (-N : ℤ) N, (((n : ℂ) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg, mul_sum, pow_two, ← zpow_two]
  rw [Summable.tsum_finsetSum (fun i hi ↦ linear_left_summable (ne_zero z) i le_rfl)]
  apply sum_congr rfl fun n hn ↦ ?_
  rw [← tsum_mul_left, ← tsum_comp_neg]
  apply tsum_congr (by grind [zpow_two, ne_zero z])
/-
**EisensteinSeries.tendsto_double_sum_S_act** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstei
nSeries`。
形式化陈述：tendsto_double_sum_S_act : Tendsto (fun N : Nat => (∑' (n : Int), ∑ m in I
co (-N : Int) N, (1 / ((n : Complex) * z + m) ^ 2))) atTop (𝓝 ((z.1 ^ 2)⁻¹ * G2 
(S • z)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EisensteinSeries.G2_eq_tsum_symmetricIco`：G2_eq_tsum_symmetricIco : G2 z
 = ∑'[symmetricIco Int] m, e2Summand m z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_mul_left`：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] 
x, f x
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用引理 `EisensteinSeries.summable_e2Summand_symmetricIco`：summable_e2Summand_sym
metricIco : Summable (e2Summand · z) (symmetricIco Int)
· 使用定理 `UpperHalfPlane.im_inv_neg_coe_pos`：im_inv_neg_coe_pos (z : ℍ) : 0 < (-z 
: Complex)⁻¹.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.modular_S_smul`：modular_S_smul (z : ℍ) : ModularGroup.S •
 z = mk (-z : Complex)⁻¹ z.im_inv_neg_coe_pos
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.aux_sum_Ico_S_identity`：∀ (z : UpperHalfPlane) (N : ℕ),   (↑z
 ^ 2)⁻¹ * ∑ x ∈ Finset.Ico (-↑N) ↑N, ∑' (n : ℤ), ((↑x * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹ =  
   ∑' (n : ℤ), ∑ x ∈ Fi…
-/
lemma tendsto_double_sum_S_act :
    Tendsto (fun N : ℕ ↦ (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) atTop
    (𝓝 ((z.1 ^ 2)⁻¹ * G2 (S • z))) := by
  rw [G2_eq_tsum_symmetricIco, ← tsum_mul_left]
  have := ((summable_e2Summand_symmetricIco (S • z)).mul_left (z.1 ^ 2)⁻¹).hasSum
  simp only [HasSum, symmetricIco, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr (fun N ↦ ?_)
  simpa [e2Summand, eisSummand, ← mul_sum] using! aux_sum_Ico_S_identity z N
/-
**EisensteinSeries.tsum_symmetricIco_tsum_eq_S_act** 是 Mathlib 中的一个引理，位于命名空间 `Ei
sensteinSeries`。
形式化陈述：tsum_symmetricIco_tsum_eq_S_act : ∑'[symmetricIco Int] n : Int, ∑' m : Int
, 1 / ((m : Complex) * z + n) ^ 2 = ((z : Complex) ^ 2)⁻¹ * G2 (S • z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotSymmetricIco`：∀ (G : Type u_1) [inst : Neg G] [
inst_1 : Preorder G] [inst_2 : LocallyFiniteOrder G] [Filter.atTop.NeBot],   (Su
mmationFilter.symmetricIco …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SummationFilter.hasSum_symmetricIco_int_iff`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : ℤ → α} {a : α},   HasSum f a (
SummationFilter.symmetricIco ℤ) ↔…
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Summable.tsum_finsetSum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β}
 [T2Space α] …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `EisensteinSeries.linear_left_summable`：linear_left_summable {z : Complex
} (hz : z != 0) (d : Int) {k : Int} (hk : 2 <= k) : Summable fun c : Int => ((c 
* z + d) ^ k)⁻¹
· 使用定理 `UpperHalfPlane.ne_zero`：ne_zero (z : ℍ) : (z : Complex) != 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `EisensteinSeries.tendsto_double_sum_S_act`：tendsto_double_sum_S_act : Te
ndsto (fun N : Nat => (∑' (n : Int), ∑ m in Ico (-N : Int) N, (1 / ((n : Complex
) * z + m) ^ 2))) atTop (𝓝 ((z.…
-/
lemma tsum_symmetricIco_tsum_eq_S_act :
    ∑'[symmetricIco ℤ] n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * z + n) ^ 2 =
    ((z : ℂ) ^ 2)⁻¹ * G2 (S • z) := by
  apply HasSum.tsum_eq
  rw [hasSum_symmetricIco_int_iff]
  apply (tendsto_double_sum_S_act z).congr (fun x ↦ ?_)
  rw [Summable.tsum_finsetSum]
  exact fun i hi ↦ by simpa using! linear_left_summable (ne_zero z) i le_rfl
/-
**EisensteinSeries.telescope_aux** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma telescope_aux (z : ℂ) (m : ℤ) (b : ℕ) :
    ∑ n ∈ Ico (-b : ℤ) b, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    1 / (m * z - b) - 1 / (m * z + b) := by
  convert! sum_Ico_int_sub b (fun n ↦ 1 / ((m : ℂ) * z + n)) using 2 <;>
  simp [add_assoc, sub_eq_add_neg]
/-
**EisensteinSeries.tsum_symmetricIco_linear_sub_linear_add_one_eq_zero** 是 Mathl
ib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：tsum_symmetricIco_linear_sub_linear_add_one_eq_zero (m : Int) : ∑'[symmetr
icIco Int] n : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) = 0
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotSymmetricIco`：∀ (G : Type u_1) [inst : Neg G] [
inst_1 : Preorder G] [inst_2 : LocallyFiniteOrder G] [Filter.atTop.NeBot],   (Su
mmationFilter.symmetricIco …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.telescope_aux`：∀ (z : ℂ) (m : ℤ) (b : ℕ),   ∑ n ∈ Finset.Ico 
(-↑b) ↑b, (1 / (↑m * z + ↑n) - 1 / (↑m * z + ↑n + 1)) = 1 / (↑m * z - ↑b) - 1 / 
(↑m * z + ↑b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `EisensteinSeries.tendsto_zero_inv_linear_sub`：tendsto_zero_inv_linear_su
b (z : Complex) (b : Int) : Tendsto (fun d : Nat => 1 / ((b : Complex) * z - d))
 atTop (𝓝 0)
· 使用引理 `EisensteinSeries.tendsto_zero_inv_linear`：tendsto_zero_inv_linear (z : C
omplex) (b : Int) : Tendsto (fun d : Nat => 1 / ((b : Complex) * z + d)) atTop (
𝓝 0)
-/
lemma tsum_symmetricIco_linear_sub_linear_add_one_eq_zero (m : ℤ) :
    ∑'[symmetricIco ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  apply HasSum.tsum_eq
  simp_rw [hasSum_symmetricIco_int_iff, telescope_aux z m]
  simpa using (tendsto_zero_inv_linear_sub z m).sub (tendsto_zero_inv_linear z m)

/- We split the sum over `ℤ` into a sum over `ℕ+` but of four terms.-/
/-
**EisensteinSeries.aux_tsum_identity_1** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeri
es`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We split the sum over `ℤ` into a sum over `ℕ+` but of four terms.
-/
private lemma aux_tsum_identity_1 (d : ℕ+) :
    ∑' (m : ℤ), (1 / ((m : ℂ) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - 1 / (m * z + d) -1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : ℂ)), tsum_int_eq_zero_add_tsum_pnat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [← Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_left_one_div_linear_sub_one_div_linear z (-d) d)).1)).congr
      grind [Int.cast_natCast]
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_left_one_div_linear_sub_one_div_linear z (-d) d)).2)).congr
      grind [Int.cast_neg, Int.cast_natCast, neg_mul, one_div]
  · simpa using! summable_left_one_div_linear_sub_one_div_linear z (-d) d

/- The sum of four terms can now be combined into a sum where `z` has changed for `-1 / z`.-/
/-
**EisensteinSeries.aux_tsum_identity_2** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeri
es`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of four terms can now be combined into a sum where `z` has changed for `
-1 / z`.
-/
private lemma aux_tsum_identity_2 (d : ℕ+) :
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - (1 / (m * z + d)) -
    1 / (-m * z + d)) = 2 / z * ∑' m : ℕ+, (1 / (-(d : ℂ) / z - m) + 1 / (-d / z + m)) := by
  rw [← Summable.tsum_mul_left]
  · apply tsum_congr (by grind [sub_eq_add_neg, ← div_neg, ne_zero z])
  · have := summable_cotTerm (by simpa using z.int_div_mem_integerComplement (n := -d) (by aesop))
    simp only [cotTerm, one_div] at *
    simp only [← Nat.cast_add_one] at this
    rw [summable_nat_add_iff (f := fun n ↦ (-d / (z : ℂ) - n)⁻¹ + (-d / (z : ℂ) + n)⁻¹)] at this
    apply this.subtype
/-
**EisensteinSeries.aux_tendsto_tsum_cexp_pnat** 是 Mathlib 中的一个引理，位于命名空间 `Eisenst
einSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_tendsto_tsum_cexp_pnat :
    Tendsto (fun N : ℕ+ ↦ ∑' (n : ℕ+), cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum_pnat (norm_exp_two_pi_I_lt_one ⟨_, im_pnat_div_pos 1 z⟩)
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_mul] at *
  exact this.congr <| by grind

/- Now this sum of terms with `-1 / z` tendsto `-2 * π * I / z` which is exactly `D2_S`. The key is
to use the cotangent series to write this as a sum of exponentials.-/
/-
**EisensteinSeries.aux_tendsto_tsum** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Now this sum of terms with `-1 / z` tendsto `-2 * π * I / z` which is exactly `D
2_S`. The key is
to use the cotangent series to write this as a sum of exponentials.
-/
private lemma aux_tendsto_tsum : Tendsto (fun n : ℕ ↦ 2 / z *
    ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m))) atTop (𝓝 (-2 * π * I / z)) := by
  rw [← PNat.tendsto_comp_val_iff]
  have H0 : (fun n : ℕ+ ↦ (2 / z * ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) =
      (fun n : ℕ+ ↦ (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' m : ℕ+, cexp (2 * π * I * (-n / z)) ^ (m : ℕ)) + 2 / n) := by
    ext N
    have h2 := cot_series_rep <| coe_mem_integerComplement ⟨-N / z, im_pnat_div_pos N z⟩
    rw [pi_mul_cot_pi_q_exp, ← sub_eq_iff_eq_add', one_div, inv_div, neg_mul, ← h2,
      ← tsum_zero_pnat_eq_tsum_nat
      (by simpa using norm_exp_two_pi_I_lt_one ⟨-N / z, im_pnat_div_pos N z⟩)] at *
    field [ne_zero z]
  rw [H0]
  nth_rw 2 [show -2 * π * I / z = (-2 * π * I / z) - (2 / z * (2 * π * I)) * 0 + 2 * 0 by ring]
  refine aux_tendsto_tsum_cexp_pnat z |>.const_mul _ |>.const_sub _ |>.add (.const_mul _ ?_)
  exact PNat.tendsto_comp_val_iff.mpr tendsto_inv_atTop_nhds_zero_nat

/- This shows that the limit of the conditional sum over larger intervals tends
to `-2 * π * I / z`. We will then show, in `tsum_tsum_symmetricIco_sub_eq` that if we swap the
order of the sum it tends to `0` instead. -/
/-
**EisensteinSeries.tendsto_tsum_one_div_linear_sub_succ_eq** 是 Mathlib 中的一个引理，位于
命名空间 `EisensteinSeries`。
形式化陈述：tendsto_tsum_one_div_linear_sub_succ_eq : Tendsto (fun N : Nat+ => ∑ n in 
Ico (-N : Int) N, ∑' m : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)
)) atTop (𝓝 (-2 * π * I / z))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Summable.tsum_finsetSum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β}
 [T2Space α] …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `EisensteinSeries.summable_left_one_div_linear_sub_one_div_linear`：summab
le_left_one_div_linear_sub_one_div_linear (a b : Int) : Summable fun m : Int => 
1 / (m * (z : Complex) + a) - 1 / (m * z + b)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.telescope_aux`：∀ (z : ℂ) (m : ℤ) (b : ℕ),   ∑ n ∈ Finset.Ico 
(-↑b) ↑b, (1 / (↑m * z + ↑n) - 1 / (↑m * z + ↑n + 1)) = 1 / (↑m * z - ↑b) - 1 / 
(↑m * z + ↑b)
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable.
0.EisensteinSeries.aux_tsum_identity_1`：∀ (z : UpperHalfPlane) (d : ℕ+),   ∑' (m
 : ℤ), (1 / (↑m * ↑z - ↑↑d) - 1 / (↑m * ↑z + ↑↑d)) =     -(2 / ↑↑d) +       ∑' (
m : ℕ+), (1 / (↑↑m *…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
This shows that the limit of the conditional sum over larger intervals tends
to `-2 * π * I / z`. We will then show, in `tsum_tsum_symmetricIco_sub_eq` that 
if we swap the
order of the sum it tends to `0` instead.
-/
lemma tendsto_tsum_one_div_linear_sub_succ_eq :
    Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) := by
  have (N : ℕ+) :
      ∑ n ∈ Ico (-N : ℤ) N, ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))
      = ∑' m : ℤ, ∑ n ∈ Ico (-N : ℤ) N, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) := by
    rw [Summable.tsum_finsetSum (fun i hi ↦ ?_)]
    apply (summable_left_one_div_linear_sub_one_div_linear z i (i + 1)).congr
    grind
  simp only [telescope_aux, aux_tsum_identity_1] at this
  rw [funext this, show -2 * π * I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · simpa [← PNat.tendsto_comp_val_iff] using!
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (-2)
  · simpa only [aux_tsum_identity_2, ← PNat.tendsto_comp_val_iff] using! aux_tendsto_tsum z

/- These are the two key lemmas, which show that swapping the order of summation gives
results differing by the term `-2 * π * I / z`. -/
/-
**EisensteinSeries.tsum_symmetricIco_tsum_sub_eq** 是 Mathlib 中的一个引理，位于命名空间 `Eise
nsteinSeries`。
形式化陈述：tsum_symmetricIco_tsum_sub_eq : ∑'[symmetricIco Int] n : Int, ∑' m : Int, 
(1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) = -2 * π * I / z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotSymmetricIco`：∀ (G : Type u_1) [inst : Neg G] [
inst_1 : Preorder G] [inst_2 : LocallyFiniteOrder G] [Filter.atTop.NeBot],   (Su
mmationFilter.symmetricIco …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `SummationFilter.symmetricIco_filter`：∀ (G : Type u_1) [inst : Neg G] [in
st_1 : Preorder G] [inst_2 : LocallyFiniteOrder G],   (SummationFilter.symmetric
Ico G).filter = Filter.ma…
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `EisensteinSeries.tendsto_tsum_one_div_linear_sub_succ_eq`：tendsto_tsum_o
ne_div_linear_sub_succ_eq : Tendsto (fun N : Nat+ => ∑ n in Ico (-N : Int) N, ∑'
 m : Int, (1 / ((m : Complex) * z + n) - 1 / (…

--- 原说明 ---
These are the two key lemmas, which show that swapping the order of summation gi
ves
results differing by the term `-2 * π * I / z`.
-/
lemma tsum_symmetricIco_tsum_sub_eq :
    ∑'[symmetricIco ℤ] n : ℤ, ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    -2 * π * I / z := by
  apply HasSum.tsum_eq
  simpa [HasSum, ← Nat.map_cast_int_atTop, ← PNat.tendsto_comp_val_iff]
    using tendsto_tsum_one_div_linear_sub_succ_eq z
/-
**EisensteinSeries.tsum_tsum_symmetricIco_sub_eq** 是 Mathlib 中的一个引理，位于命名空间 `Eise
nsteinSeries`。
形式化陈述：tsum_tsum_symmetricIco_sub_eq : ∑' m : Int, ∑'[symmetricIco Int] n : Int, 
(1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `EisensteinSeries.tsum_symmetricIco_linear_sub_linear_add_one_eq_zero`：ts
um_symmetricIco_linear_sub_linear_add_one_eq_zero (m : Int) : ∑'[symmetricIco In
t] n : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n …
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
-/
lemma tsum_tsum_symmetricIco_sub_eq :
    ∑' m : ℤ, ∑'[symmetricIco ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  convert! tsum_zero
  exact tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z _

end Auxiliary

end EisensteinSeries

