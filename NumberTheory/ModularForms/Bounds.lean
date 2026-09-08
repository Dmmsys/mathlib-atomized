/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Bounds for the norm of a modular form

We prove bounds for the norm of a modular form `f τ` in terms of `im τ`, and deduce polynomial
bounds for its q-expansion coefficients. The main results are

* `ModularFormClass.exists_bound`: a modular form of weight `k` (for an arithmetic subgroup `Γ`)
  is bounded by a constant multiple of `max 1 (1 / (im τ) ^ k))`.
* `CuspFormClass.exists_bound`: a cusp form of weight `k` (for an arithmetic subgroup `Γ`)
  is bounded by a constant multiple of `1 / (im τ) ^ (k / 2)`.
* `ModularFormClass.qExpansion_isBigO`: for a a modular form of weight `k` (for an arithmetic
  subgroup `Γ`), the `n`-th q-expansion coefficient is `O(n ^ k)`.
* `CuspFormClass.qExpansion_isBigO`: **Hecke's bound** for a a cusp form of weight `k` (for
  an arithmetic subgroup `Γ`): the `n`-th q-expansion coefficient is `O(n ^ (k / 2))`.
-/

public section

open Filter Topology Asymptotics Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

open UpperHalfPlane hiding I

open Matrix hiding mul_smul

open scoped Modular MatrixGroups ComplexConjugate ModularForm

variable {E : Type*} [SeminormedAddCommGroup E]

namespace ModularGroup

/-
**ModularGroup.exists_bound_fundamental_domain_of_isBigO** 是 Mathlib 中的一个引理，位于命名
空间 `ModularGroup`。
形式化陈述：exists_bound_fundamental_domain_of_isBigO {f : ℍ -> E} (hf_cont : Continuo
us f) {t : Real} (hf_infinity : f =O[atImInfty] fun z => z.im ^ t) : exists F, f
orall τ in 𝒟, ‖f τ‖ <= F * τ.im ^ t
参数：hf_cont : Continuous f；hf_infinity : f =O[atImInfty] fun z => z.im ^ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.eventually_comap`：eventually_comap : (forallᶠ a in comap f l, p a
) ↔ forallᶠ b in l, forall a, f a = b -> p a
· 使用定理 `UpperHalfPlane.atImInfty.eq_1`：UpperHalfPlane.atImInfty = Filter.comap U
pperHalfPlane.im Filter.atTop
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.div`：Continuous.div (hf : Continuous f) (hg : Continuous g) (
h₀ : forall x, g x != 0) : Continuous (f / g)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.rpow_const`：Continuous.rpow_const (hf : Continuous f) (h : fo
rall x, f x != 0 ∨ 0 <= p) : Continuous fun x => f x ^ p
· 使用定理 `UpperHalfPlane.continuous_im`：continuous_im : Continuous im
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
（共 47 条，此处仅展示前 30 条）
-/
lemma exists_bound_fundamental_domain_of_isBigO
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (hf_infinity : f =O[atImInfty] fun z ↦ z.im ^ t) :
    ∃ F, ∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t := by
  -- Extract a bound for large `im τ` using `hf_infty`.
  obtain ⟨D, hD, hf_infinity⟩ := hf_infinity.exists_pos
  rw [IsBigOWith, atImInfty, eventually_comap, eventually_atTop] at hf_infinity
  obtain ⟨y, hy⟩ := hf_infinity
  simp only [Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le] at hy
  -- Extract a bound for the rest of `𝒟` using continuity and compactness.
  have hfm : ContinuousOn (fun τ ↦ ‖f τ‖ / (im τ) ^ t) (truncatedFundamentalDomain y) := by
    apply (hf_cont.norm.div ?_ fun τ ↦ by positivity).continuousOn
    exact continuous_im.rpow_const fun τ ↦ .inl τ.im_ne_zero
  obtain ⟨E, hE⟩ : ∃ E, ∀ τ ∈ truncatedFundamentalDomain y, ‖f τ‖ / (im τ) ^ t ≤ E := by
    simpa [norm_mul, norm_norm, Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le]
      using (isCompact_truncatedFundamentalDomain y).exists_bound_of_continuousOn hfm
  -- Put the two bounds together.
  refine ⟨max D E, fun τ hτ ↦ ?_⟩
  rcases le_total y (im τ) with hτ' | hτ'
  · exact (hy _ hτ' _ rfl).trans <| mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
  · rw [← div_le_iff₀ (by positivity)]
    exact (hE τ ⟨hτ, hτ'⟩).trans (le_max_right _ _)

/-- A function on `ℍ` which is invariant under `SL(2, ℤ)`, and is `O ((im τ) ^ t)` at `I∞` for
some `0 ≤ t`, is bounded on `ℍ` by a constant multiple of `(max (im τ) (1 / im τ)) ^ t`.

This will be applied to `f τ * (im τ) ^ (k / 2)` for `f` a modular form of weight `k`, taking
`t = 0` if `f` is cuspidal, and `t = k / 2` otherwise. -/
/-
**ModularGroup.exists_bound_of_invariant_of_isBigO** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dularGroup`。
形式化陈述：exists_bound_of_invariant_of_isBigO {f : ℍ -> E} (hf_cont : Continuous f) 
{t : Real} (ht : 0 <= t) (hf_infinity : f =O[atImInfty] fun z => (im z) ^ t) (hf
_inv : forall (g : SL(2, Int)) τ, f (g • τ) = f τ) : exists C, forall τ, ‖f τ‖ <
= C * (max (im τ) (1 / im τ)) ^ t
参数：hf_cont : Continuous f；ht : 0 <= t；hf_infinity : f =O[atImInfty] fun z => (im
 z) ^ t；hf_inv : forall (g : SL(2, Int)) τ, f (g • τ) = f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModularGroup.exists_bound_fundamental_domain_of_isBigO`：exists_bound_fun
damental_domain_of_isBigO {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (hf_i
nfinity : f =O[atImInfty] fun z => z.im ^ t)…
· 使用定理 `ModularGroup.exists_smul_mem_fd`：exists_smul_mem_fd (z : ℍ) : exists g :
 SL(2, Int), g • z in 𝒟
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `ModularGroup.im_smul_eq_div_normSq`：im_smul_eq_div_normSq : (g • z).im =
 z.im / Complex.normSq (denom g z)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ModularGroup.denom_apply`：denom_apply : denom g z = g 1 0 * z + g 1 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_le_sq_iff_one_le_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : Lin
earOrder α] [IsStrictOrderedRing α] (a : α), 1 ≤ a ^ 2 ↔ 1 ≤ |a|
· 使用定理 `Int.one_le_abs`：one_le_abs {z : Int} (h₀ : z != 0) : 1 <= |z|
（共 157 条，此处仅展示前 30 条）

--- 原说明 ---
A function on `ℍ` which is invariant under `SL(2, ℤ)`, and is `O ((im τ) ^ t)` a
t `I∞` for
some `0 ≤ t`, is bounded on `ℍ` by a constant multiple of `(max (im τ) (1 / im τ
)) ^ t`.

This will be applied to `f τ * (im τ) ^ (k / 2)` for `f` a modular form of weigh
t `k`, taking
`t = 0` if `f` is cuspidal, and `t = k / 2` otherwise.
-/
lemma exists_bound_of_invariant_of_isBigO {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : f =O[atImInfty] fun z ↦ (im z) ^ t)
    (hf_inv : ∀ (g : SL(2, ℤ)) τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * (max (im τ) (1 / im τ)) ^ t := by
  -- First find an `F` such that `∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t`.
  obtain ⟨F, hF𝒟⟩ : ∃ F, ∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t :=
    exists_bound_fundamental_domain_of_isBigO hf_cont hf_infinity
  refine ⟨F, fun τ ↦ ?_⟩
  -- Given `τ`, choose a `g = [a, b; c, d] ∈ SL(2, ℤ)` that translates `τ` into `𝒟`.
  obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
  specialize hF𝒟 (g • τ) hg
  rw [hf_inv g τ] at hF𝒟
  grw [hF𝒟]
  gcongr
  · rw [← div_le_iff₀ (by positivity)] at hF𝒟
    exact le_trans (by positivity) hF𝒟
  -- It remains to show `(g • τ).im ≤ max τ.im (1 / τ.im)`.
  -- We split into two cases depending whether `c = g 1 0` is zero.
  rw [im_smul_eq_div_normSq, denom_apply]
  by_cases hg : g 1 0 = 0
  · -- If `c = 0`, then `(g • τ).im = τ.im / d ^ 2` and `d ^ 2 ≥ 1`.
    -- (In fact `d = ±1`, but we do not need this stronger statement).
    have : g 1 1 ≠ 0 := fun hg' ↦ zero_ne_one <| by
      simpa only [Matrix.det_fin_two, hg, hg', mul_zero, mul_zero, sub_zero] using g.det_coe
    have : (1 : ℝ) ≤ g 1 1 ^ 2 := mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs this)
    refine le_trans ?_ <| le_max_left _ _
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) = (g 1 1) ^ 2 by simp [hg, sq]]
    simpa [field] using inv_le_one_of_one_le₀ this
  · -- If `c ≠ 0`, then `1 ≤ c ^ 2`, so
    -- `(g • τ).im = τ.im / (c ^ 2 * τ.im ^ 2 +  ...) ≤ 1 / τ.im`.
    refine le_trans ?_ <| le_max_right _ _
    rw [show 1 / τ.im = τ.im / τ.im ^ 2 by field_simp]
    gcongr
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) =
      ((g 1 0) * τ.re + (g 1 1)) ^ 2 + (g 1 0) ^ 2 * τ.im ^ 2 by simp [Complex.normSq_apply]; ring]
    have : (1 : ℝ) ≤ g 1 0 ^ 2 := mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hg)
    nlinarith

/-- A function on `ℍ` which is invariant under a finite-index subgroup of `SL(2, ℤ)`, and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bounded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`. -/
/-
**ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO** 是 Mathlib 中的一个引理，位
于命名空间 `ModularGroup`。
形式化陈述：exists_bound_of_subgroup_invariant_of_isBigO {f : ℍ -> E} (hf_cont : Conti
nuous f) {t : Real} (ht : 0 <= t) (hf_infinity : forall (g : SL(2, Int)), (fun τ
 => f (g • τ)) =O[atImInfty] fun z => (im z) ^ t) {Γ : Subgroup SL(2, Int)} [Γ.F
initeIndex] (hf_inv : forall g in Γ, forall τ, f (g • τ) = f τ) : exists C, fora
ll τ, ‖f τ‖ <= C * max τ.im (1 / τ.im) ^ t
参数：hf_cont : Continuous f；ht : 0 <= t；hf_infinity : forall (g : SL(2, Int)), (fu
n τ => f (g • τ)) =O[atImInfty] fun z => (im z) ^ t；2, Int；hf_inv : forall g in 
Γ, forall τ, f (g • τ) = f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.eq_iff_equiv`：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : 
Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用引理 `ModularGroup.exists_bound_of_invariant_of_isBigO`：exists_bound_of_invari
ant_of_isBigO {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (ht : 0 <= t) (hf
_infinity : f =O[atImInfty] fun z => (…
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Asymptotics.IsBigO.fun_sum`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filt
er α} {ι : Type …
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
A function on `ℍ` which is invariant under a finite-index subgroup of `SL(2, ℤ)`
, and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bou
nded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`.
-/
lemma exists_bound_of_subgroup_invariant_of_isBigO
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : ∀ (g : SL(2, ℤ)), (fun τ ↦ f (g • τ)) =O[atImInfty] fun z ↦ (im z) ^ t)
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * max τ.im (1 / τ.im) ^ t := by
  -- marshall the info we have in terms of a function on the quotient
  let f' τ : SL(2, ℤ) ⧸ Γ → E := Quotient.lift (fun g ↦ f (g⁻¹ • τ)) fun g h hgh ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hgh
      exact ⟨g⁻¹ * h, hgh, (mul_inv_cancel_left g h).symm⟩
    simp [-sl_moeb, hj', mul_smul, hf_inv j⁻¹ (inv_mem hj)]
  have hf'_cont γ : Continuous (f' · γ) := QuotientGroup.induction_on γ fun g ↦ by
    simp only [sl_moeb, f']
    fun_prop
  have hf'_inv τ (g : SL(2, ℤ)) γ : f' (g • τ) (g • γ) = f' τ γ := by
    induction γ using QuotientGroup.induction_on
    simp [-sl_moeb, f', mul_smul]
  have hf'_infty γ : (f' · γ) =O[_] _ := γ.induction_on fun h ↦ hf_infinity h⁻¹
  -- now take the sum over the quotient
  have : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  -- Now the conclusion is very simple.
  obtain ⟨C, hC⟩ := exists_bound_of_invariant_of_isBigO (by fun_prop) ht
    (.fun_sum fun i _ ↦ (hf'_infty i).norm_left)
    (fun g τ ↦ (Fintype.sum_equiv (MulAction.toPerm g) _ _ (by simp [-sl_moeb, hf'_inv])).symm)
  refine ⟨C, fun τ ↦ le_trans ?_ (hC τ)⟩
  simpa [Real.norm_of_nonneg <| show 0 ≤ ∑ γ, ‖f' τ γ‖ by positivity, -sl_moeb, f'] using
    Finset.univ.single_le_sum (fun γ _ ↦ norm_nonneg (f' τ γ)) (Finset.mem_univ ⟦1⟧)

/-- A function on `ℍ` which is invariant under an arithmetic subgroup of `GL(2, ℝ)`, and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bounded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`. -/
/-
**ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO** 是 
Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO {f : ℍ -> E} 
(hf_cont : Continuous f) {t : Real} (ht : 0 <= t) (hf_infinity : forall (g : SL(
2, Int)), (fun τ => f (g • τ)) =O[atImInfty] fun z => (im z) ^ t) {Γ : Subgroup 
(GL (Fin 2) Real)} [Γ.IsArithmetic] (hf_inv : forall g in Γ, forall τ, f (g • τ)
 = f τ) : exists C, forall τ, ‖f τ‖ <= C * max τ.im (1 / τ.im) ^ t
参数：hf_cont : Continuous f；ht : 0 <= t；hf_infinity : forall (g : SL(2, Int)), (fu
n τ => f (g • τ)) =O[atImInfty] fun z => (im z) ^ t；GL (Fin 2) Real；hf_inv : for
all g in Γ, forall τ, f (g • τ) = f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO`：exists_bound_
of_subgroup_invariant_of_isBigO {f : ℍ -> E} (hf_cont : Continuous f) {t : Real}
 (ht : 0 <= t) (hf_infinity : forall (g : SL(2,…
· 使用定理 `Subgroup.IsArithmetic.finiteIndex_comap`：∀ (𝒢 : Subgroup (GL (Fin 2) ℝ))
 [𝒢.IsArithmetic], (Subgroup.comap (Matrix.SpecialLinearGroup.mapGL ℝ) 𝒢).Finite
Index

--- 原说明 ---
A function on `ℍ` which is invariant under an arithmetic subgroup of `GL(2, ℝ)`,
 and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bou
nded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`.
-/
lemma exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : ∀ (g : SL(2, ℤ)), (fun τ ↦ f (g • τ)) =O[atImInfty] fun z ↦ (im z) ^ t)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * max τ.im (1 / τ.im) ^ t :=
  exists_bound_of_subgroup_invariant_of_isBigO hf_cont ht hf_infinity (Γ := Γ.comap (mapGL ℝ))
    (hf_inv ·)

/-- A function on `ℍ` which is invariant under `SL(2, ℤ)`, and bounded at `∞`, is uniformly
bounded. -/
/-
**ModularGroup.exists_bound_of_invariant** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup
`。
形式化陈述：exists_bound_of_invariant {f : ℍ -> E} (hf_cont : Continuous f) (hf_infini
ty : IsBoundedAtImInfty f) (hf_inv : forall (g : SL(2, Int)) τ, f (g • τ) = f τ)
 : exists C, forall τ, ‖f τ‖ <= C
参数：hf_cont : Continuous f；hf_infinity : IsBoundedAtImInfty f；hf_inv : forall (g 
: SL(2, Int)) τ, f (g • τ) = f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `ModularGroup.exists_bound_of_invariant_of_isBigO`：exists_bound_of_invari
ant_of_isBigO {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (ht : 0 <= t) (hf
_infinity : f =O[atImInfty] fun z => (…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A function on `ℍ` which is invariant under `SL(2, ℤ)`, and bounded at `∞`, is un
iformly
bounded.
-/
lemma exists_bound_of_invariant
    {f : ℍ → E} (hf_cont : Continuous f) (hf_infinity : IsBoundedAtImInfty f)
    (hf_inv : ∀ (g : SL(2, ℤ)) τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  simpa using! exists_bound_of_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

/-- A function on `ℍ` which is invariant under an arithmetic subgroup and bounded at all cusps,
is uniformly bounded. -/
/-
**ModularGroup.exists_bound_of_subgroup_invariant** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ularGroup`。
形式化陈述：exists_bound_of_subgroup_invariant {f : ℍ -> E} (hf_cont : Continuous f) (
hf_infinity : forall (g : SL(2, Int)), IsBoundedAtImInfty fun τ => f (g • τ)) {Γ
 : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] (hf_inv : forall g in Γ, forall 
τ, f (g • τ) = f τ) : exists C, forall τ, ‖f τ‖ <= C
参数：hf_cont : Continuous f；hf_infinity : forall (g : SL(2, Int)), IsBoundedAtImIn
fty fun τ => f (g • τ)；GL (Fin 2) Real；hf_inv : forall g in Γ, forall τ, f (g • 
τ) = f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBig
O`：exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO {f : ℍ -> E} (hf
_cont : Continuous f) {t : Real} (ht : 0 <= t) (hf_infinity : f…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A function on `ℍ` which is invariant under an arithmetic subgroup and bounded at
 all cusps,
is uniformly bounded.
-/
lemma exists_bound_of_subgroup_invariant {f : ℍ → E} (hf_cont : Continuous f)
    (hf_infinity : ∀ (g : SL(2, ℤ)), IsBoundedAtImInfty fun τ ↦ f (g • τ))
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  simpa using! exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

end ModularGroup

/-- If `f, f'` are modular forms, then `petersson k f f'` is bounded by a constant multiple of
`max τ.im (1 / τ.im) ^ k`. -/
/-
**ModularFormClass.exists_petersson_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularFormClass.exists_petersson_le {k : Int} (hk : 0 <= k) (Γ : Subgroup
 (GL (Fin 2) Real)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F') [FunLike F
 ℍ Complex] [FunLike F' ℍ Complex] [ModularFormClass F Γ k] [ModularFormClass F'
 Γ k] : exists C, forall τ, ‖petersson k f f' τ‖ <= C * max τ.im (1 / τ.im) ^ k
参数：hk : 0 <= k；Γ : Subgroup (GL (Fin 2) Real)；f : F；f' : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用引理 `ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBig
O`：exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO {f : ℍ -> E} (hf
_cont : Continuous f) {t : Real} (ht : 0 <= t) (hf_infinity : f…
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用引理 `UpperHalfPlane.petersson_continuous`：petersson_continuous (k : Int) {f f
' : ℍ -> Complex} (hf : Continuous f) (hf' : Continuous f') : Continuous (peters
son k f f')
· 使用引理 `ModularFormClass.continuous`：ModularFormClass.continuous {k : Int} {Γ : 
Subgroup (GL (Fin 2) Real)} {F : Type*} [FunLike F ℍ Complex] [ModularFormClass 
F Γ k] (f : F) : …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `f, f'` are modular forms, then `petersson k f f'` is bounded by a constant m
ultiple of
`max τ.im (1 / τ.im) ^ k`.
-/
lemma ModularFormClass.exists_petersson_le {k : ℤ} (hk : 0 ≤ k) (Γ : Subgroup (GL (Fin 2) ℝ))
    [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C * max τ.im (1 / τ.im) ^ k := by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine mod_cast ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    (show Continuous (‖petersson k f f' ·‖) by fun_prop) (mod_cast hk : 0 ≤ (k : ℝ))
    (fun g ↦ ?_) (fun g hg τ ↦ SlashInvariantFormClass.norm_petersson_smul hg)
  simp_rw [← UpperHalfPlane.petersson_slash_SL, Real.rpow_intCast]
  simpa [petersson, Real.norm_of_nonneg (_ : ℍ).im_pos.le]
    using (bdd_at_infty_slash f g).norm_left.mul (bdd_at_infty_slash f' g).norm_left
      |>.mul (isBigO_refl ..)

open ConjAct Pointwise in
/-- If `f` is a cusp form and `f'` a modular form, then `petersson k f f'` is bounded. -/
/-
**CuspFormClass.petersson_bounded_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspFormClass.petersson_bounded_left (k : Int) (Γ : Subgroup (GL (Fin 2) R
eal)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F') [FunLike F ℍ Complex] [F
unLike F' ℍ Complex] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] : exists C,
 forall τ, ‖petersson k f f' τ‖ <= C
参数：k : Int；Γ : Subgroup (GL (Fin 2) Real)；f : F；f' : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用引理 `ModularGroup.exists_bound_of_subgroup_invariant`：exists_bound_of_subgrou
p_invariant {f : ℍ -> E} (hf_cont : Continuous f) (hf_infinity : forall (g : SL(
2, Int)), IsBoundedAtImInfty fun τ =>…
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用引理 `UpperHalfPlane.petersson_continuous`：petersson_continuous (k : Int) {f f
' : ℍ -> Complex} (hf : Continuous f) (hf' : Continuous f') : Continuous (peters
son k f f')
· 使用引理 `ModularFormClass.continuous`：ModularFormClass.continuous {k : Int} {Γ : 
Subgroup (GL (Fin 2) Real)} {F : Type*} [FunLike F ℍ Complex] [ModularFormClass 
F Γ k] (f : F) : …
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty`：∀ {α : Type u_1} [ins
t : SeminormedAddGroup α] {f : UpperHalfPlane → α},   UpperHalfPlane.IsZeroAtImI
nfty f → UpperHalfPlane.IsBoundedAtImIn…
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.eq_1`：∀ {α : Type u_1} [inst : Zero α] [i
nst_1 : TopologicalSpace α] (f : UpperHalfPlane → α),   UpperHalfPlane.IsZeroAtI
mInfty f = UpperHalfPlane…
· 使用定理 `Filter.ZeroAtFilter.eq_1`：∀ {α : Type u_2} {β : Type u_3} [inst : Zero β
] [inst_1 : TopologicalSpace β] (l : Filter α) (f : α → β),   l.ZeroAtFilter f =
 Filter.Tendst…
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Matrix.SpecialLinearGroup.map_mapGL`：map_mapGL {T : Type*} [CommRing T] 
[Algebra R T] [Algebra S T] [IsScalarTower R S T] (g : SpecialLinearGroup n R) :
 (mapGL S g).map (algebra…
· 使用定理 `Subgroup.IsArithmetic.conj`：∀ (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithme
tic] (g : GL (Fin 2) ℚ),   (ConjAct.toConjAct ((Matrix.GeneralLinearGroup.map (R
at.castHom ℝ)) g…
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left`：petersson
_isZeroAtImInfty_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') : IsZeroAtImI
nfty (petersson k f f')
· 使用定理 `instFactIsCuspInftyRealOfIsArithmetic`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [
Γ.IsArithmetic], Fact (IsCusp OnePoint.infty Γ)
· 使用定理 `Subgroup.instHasDetPlusMinusOneFinOfNatNatRealOfIsArithmetic`：∀ {Γ : Sub
group (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic], Γ.HasDetPlusMinusOne
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
· 使用引理 `SlashInvariantFormClass.norm_petersson_smul`：SlashInvariantFormClass.nor
m_petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
 [SlashInvariantFormClass F Γ k] …
· 使用定理 `CuspFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outParam 
(Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ} 
  [self : CuspFormClass F Γ k…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a cusp form and `f'` a modular form, then `petersson k f f'` is bounde
d.
-/
lemma CuspFormClass.petersson_bounded_left
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine ModularGroup.exists_bound_of_subgroup_invariant (by fun_prop) (fun g ↦ ?_)
    fun g hg τ ↦ SlashInvariantFormClass.norm_petersson_smul hg
  apply IsZeroAtImInfty.isBoundedAtImInfty
  rw [IsZeroAtImInfty, ZeroAtFilter, ← tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← UpperHalfPlane.petersson_slash_SL]
  have : ((toConjAct (g : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj Γ (mapGL ℚ g)⁻¹
  exact (zero_at_infty <| CuspForm.translate f g).petersson_isZeroAtImInfty_left k _
    (ModularForm.translate f' g)

/-- If `f` is a modular form and `f'` a cusp form, then `petersson k f f'` is bounded. -/
/-
**CuspFormClass.petersson_bounded_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspFormClass.petersson_bounded_right (k : Int) (Γ : Subgroup (GL (Fin 2) 
Real)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F') [FunLike F ℍ Complex] [
FunLike F' ℍ Complex] [ModularFormClass F Γ k] [CuspFormClass F' Γ k] : exists C
, forall τ, ‖petersson k f f' τ‖ <= C
参数：k : Int；Γ : Subgroup (GL (Fin 2) Real)；f : F；f' : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `UpperHalfPlane.petersson_norm_symm`：petersson_norm_symm (k : Int) (f f' 
: ℍ -> Complex) (τ : ℍ) : ‖petersson k f' f τ‖ = ‖petersson k f f' τ‖
· 使用引理 `CuspFormClass.petersson_bounded_left`：CuspFormClass.petersson_bounded_le
ft (k : Int) (Γ : Subgroup (GL (Fin 2) Real)) [Γ.IsArithmetic] {F F' : Type*} (f
 : F) (f' : F') [FunLike F…

--- 原说明 ---
If `f` is a modular form and `f'` a cusp form, then `petersson k f f'` is bounde
d.
-/
lemma CuspFormClass.petersson_bounded_right
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [CuspFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  simpa [petersson_norm_symm] using petersson_bounded_left k Γ f' f

/-- A weight `k` cusp form is bounded in norm by a constant multiple of `(im τ) ^ (-k / 2)`. -/
/-
**CuspFormClass.exists_bound** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspFormClass.exists_bound {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.I
sArithmetic] {F : Type*} [FunLike F ℍ Complex] [CuspFormClass F Γ k] (f : F) : e
xists C, forall τ, ‖f τ‖ <= C / τ.im ^ (k / 2 : Real)
参数：GL (Fin 2) Real；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CuspFormClass.petersson_bounded_left`：CuspFormClass.petersson_bounded_le
ft (k : Int) (Γ : Subgroup (GL (Fin 2) Real)) [Γ.IsArithmetic] {F F' : Type*} (f
 : F) (f' : F') [FunLike F…
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_le_sq₀`：sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <=
 b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `UpperHalfPlane.petersson.eq_1`：∀ (k : ℤ) (f f' : UpperHalfPlane → ℂ) (τ 
: UpperHalfPlane),   UpperHalfPlane.petersson k f f' τ = (starRingEnd ℂ) (f τ) *
 f' τ * ↑τ.im ^ k
· 使用引理 `Real.rpow_mul_natCast`：rpow_mul_natCast (hx : 0 <= x) (y : Real) (n : Na
t) : x ^ (y * n) = (x ^ y) ^ n
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
A weight `k` cusp form is bounded in norm by a constant multiple of `(im τ) ^ (-
k / 2)`.
-/
lemma CuspFormClass.exists_bound {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C / τ.im ^ (k / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  specialize hC τ
  rw [← sq_le_sq₀ (by positivity) (by positivity), div_pow, Real.sq_sqrt ((norm_nonneg _).trans hC)]
  grw [← hC]
  rw [petersson, ← Real.rpow_mul_natCast τ.im_pos.le]
  simp [abs_of_pos τ.im_pos, field]

open Real in
/-- A weight `k` modular form is bounded in norm by a constant multiple of
`max 1 (1 / (τ.im) ^ k)`. -/
/-
**ModularFormClass.exists_bound** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularFormClass.exists_bound {k : Int} (hk : 0 <= k) {Γ : Subgroup (GL (F
in 2) Real)} [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [ModularFormClas
s F Γ k] (f : F) : exists C, forall τ, ‖f τ‖ <= C * (max 1 (1 / (τ.im) ^ k))
参数：hk : 0 <= k；GL (Fin 2) Real；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModularFormClass.exists_petersson_le`：ModularFormClass.exists_petersson_
le {k : Int} (hk : 0 <= k) (Γ : Subgroup (GL (Fin 2) Real)) [Γ.IsArithmetic] {F 
F' : Type*} (f : F) (f' : …
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
（共 97 条，此处仅展示前 30 条）

--- 原说明 ---
A weight `k` modular form is bounded in norm by a constant multiple of
`max 1 (1 / (τ.im) ^ k)`.
-/
lemma ModularFormClass.exists_bound {k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * (max 1 (1 / (τ.im) ^ k)) := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_petersson_le hk Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  lift k to ℕ using hk
  specialize hC τ
  have hC' : 0 ≤ C := le_trans (by positivity) <| (div_le_iff₀ (by positivity)).mpr hC
  have h : 0 < ‖(τ.im : ℂ) ^ (k : ℤ)‖ := mod_cast norm_pos_iff.mpr (pow_ne_zero _ τ.im_ne_zero)
  rw [petersson, norm_mul, norm_mul, Complex.norm_conj, ← sq, ← le_div_iff₀ h, mul_div_assoc] at hC
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, sq_sqrt hC']
  refine hC.trans (congrArg (C * ·) ?_).le
  -- remains to show `(max τ.im (1 / τ.im)) ^ k / ‖τ.im ^ k‖ = (max 1 (1 / τ.im ^ k)) ^ 2`,
  -- which is easier after lifting to `NNReal`
  generalize h : τ.im = t
  have ht : 0 < t := h ▸ τ.im_pos
  lift t to NNReal using ht.le
  rw [← coe_nnnorm]
  norm_cast at ⊢ ht
  rw [(pow_left_mono k).map_max, (pow_left_mono 2).map_max, ← max_div_div_right (by positivity)]
  congr <;> simp [field, ht.ne']

local notation "𝕢" => Function.Periodic.qParam

open Complex ModularFormClass

/-- General result on bounding q-expansion coefficients using a bound on the norm of the function.
This will get used twice over, once for cusp forms (with `e = k / 2`) and once for modular forms
(with `e = k`). -/
/-
**qExpansion_coeff_isBigO_of_norm_isBigO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：qExpansion_coeff_isBigO_of_norm_isBigO {k : Int} {Γ : Subgroup (GL (Fin 2)
 Real)} [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [ModularFormClass F Γ
 k] (f : F) (e : Real) (hF : IsBigO (comap UpperHalfPlane.im (𝓝 0)) f (fun τ => 
τ.im ^ (-e))) : (fun n => (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] f
un n => (n : Real) ^ e
参数：GL (Fin 2) Real；f : F；e : Real；hF : IsBigO (comap UpperHalfPlane.im (𝓝 0)) f 
(fun τ => τ.im ^ (-e))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subgroup.strictWidthInfty_pos_iff`：strictWidthInfty_pos_iff [DiscreteTop
ology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] : 0 < 𝒢.strictWidthInfty ↔ IsCusp 
∞ 𝒢
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Subgroup.instHasDetPlusMinusOneFinOfNatNatRealOfIsArithmetic`：∀ {Γ : Sub
group (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic], Γ.HasDetPlusMinusOne
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `instFactIsCuspInftyRealOfIsArithmetic`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [
Γ.IsArithmetic], Fact (IsCusp OnePoint.infty Γ)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Subgroup.strictWidthInfty_mem_strictPeriods`：strictWidthInfty_mem_strict
Periods : 𝒢.strictWidthInfty in 𝒢.strictPeriods
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Filter.eventually_comap`：eventually_comap : (forallᶠ a in comap f l, p a
) ↔ forallᶠ b in l, forall a, f a = b -> p a
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 159 条，此处仅展示前 30 条）

--- 原说明 ---
General result on bounding q-expansion coefficients using a bound on the norm of
 the function.
This will get used twice over, once for cusp forms (with `e = k / 2`) and once f
or modular forms
(with `e = k`).
-/
lemma qExpansion_coeff_isBigO_of_norm_isBigO {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) (e : ℝ)
    (hF : IsBigO (comap UpperHalfPlane.im (𝓝 0)) f (fun τ ↦ τ.im ^ (-e))) :
    (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ e := by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have : NeZero h := ⟨hh.ne'⟩
  have hΓ : h ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  obtain ⟨C, Cpos, hC⟩ := hF.exists_pos
  rw [isBigO_iff]
  rw [IsBigOWith, eventually_comap] at hC
  use (1 / Real.exp (-2 * Real.pi / ↑h)) * C
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually hC] with n hn hn'
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral (t := 1 / n) f hh hΓ _ (by positivity),
    ← intervalIntegral.integral_const_mul]
  simp only [ofReal_div, ofReal_one, ofReal_natCast]
  refine intervalIntegral.norm_integral_le_integral_norm (by positivity) |>.trans ?_
  let F (x : ℝ) : ℝ := ‖1 / ↑h * (1 / 𝕢 h ((x : ℂ) + 1 / n * I) ^ n
      * f ⟨(x : ℂ) + 1 / n * Complex.I, by simp [hn]⟩)‖
  have hne : ‖(n : ℝ) ^ e‖ = n ^ e := Real.norm_of_nonneg (by positivity)
  have (x : ℝ) : F x ≤ 1 / h * (1 / Real.exp (-2 * Real.pi / ↑h)) * (C * n ^ e) := by
    simp only [F, norm_mul, norm_div, norm_real, norm_one, norm_pow, mul_assoc]
    rw [Real.norm_of_nonneg hh.le, Function.Periodic.norm_qParam, ← Real.exp_nat_mul]
    gcongr
    · simp [field]
    · grw [hn' _ (by simp [← UpperHalfPlane.coe_im])]
      simp [← UpperHalfPlane.coe_im, Real.rpow_neg_eq_inv_rpow, hne]
  refine (intervalIntegral.integral_mono (by positivity) ?_ ?_ this).trans (le_of_eq ?_)
  · apply Continuous.intervalIntegrable
    fun_prop (disch := simp [Function.Periodic.qParam_ne_zero])
  · exact continuous_const.intervalIntegrable ..
  · simp [field, intervalIntegral.integral_const, hne]

/-- Bound for the coefficients of a modular form: if `f` is a weight `k` modular form for an
arithmetic subgroup, then its `q`-expansion coefficients are `O (n ^ k)`.

This is not optimal -- the optimal exponent is `k - 1 + ε` for any `0 < ε`, at least for congruence
levels -- but is much easier to prove than the optimal result.

See `CuspFormClass.qExpansion_isBigO` for a sharper bound assuming `f` is cuspidal. -/
/-
**ModularFormClass.qExpansion_isBigO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularFormClass.qExpansion_isBigO {k : Int} (hk : 0 <= k) {Γ : Subgroup (
GL (Fin 2) Real)} [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [ModularFor
mClass F Γ k] (f : F) : (fun n => (qExpansion Γ.strictWidthInfty f).coeff n) =O[
atTop] fun n => (n : Real) ^ k
参数：hk : 0 <= k；GL (Fin 2) Real；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `qExpansion_coeff_isBigO_of_norm_isBigO`：qExpansion_coeff_isBigO_of_norm_
isBigO {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] {F : Type*} [
FunLike F ℍ Complex] [Modula…
· 使用引理 `ModularFormClass.exists_bound`：ModularFormClass.exists_bound {k : Int} (
hk : 0 <= k) {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] {F : Type*} [FunL
ike F ℍ Complex] [M…
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_le_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x ≤ b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `one_le_one_div`：one_le_one_div (h1 : 0 < a) (h2 : a <= 1) : 1 <= 1 / a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `zpow_le_one₀`：zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : 0 <= n) : 
a ^ n <= 1
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Bound for the coefficients of a modular form: if `f` is a weight `k` modular for
m for an
arithmetic subgroup, then its `q`-expansion coefficients are `O (n ^ k)`.

This is not optimal -- the optimal exponent is `k - 1 + ε` for any `0 < ε`, at l
east for congruence
levels -- but is much easier to prove than the optimal result.

See `CuspFormClass.qExpansion_isBigO` for a sharper bound assuming `f` is cuspid
al.
-/
lemma ModularFormClass.qExpansion_isBigO {k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ k := by
  simp only [← Real.rpow_intCast]
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound hk f
  simp_rw [IsBigO, ← Int.cast_neg, Real.rpow_intCast, IsBigOWith, eventually_comap]
  use C
  filter_upwards [eventually_le_nhds zero_lt_one] with _ hτ τ rfl
  refine (hC τ).trans (le_of_eq ?_)
  rw [max_eq_right, zpow_neg, Real.norm_of_nonneg (by positivity), one_div]
  exact one_le_one_div (by positivity) (zpow_le_one₀ τ.im_pos hτ hk)

/-- **Hecke's bound** for the coefficients of a cusp form: if `f` is a weight `k` modular form for
an arithmetic subgroup, then its `q`-expansion coefficients are `O (n ^ (k / 2))`.

This is not optimal -- the optimal exponent is `(k - 1) / 2 + ε` for any `0 < ε`, at least for
congruence levels -- but is much easier to prove than the optimal result. -/
/-
**CuspFormClass.qExpansion_isBigO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspFormClass.qExpansion_isBigO {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
 [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [CuspFormClass F Γ k] (f : F
) : (fun n => (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop
] fun n => (n : Real) ^ ((k : Real) / 2)
参数：GL (Fin 2) Real；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `qExpansion_coeff_isBigO_of_norm_isBigO`：qExpansion_coeff_isBigO_of_norm_
isBigO {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] {F : Type*} [
FunLike F ℍ Complex] [Modula…
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CuspFormClass.exists_bound`：CuspFormClass.exists_bound {k : Int} {Γ : Su
bgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [Cu
spFormClass F Γ …
· 使用定理 `Asymptotics.isBigO_of_le'`：isBigO_of_le' (hfg : forall x, ‖f x‖ <= c * ‖
g x‖) : f =O[l] g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq`：of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹

--- 原说明 ---
**Hecke's bound** for the coefficients of a cusp form: if `f` is a weight `k` mo
dular form for
an arithmetic subgroup, then its `q`-expansion coefficients are `O (n ^ (k / 2))
`.

This is not optimal -- the optimal exponent is `(k - 1) / 2 + ε` for any `0 < ε`
, at least for
congruence levels -- but is much easier to prove than the optimal result.
-/
lemma CuspFormClass.qExpansion_isBigO {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    (fun n ↦ (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n)
      =O[atTop] fun n ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound f
  refine isBigO_of_le' (c := C) _ fun τ ↦ (hC τ).trans (of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg τ.im_pos.le, div_eq_mul_inv]
