/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DividedPowers.RatAlgebra

/-! # Divided powers on `ℤ_[p]`

Given a divided power algebra `(B, J, δ)` and an injective ring morphism `f : A →+* B`, if `I` is
an `A`-ideal such that `I.map f = J` and such that for all `n : ℕ`, `x ∈ I`, the preimage of
`hJ.dpow n (f x)` under `f` belongs to `I`, we get an induced divided power structure on `I`.

We specialize this construction to the coercion map `ℤ_[p] →+* ℚ_[p]` to get a divided power
structure on the ideal `(p) ⊆ ℤ_[p]`. This divided power structure is given by the family of maps
`fun n x ↦ x^n / n!`.

TODO: If `K` is a `p`-adic local field with ring of integers `R` and uniformizer `π` such that
`p = u * π^e` for some unit `u`, then the ideal `(π) ⊆ R` has divided powers if and only if
`e ≤ p - 1`.

-/

@[expose] public section

open DividedPowers DividedPowers.OfInvertibleFactorial Nat Ring

section Injective

open Function

variable {A B : Type*} [CommSemiring A] [CommSemiring B] (I : Ideal A) (J : Ideal B)

/-- Given a divided power algebra `(B, J, δ)` and an injective ring morphism `f : A →+* B`, if `I`
is an `A`-ideal such that `I.map f = J` and such that for all `n : ℕ`, `x ∈ I`, the preimage of
`hJ.dpow n (f x)` under `f` belongs to `I`, this is the induced divided power structure on `I`. -/
/-
**DividedPowers.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DividedPowers.ofInjective (f : A ->+* B) (hf : Injective f) (hJ : DividedP
owers J) (hIJ : I.map f = J) (hmem : forall (n : Nat) {x : A} (_ : x in I), exis
ts (y : A) (_ : n != 0 -> y in I), f y = hJ.dpow n (f x)) : DividedPowers I wher
e dpow n x
参数：f : A ->+* B；hf : Injective f；hJ : DividedPowers J；hIJ : I.map f = J；hmem : f
orall (n : Nat) {x : A} (_ : x in I), exists (y : A) (_ : n != 0 -> y in I), f y
 = hJ.dpow n (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a divided power algebra `(B, J, δ)` and an injective ring morphism `f : A 
→+* B`, if `I`
is an `A`-ideal such that `I.map f = J` and such that for all `n : ℕ`, `x ∈ I`, 
the preimage of
`hJ.dpow n (f x)` under `f` belongs to `I`, this is the induced divided power st
ructure on `I`.
-/
noncomputable def DividedPowers.ofInjective (f : A →+* B) (hf : Injective f)
    (hJ : DividedPowers J) (hIJ : I.map f = J)
    (hmem : ∀ (n : ℕ) {x : A} (_ : x ∈ I), ∃ (y : A) (_ : n ≠ 0 → y ∈ I), f y = hJ.dpow n (f x)) :
    DividedPowers I where
  dpow n x := open scoped Classical in if hx : x ∈ I then Exists.choose (hmem n hx) else 0
  dpow_null hx := by simp [dif_neg hx]
  dpow_zero {x} hx := by
    simp only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (hmem 0 hx)).2, map_one]
    rw [hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hx)]
  dpow_one hx := by
    simpa only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2]
      using hJ.dpow_one (hIJ ▸ Ideal.mem_map_of_mem f hx)
  dpow_mem {n x} hn hx := by simpa only [dif_pos hx] using (Exists.choose_spec (hmem n hx)).1 hn
  dpow_add {n x y} hx hy := by
    have hxy : x + y ∈ I := Ideal.add_mem _ hx hy
    simpa only [dif_pos hxy, dif_pos hx, dif_pos hy, ← hf.eq_iff, map_sum, map_mul,
      (Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2, map_add]
      using hJ.dpow_add (hIJ ▸ I.mem_map_of_mem f hx) (hIJ ▸ I.mem_map_of_mem f hy)
  dpow_mul {n a x} hx := by
    have hax : a * x ∈ I := Ideal.mul_mem_left _ _ hx
    simpa only [(Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2, dif_pos hax, dif_pos hx,
    ← hf.eq_iff, map_mul, map_pow] using hJ.dpow_mul (hIJ ▸ I.mem_map_of_mem f hx)
  mul_dpow hx := by simpa only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (hmem _ hx)).2,
    map_mul, map_natCast] using hJ.mul_dpow (hIJ ▸ I.mem_map_of_mem f hx)
  dpow_comp {n m x} hm hx := by
    simp only [dif_pos hx, ← hf.eq_iff, map_mul, map_natCast]
    -- the condition for the other `dif_pos` is a bit messy so we use `rw` to
    -- spin it off into a separate branch
    rw [dif_pos]
    · simp only [(Exists.choose_spec (_ : ∃ a, ∃ _, f a = _)).2]
      exact hJ.dpow_comp hm (hIJ ▸ I.mem_map_of_mem f hx)
    · rw [dif_pos hx]
      exact (Exists.choose_spec (hmem m hx)).1 hm

end Injective

namespace PadicInt

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

set_option backward.privateInPublic true in
/-- The family `ℕ → ℚ_[p] → ℚ_[p]` given by `dpow n x = x ^ n / n!`. -/
/-
**PadicInt.dpow'** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family `ℕ → ℚ_[p] → ℚ_[p]` given by `dpow n x = x ^ n / n!`.
-/
private noncomputable def dpow' : ℕ → ℚ_[p] → ℚ_[p] := fun m x => inverse (m ! : ℚ_[p]) * x ^ m
/-
**PadicInt.dpow'_norm_le_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma dpow'_norm_le_of_ne_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : ‖dpow' p n x‖ ≤ (p : ℝ)⁻¹ := by
  unfold dpow'
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [inverse_eq_inv', coe_zero, ne_eq, hn, not_false_eq_true, zero_pow, mul_zero,
      norm_zero, inv_nonneg, cast_nonneg]
  · have hlt : (padicValNat p n.factorial : ℤ) < n := by
      exact_mod_cast padicValNat_factorial_lt_of_ne_zero p hn
    have hnorm : 0 < ‖(n ! : ℚ_[p])‖ := by
      simp only [norm_pos_iff, ne_eq, cast_eq_zero]
      exact factorial_ne_zero n
    rw [← zpow_neg_one, ← Nat.cast_one (R := ℤ), Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simp only [inverse_eq_inv', Padic.padicNormE.mul, norm_inv, _root_.norm_pow,
      padic_norm_e_of_padicInt, cast_one, Int.reduceNeg, neg_add_cancel, zpow_zero]
    rw [norm_eq_zpow_neg_valuation hx0, inv_mul_lt_one₀ hnorm, Padic.norm_eq_zpow_neg_valuation
      (cast_ne_zero.mpr n.factorial_ne_zero), ← zpow_natCast, ← zpow_mul]
    gcongr
    · exact_mod_cast Nat.Prime.one_lt hp.elim
    · simp only [neg_mul, Padic.valuation_natCast, neg_lt_neg_iff]
      apply lt_of_lt_of_le hlt
      conv_lhs => rw [← one_mul (n : ℤ)]
      gcongr
      norm_cast
      rwa [← PadicInt.mem_span_pow_iff_le_valuation x hx0, pow_one]

set_option backward.privateInPublic true in
/-
**PadicInt.dpow'_int** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma dpow'_int (n : ℕ) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖dpow' p n x‖ ≤ 1 := by
  unfold dpow'
  by_cases hn : n = 0
  · simp [hn]
  · apply le_trans (dpow'_norm_le_of_ne_zero p hn hx)
    rw [← zpow_neg_one, ← zpow_zero ↑p]
    gcongr
    · exact_mod_cast Nat.Prime.one_le hp.elim
    · norm_num

set_option backward.privateInPublic true in
/-
**PadicInt.dpow'_mem** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem dpow'_mem {n : ℕ} {x : ℤ_[p]} (hm : n ≠ 0) (hx : x ∈ Ideal.span {↑p}) :
    ⟨dpow' p n x, dpow'_int p n hx⟩ ∈ Ideal.span {(p : ℤ_[p])} := by
  have hiff := PadicInt.norm_le_pow_iff_mem_span_pow ⟨dpow' p n x, dpow'_int p n hx⟩ 1
  rw [pow_one] at hiff
  rw [← hiff]
  simp only [cast_one, zpow_neg_one]
  exact dpow'_norm_le_of_ne_zero p hm hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The family `ℕ → Ideal.span {(p : ℤ_[p])} → ℤ_[p]` given by `dpow n x = x ^ n / n!` is a
  divided power structure on the `ℤ_[p]`-ideal `(p)`. -/
/-
**PadicInt.dividedPowers** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：dividedPowers : DividedPowers (Ideal.span {(p : Int_[p])})
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]

--- 原说明 ---
The family `ℕ → Ideal.span {(p : ℤ_[p])} → ℤ_[p]` given by `dpow n x = x ^ n / n
!` is a
  divided power structure on the `ℤ_[p]`-ideal `(p)`.
-/
noncomputable def dividedPowers : DividedPowers (Ideal.span {(p : ℤ_[p])}) := by
  classical
  refine ofInjective (Ideal.span {(p : ℤ_[p])}) (⊤)
    PadicInt.Coe.ringHom ((Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a)
    (RatAlgebra.dividedPowers (⊤ : Ideal ℚ_[p])) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    simp only [Ideal.span_singleton_eq_top, isUnit_iff_ne_zero, ne_eq, cast_eq_zero]
    exact Nat.Prime.ne_zero hp.elim
  · intro n x hx
    exact ⟨⟨dpow' p n x, dpow'_int p n hx⟩, fun hn ↦ dpow'_mem p hn hx, by
      simp [dpow', inverse_eq_inv', Coe.ringHom_apply, RatAlgebra.dpow_apply,
        Submodule.mem_top, ↓reduceIte]⟩

open Function

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.dividedPowers_eq** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma dividedPowers_eq (n : ℕ) (x : ℤ_[p]) :
    (dividedPowers p).dpow n x = open scoped Classical in
      if hx : x ∈ Ideal.span {(p : ℤ_[p])} then ⟨dpow' p n x, dpow'_int p n hx⟩ else 0 := by
  simp only [dividedPowers, ofInjective]
  split_ifs with hx
  · have hinj : Injective (PadicInt.Coe.ringHom (p := p)) :=
      (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
    have heq : Coe.ringHom ⟨dpow' p n x, dpow'_int p n hx⟩ =
        inverse (n ! : ℚ_[p]) * Coe.ringHom x ^ n := by
      simp [dpow', inverse_eq_inv', Coe.ringHom_apply]
    simpa only [← hinj.eq_iff, (Exists.choose_spec (_ : ∃ a, ∃ _, Coe.ringHom a = _)).2,
      RatAlgebra.dpow_apply, Submodule.mem_top] using! heq.symm
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.coe_dpow_eq** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：coe_dpow_eq (n : Nat) (x : Int_[p]) : ((dividedPowers p).dpow n x : Rat_[p
]) = open scoped Classical in if _ : x in Ideal.span {(p : Int_[p])} then invers
e (n ! : Rat_[p]) * x ^ n else 0
参数：n : Nat；x : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.DividedPowers.Padic.0.PadicInt.dpow'_int`：∀ 
(p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) {x : ℤ_[p]}, x ∈ Ideal.span {↑p} → ‖Pa
dicInt.dpow'✝ p n ↑x‖ ≤ 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.RingTheory.DividedPowers.Padic.0.PadicInt.dividedPowers
_eq`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (x : ℤ_[p]),   (PadicInt.divide
dPowers p).dpow n x = if hx : x ∈ Ideal.span {↑p} then ⟨PadicInt.…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma coe_dpow_eq (n : ℕ) (x : ℤ_[p]) :
    ((dividedPowers p).dpow n x : ℚ_[p]) = open scoped Classical in
      if _ : x ∈ Ideal.span {(p : ℤ_[p])} then inverse (n ! : ℚ_[p]) * x ^ n else 0 := by
  simp only [dividedPowers_eq, dpow', inverse_eq_inv', dite_eq_ite]
  split_ifs <;> simp

end Padic

end PadicInt

