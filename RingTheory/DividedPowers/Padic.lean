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

/--
Definition of `DividedPowers.ofInjective` / `DividedPowers.ofInjective` 的定义

English:
definition DividedPowers.ofInjective
  signature: (f : A ->+* B) (hf : Injective f)
  body: open scoped Classical in if hx : x in I then Exists.choose (hmem n hx) else 0
  dpow_null hx := by simp [dif_neg hx]
  dpow_zero {x} hx := by
    simp only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (hmem 0 hx)).2, map_one]
    rw [hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hx)]
  dpow_one hx := 

中文:
定义 DividedPowers.ofInjective
  签名: (f : A ->+* B) (hf : 单射 f)
  定义体: open scoped Classical in if hx : x in I then Exists.choose (hmem n hx) else 0
  dpow_null hx := by simp [dif_neg hx]
  dpow_zero {x} hx := by
    simp only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (hmem 0 hx)).2, map_one]
    rw [hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hx)]
  dpow_one hx := 

Depends on / 依赖: Classical, Exists, Exists.choose, scoped
-/
noncomputable def DividedPowers.ofInjective (f : A ->+* B) (hf : Injective f)
    (hJ : DividedPowers J) (hIJ : I.map f = J)
    (hmem : forall (n : Nat) {x : A} (_ : x in I), exists (y : A) (_ : n != 0 -> y in I), f y = hJ.dpow n (f x)) :
    DividedPowers I where
  dpow n x := open scoped Classical in if hx : x in I then Exists.choose (hmem n hx) else 0
  dpow_null hx := by simp [dif_neg hx]
  dpow_zero {x} hx := by
    simp only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (hmem 0 hx)).2, map_one]
    rw [hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hx)]
  dpow_one hx := by
    simpa only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (_ : exists a, exists _, f a = _)).2]
      using hJ.dpow_one (hIJ ▸ Ideal.mem_map_of_mem f hx)
  dpow_mem {n x} hn hx := by simpa only [dif_pos hx] using (Exists.choose_spec (hmem n hx)).1 hn
  dpow_add {n x y} hx hy := by
    have hxy : x + y in I := Ideal.add_mem _ hx hy
    simpa only [dif_pos hxy, dif_pos hx, dif_pos hy, ← hf.eq_iff, map_sum, map_mul,
      (Exists.choose_spec (_ : exists a, exists _, f a = _)).2, map_add]
      using hJ.dpow_add (hIJ ▸ I.mem_map_of_mem f hx) (hIJ ▸ I.mem_map_of_mem f hy)
  dpow_mul {n a x} hx := by
    have hax : a * x in I := Ideal.mul_mem_left _ _ hx
    simpa only [(Exists.choose_spec (_ : exists a, exists _, f a = _)).2, dif_pos hax, dif_pos hx,
    ← hf.eq_iff, map_mul, map_pow] using hJ.dpow_mul (hIJ ▸ I.mem_map_of_mem f hx)
  mul_dpow hx := by simpa only [dif_pos hx, ← hf.eq_iff, (Exists.choose_spec (hmem _ hx)).2,
    map_mul, map_natCast] using hJ.mul_dpow (hIJ ▸ I.mem_map_of_mem f hx)
  dpow_comp {n m x} hm hx := by
    simp only [dif_pos hx, ← hf.eq_iff, map_mul, map_natCast]
    -- the condition for the other `dif_pos` is a bit messy so we use `rw` to
    -- spin it off into a separate branch
    rw [dif_pos]
    · simp only [(Exists.choose_spec (_ : exists a, exists _, f a = _)).2]
      exact hJ.dpow_comp hm (hIJ ▸ I.mem_map_of_mem f hx)
    · rw [dif_pos hx]
      exact (Exists.choose_spec (hmem m hx)).1 hm

end Injective

namespace PadicInt

section Padic

variable (p : Nat) [hp : Fact p.Prime]

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def dpow'
  body: fun m x => inverse (m ! : Rat_[p]) * x ^ m

中文:
定义 noncomputable
  签名: def dpow'
  定义体: fun m x => inverse (m ! : Rat_[p]) * x ^ m
-/
private noncomputable def dpow' : Nat -> Rat_[p] -> Rat_[p] := fun m x => inverse (m ! : Rat_[p]) * x ^ m

/--
lemma `dpow'_norm_le_of_ne_zero` / 引理 `dpow'_norm_le_of_ne_zero`

English:
lemma dpow'_norm_le_of_ne_zero
  statement: {n : Nat} (hn : n != 0) {x : Int_[p]}
  proof: by
  unfold dpow'
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [inverse_eq_inv', coe_zero, ne_eq, hn, not_false_eq_true, zero_pow, mul_zero,
      norm_zero, inv_nonneg, cast_nonneg]
  · have hlt : (padicValNat p n.factorial : Int) < n := by
      exact_mod_cast padicValNat_factorial_lt_of_ne_zero p

中文:
引理 dpow'_norm_le_of_ne_zero
  结论: {n : 自然数} (hn : n != 0) {x : 整数_[p]}
  证明: by
  unfold dpow'
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [inverse_eq_inv', coe_zero, ne_eq, hn, not_false_eq_true, zero_pow, mul_zero,
      norm_zero, inv_nonneg, cast_nonneg]
  · have hlt : (padicValNat p n.factorial : Int) < n := by
      exact_mod_cast padicValNat_factorial_lt_of_ne_zero p
-/
private lemma dpow'_norm_le_of_ne_zero {n : Nat} (hn : n != 0) {x : Int_[p]}
    (hx : x in Ideal.span {(p : Int_[p])}) : ‖dpow' p n x‖ <= (p : Real)⁻¹ := by
  unfold dpow'
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [inverse_eq_inv', coe_zero, ne_eq, hn, not_false_eq_true, zero_pow, mul_zero,
      norm_zero, inv_nonneg, cast_nonneg]
  · have hlt : (padicValNat p n.factorial : Int) < n := by
      exact_mod_cast padicValNat_factorial_lt_of_ne_zero p hn
    have hnorm : 0 < ‖(n ! : Rat_[p])‖ := by
      simp only [norm_pos_iff, ne_eq, cast_eq_zero]
      exact factorial_ne_zero n
    rw [← zpow_neg_one]; rw [← Nat.cast_one (R := Int)]; rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simp only [inverse_eq_inv', Padic.padicNormE.mul, norm_inv, _root_.norm_pow,
      padic_norm_e_of_padicInt, cast_one, Int.reduceNeg, neg_add_cancel, zpow_zero]
    rw [norm_eq_zpow_neg_valuation hx0]; rw [inv_mul_lt_one₀ hnorm]; rw [Padic.norm_eq_zpow_neg_valuation
      (cast_ne_zero.mpr n.factorial_ne_zero)]; rw [← zpow_natCast]; rw [← zpow_mul]
    gcongr
    · exact_mod_cast Nat.Prime.one_lt hp.elim
    · simp only [neg_mul, Padic.valuation_natCast, neg_lt_neg_iff]
      apply lt_of_lt_of_le hlt
      conv_lhs => rw [← one_mul (n : Int)]
      gcongr
      norm_cast
      rwa [← PadicInt.mem_span_pow_iff_le_valuation x hx0, pow_one]

set_option backward.privateInPublic true in
/--
lemma `dpow'_int` / 引理 `dpow'_int`

English:
lemma dpow'_int
  given: (n : Nat) {x : Int_[p]} (hx : x in Ideal.span {(p : Int_[p])})
  proof: by
  unfold dpow'
  by_cases hn : n = 0
  · simp [hn]
  · apply le_trans (dpow'_norm_le_of_ne_zero p hn hx)
    rw [← zpow_neg_one]; rw [← zpow_zero ↑p]
    gcongr
    · exact_mod_cast Nat.Prime.one_le hp.elim
    · norm_num

中文:
引理 dpow'_int
  条件: (n : 自然数) {x : 整数_[p]} (hx : x in 理想.span {(p : 整数_[p])})
  证明: by
  unfold dpow'
  by_cases hn : n = 0
  · simp [hn]
  · apply le_trans (dpow'_norm_le_of_ne_zero p hn hx)
    rw [← zpow_neg_one]; rw [← zpow_zero ↑p]
    gcongr
    · exact_mod_cast Nat.Prime.one_le hp.elim
    · norm_num
-/
private lemma dpow'_int (n : Nat) {x : Int_[p]} (hx : x in Ideal.span {(p : Int_[p])}) :
    ‖dpow' p n x‖ <= 1 := by
  unfold dpow'
  by_cases hn : n = 0
  · simp [hn]
  · apply le_trans (dpow'_norm_le_of_ne_zero p hn hx)
    rw [← zpow_neg_one]; rw [← zpow_zero ↑p]
    gcongr
    · exact_mod_cast Nat.Prime.one_le hp.elim
    · norm_num

set_option backward.privateInPublic true in
/--
theorem `dpow'_mem` / 定理 `dpow'_mem`

English:
theorem dpow'_mem
  given: {n : Nat} {x : Int_[p]} (hm : n != 0) (hx : x in Ideal.span {↑p})
  proof: by
  have hiff := PadicInt.norm_le_pow_iff_mem_span_pow ⟨dpow' p n x, dpow'_int p n hx⟩ 1
  rw [pow_one] at hiff
  rw [← hiff]
  simp only [cast_one, zpow_neg_one]
  exact dpow'_norm_le_of_ne_zero p hm hx

中文:
定理 dpow'_mem
  条件: {n : 自然数} {x : 整数_[p]} (hm : n != 0) (hx : x in 理想.span {↑p})
  证明: by
  have hiff := PadicInt.norm_le_pow_iff_mem_span_pow ⟨dpow' p n x, dpow'_int p n hx⟩ 1
  rw [pow_one] at hiff
  rw [← hiff]
  simp only [cast_one, zpow_neg_one]
  exact dpow'_norm_le_of_ne_zero p hm hx
-/
private theorem dpow'_mem {n : Nat} {x : Int_[p]} (hm : n != 0) (hx : x in Ideal.span {↑p}) :
    ⟨dpow' p n x, dpow'_int p n hx⟩ in Ideal.span {(p : Int_[p])} := by
  have hiff := PadicInt.norm_le_pow_iff_mem_span_pow ⟨dpow' p n x, dpow'_int p n hx⟩ 1
  rw [pow_one] at hiff
  rw [← hiff]
  simp only [cast_one, zpow_neg_one]
  exact dpow'_norm_le_of_ne_zero p hm hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `dividedPowers` / `dividedPowers` 的定义

English:
definition dividedPowers
  signature: : DividedPowers (Ideal.span {(p : Int_[p])})
  body: by
  classical
  refine ofInjective (Ideal.span {(p : Int_[p])}) (⊤)
    PadicInt.Coe.ringHom ((Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a)
    (RatAlgebra.dividedPowers (⊤ : Ideal Rat_[p])) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    simp only [Ideal.s

中文:
定义 dividedPowers
  签名: : DividedPowers (理想.span {(p : 整数_[p])})
  定义体: by
  classical
  refine ofInjective (Ideal.span {(p : Int_[p])}) (⊤)
    PadicInt.Coe.ringHom ((Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a)
    (RatAlgebra.dividedPowers (⊤ : Ideal Rat_[p])) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    simp only [Ideal.s

Depends on / 依赖: Coe.ri, Ideal.map_span, Ideal.span, Ideal.span_singleton_eq_top, Int_, Nat.Prime.ne_zero, PadicInt, PadicInt.Coe.ringHom, RatAlgebra, RatAlgebra.dividedPowers, Rat_, Set.image_singleton, Set.injective_codRestrict, Subtype, Subtype.property, _int, _mem, cast_eq_zero, classical, dividedPowers
-/
noncomputable def dividedPowers : DividedPowers (Ideal.span {(p : Int_[p])}) := by
  classical
  refine ofInjective (Ideal.span {(p : Int_[p])}) (⊤)
    PadicInt.Coe.ringHom ((Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a)
    (RatAlgebra.dividedPowers (⊤ : Ideal Rat_[p])) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    simp only [Ideal.span_singleton_eq_top, isUnit_iff_ne_zero, ne_eq, cast_eq_zero]
    exact Nat.Prime.ne_zero hp.elim
  · intro n x hx
    exact ⟨⟨dpow' p n x, dpow'_int p n hx⟩, fun hn => dpow'_mem p hn hx, by
      simp [dpow', inverse_eq_inv', Coe.ringHom_apply, RatAlgebra.dpow_apply,
        Submodule.mem_top, ↓reduceIte]⟩

open Function

set_option backward.isDefEq.respectTransparency false in
/--
lemma `dividedPowers_eq` / 引理 `dividedPowers_eq`

English:
lemma dividedPowers_eq
  given: (n : Nat) (x : Int_[p])
  proof: by
  simp only [dividedPowers, ofInjective]
  split_ifs with hx
  · have hinj : Injective (PadicInt.Coe.ringHom (p := p)) :=
      (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a
    have heq : Coe.ringHom ⟨dpow' p n x, dpow'_int p n hx⟩ =
        inverse (n ! : Rat_[p]) * Coe.rin

中文:
引理 dividedPowers_eq
  条件: (n : 自然数) (x : 整数_[p])
  证明: by
  simp only [dividedPowers, ofInjective]
  split_ifs with hx
  · have hinj : Injective (PadicInt.Coe.ringHom (p := p)) :=
      (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a
    have heq : Coe.ringHom ⟨dpow' p n x, dpow'_int p n hx⟩ =
        inverse (n ! : Rat_[p]) * Coe.rin
-/
private lemma dividedPowers_eq (n : Nat) (x : Int_[p]) :
    (dividedPowers p).dpow n x = open scoped Classical in
      if hx : x in Ideal.span {(p : Int_[p])} then ⟨dpow' p n x, dpow'_int p n hx⟩ else 0 := by
  simp only [dividedPowers, ofInjective]
  split_ifs with hx
  · have hinj : Injective (PadicInt.Coe.ringHom (p := p)) :=
      (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a
    have heq : Coe.ringHom ⟨dpow' p n x, dpow'_int p n hx⟩ =
        inverse (n ! : Rat_[p]) * Coe.ringHom x ^ n := by
      simp [dpow', inverse_eq_inv', Coe.ringHom_apply]
    simpa only [← hinj.eq_iff, (Exists.choose_spec (_ : exists a, exists _, Coe.ringHom a = _)).2,
      RatAlgebra.dpow_apply, Submodule.mem_top] using! heq.symm
  · rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coe_dpow_eq` / 引理 `coe_dpow_eq`

English:
lemma coe_dpow_eq
  given: (n : Nat) (x : Int_[p])
  proof: by
  simp only [dividedPowers_eq, dpow', inverse_eq_inv', dite_eq_ite]
  split_ifs <;> simp

中文:
引理 coe_dpow_eq
  条件: (n : 自然数) (x : 整数_[p])
  证明: by
  simp only [dividedPowers_eq, dpow', inverse_eq_inv', dite_eq_ite]
  split_ifs <;> simp

Depends on / 依赖: dite_eq_ite, dividedPowers_eq, inverse_eq_inv, split_ifs
-/
lemma coe_dpow_eq (n : Nat) (x : Int_[p]) :
    ((dividedPowers p).dpow n x : Rat_[p]) = open scoped Classical in
      if _ : x in Ideal.span {(p : Int_[p])} then inverse (n ! : Rat_[p]) * x ^ n else 0 := by
  simp only [dividedPowers_eq, dpow', inverse_eq_inv', dite_eq_ite]
  split_ifs <;> simp

end Padic

end PadicInt
