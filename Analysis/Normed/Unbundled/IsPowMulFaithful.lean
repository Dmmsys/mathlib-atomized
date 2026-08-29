/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Equivalent power-multiplicative norms

In this file, we prove [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert]: if `R` is a normed
commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra norms on `S`, then if
`f₁` and `f₂` are equivalent on every subring `R[y]` for `y : S`, it follows that `f₁ = f₂`.

## Main Results
* `eq_of_powMul_faithful` : the proof of [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

norm, equivalent, power-multiplicative
-/

public section

open Filter Real Algebra
open scoped Topology

/--
theorem `contraction_of_isPowMul_of_boundedWrt` / 定理 `contraction_of_isPowMul_of_boundedWrt`

English:
theorem contraction_of_isPowMul_of_boundedWrt
  statement: {F : Type*} {α : outParam (Type*)} [Ring α]
  proof: by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Tendsto (fun n : Nat => C ^ (1 / (n : Real)) * nα x) atTop (𝓝 (nα x)) := by
    nth_rewrite 2 [← one_mul (nα x)]
    exact ((rpow_zero C ▸ ContinuousAt.tendsto (continuousAt_const_rpow (ne_of_gt hC0))).comp
      (tendsto_const_div_atTop_nhds_zero_nat 1))

中文:
定理 contraction_of_isPowMul_of_boundedWrt
  结论: {F : 类型} {α : outParam (类型)} [Ring α]
  证明: by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Tendsto (fun n : Nat => C ^ (1 / (n : Real)) * nα x) atTop (𝓝 (nα x)) := by
    nth_rewrite 2 [← one_mul (nα x)]
    exact ((rpow_zero C ▸ ContinuousAt.tendsto (continuousAt_const_rpow (ne_of_gt hC0))).comp
      (tendsto_const_div_atTop_nhds_zero_nat 1))

Depends on / 依赖: ContinuousAt, ContinuousAt.tendsto, Nat.cast_ne_zero.mpr, Tendsto, cast_ne_zero, continuousAt_const_rpow, eventually_atTop, ge_of_tendsto, ne_of_gt, nth_rewrite, one_mul, rpow_nat, rpow_zero, tendsto, tendsto_const_div_atTop_nhds_zero_nat, tendsto_const_nhds
-/
theorem contraction_of_isPowMul_of_boundedWrt {F : Type*} {α : outParam (Type*)} [Ring α]
    [FunLike F α Real] [RingSeminormClass F α Real] {β : Type*} [Ring β] (nα : F) {nβ : β -> Real}
    (hβ : IsPowMul nβ) {f : α ->+* β} (hf : f.IsBoundedWrt nα nβ) (x : α) : nβ (f x) <= nα x := by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Tendsto (fun n : Nat => C ^ (1 / (n : Real)) * nα x) atTop (𝓝 (nα x)) := by
    nth_rewrite 2 [← one_mul (nα x)]
    exact ((rpow_zero C ▸ ContinuousAt.tendsto (continuousAt_const_rpow (ne_of_gt hC0))).comp
      (tendsto_const_div_atTop_nhds_zero_nat 1)).mul tendsto_const_nhds
  apply ge_of_tendsto hlim
  simp only [eventually_atTop]
  use 1
  intro n hn
  have h : (C ^ (1 / n : Real)) ^ n = C := by
    have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    rw [← rpow_natCast]; rw [← rpow_mul hC0.le]; rw [one_div]; rw [inv_mul_cancel₀ hn0]; rw [rpow_one]
  apply le_of_pow_le_pow_left₀ (ne_of_gt hn) (by positivity)
  · rw [mul_pow, h, ← hβ _ hn, ← map_pow]
    apply le_trans (hC (x ^ n))
    rw [mul_le_mul_iff_right₀ hC0]
    exact map_pow_le_pow _ _ (Nat.one_le_iff_ne_zero.mp hn)

/--
theorem `contraction_of_isPowMul` / 定理 `contraction_of_isPowMul`

English:
theorem contraction_of_isPowMul
  statement: {α β : Type*} [SeminormedRing α] [SeminormedRing β]
  proof: contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm α) hβ hf x

中文:
定理 contraction_of_isPowMul
  结论: {α β : 类型} [SeminormedRing α] [SeminormedRing β]
  证明: contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm α) hβ hf x

Depends on / 依赖: SeminormedRing, SeminormedRing.toRingSeminorm, contraction_of_isPowMul_of_boundedWrt, toRingSeminorm
-/
theorem contraction_of_isPowMul {α β : Type*} [SeminormedRing α] [SeminormedRing β]
    (hβ : IsPowMul (norm : β -> Real)) {f : α ->+* β} (hf : f.IsBounded) (x : α) : norm (f x) <= norm x :=
  contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm α) hβ hf x

/--
theorem `eq_seminorms` / 定理 `eq_seminorms`

English:
theorem eq_seminorms
  statement: {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α Real]
  proof: by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff DFunLike.coe_injective]
  ext x
  exact le_antisymm (contraction_of

中文:
定理 eq_seminorms
  结论: {F : 类型} {α : outParam (类型)} [Ring α] [FunLike F α 实数]
  证明: by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff DFunLike.coe_injective]
  ext x
  exact le_antisymm (contraction_of

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.Injective.eq_iff, Injective, IsBoundedWrt, RingHom, RingHom.IsBoundedWrt, RingHom.id, coe_injective, contraction_of_isPowMul_of_boundedWrt, eq_iff, le_antisymm
-/
theorem eq_seminorms {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α Real]
    [RingSeminormClass F α Real] {f g : F} (hfpm : IsPowMul f) (hgpm : IsPowMul g)
    (hfg : exists (r : Real) (_ : 0 < r), forall a : α, f a <= r * g a)
    (hgf : exists (r : Real) (_ : 0 < r), forall a : α, g a <= r * f a) : f = g := by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff DFunLike.coe_injective]
  ext x
  exact le_antisymm (contraction_of_isPowMul_of_boundedWrt g hfpm hge x)
    (contraction_of_isPowMul_of_boundedWrt f hgpm hle x)

variable {R S : Type*} [NormedCommRing R] [CommRing S] [Algebra R S]

/--
theorem `eq_of_powMul_faithful` / 定理 `eq_of_powMul_faithful`

English:
theorem eq_of_powMul_faithful
  statement: (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S)
  proof: by
  ext x
  set g₁ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₁
  set g₂ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₂
  have hg₁_pm : IsPowMul g₁ := IsPowMul.restriction _ hf₁_pm
  have hg₂_pm : IsPowMul g₂ := IsPowMul.restriction _ hf₂_pm
  let y : R[(x : S)] := ⟨x, sel

中文:
定理 eq_of_powMul_faithful
  结论: (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S)
  证明: by
  ext x
  set g₁ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₁
  set g₂ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₂
  have hg₁_pm : IsPowMul g₁ := IsPowMul.restriction _ hf₁_pm
  have hg₂_pm : IsPowMul g₂ := IsPowMul.restriction _ hf₂_pm
  let y : R[(x : S)] := ⟨x, sel

Depends on / 依赖: AlgebraNorm, AlgebraNorm.restriction, IsPowMul, IsPowMul.restriction, forall_and, forall_and.mp, h_eq, restriction, self_mem_adjoin_singleton, y.val
-/
theorem eq_of_powMul_faithful (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S)
    (hf₂_pm : IsPowMul f₂)
    (h_eq : forall y : S, exists (C₁ C₂ : Real) (_ : 0 < C₁) (_ : 0 < C₂),
      forall x : R[y], f₁ x.val <= C₁ * f₂ x.val ∧ f₂ x.val <= C₂ * f₁ x.val) :
    f₁ = f₂ := by
  ext x
  set g₁ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₁
  set g₂ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₂
  have hg₁_pm : IsPowMul g₁ := IsPowMul.restriction _ hf₁_pm
  have hg₂_pm : IsPowMul g₂ := IsPowMul.restriction _ hf₂_pm
  let y : R[(x : S)] := ⟨x, self_mem_adjoin_singleton R x⟩
  have hy : x = y.val := rfl
  have h1 : f₁ y.val = g₁ y := rfl
  have h2 : f₂ y.val = g₂ y := rfl
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hC⟩ := h_eq x
  obtain ⟨hC₁, hC₂⟩ := forall_and.mp hC
  rw [hy]; rw [h1]; rw [h2]; rw [eq_seminorms hg₁_pm hg₂_pm ⟨C₁]; rw [hC₁_pos]; rw [hC₁⟩ ⟨C₂]; rw [hC₂_pos]; rw [hC₂⟩]
