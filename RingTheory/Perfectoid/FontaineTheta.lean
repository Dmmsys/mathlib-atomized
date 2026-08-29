/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Fontaine's θ map

In this file, we define Fontaine's `θ` map, which is a ring
homomorphism from the Witt vector `𝕎 R♭` of the tilt of a perfectoid ring `R`
to `R` itself. Our definition of `θ` does not require that `R` is perfectoid in the first place.
We only need `R` to be `p`-adically complete.

## Main Definitions
* `fontaineTheta` : Fontaine's θ map, which is a ring homomorphism from `𝕎 R♭` to `R`.

## Main Theorems
* `fontaineTheta_teichmuller` : `θ([x])` is the untilt of `x`.
* `fontaineTheta_surjective` : Fontaine's θ map is surjective.

## TODO
Establish that our definition (explicit construction of `θ mod p ^ n`) agrees with the
deformation-theoretic approach via the cotangent complex, as in
[Bhatt, *Lecture notes for a class on perfectoid spaces*.
Remark 6.1.7](https://www.math.ias.edu/~bhatt/teaching/mat679w17/lectures.pdf).

## Tags
Fontaine's theta map, perfectoid theory, p-adic Hodge theory

## Reference

* [Fontaine, *Sur Certains Types de Représentations p-Adiques du Groupe de Galois d'un Corps Local;
  Construction d'un Anneau de Barsotti-Tate*][fontaine1982certains]
* [Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps]

-/

@[expose] public section

universe u

open Ideal Quotient PreTilt WittVector

noncomputable section

variable {R : Type u} [CommRing R] {p : Nat} [Fact p.Prime]

local notation "𝕎 " A:100 => WittVector p A
local notation A "♭" => PreTilt A p
local notation3 "𝔭" => span {(p : R)}

namespace WittVector


/--
theorem `ker_map_le_ker_mk_comp_ghostComponent` / 定理 `ker_map_le_ker_mk_comp_ghostComponent`

English:
theorem ker_map_le_ker_mk_comp_ghostComponent
  given: (n : Nat)
  proof: by
  intro x
  simp only [RingHom.mem_ker, map_eq_zero_iff, RingHom.comp_apply]
  intro h
  simp only [ghostComponent]
  apply_fun Ideal.quotEquivOfEq (Ideal.span_singleton_pow _ (n + 1))
  simp only [RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply, ghostMap_apply,
    quotEquivOfEq_mk, 

中文:
定理 ker_map_le_ker_mk_comp_ghostComponent
  条件: (n : 自然数)
  证明: by
  intro x
  simp only [RingHom.mem_ker, map_eq_zero_iff, RingHom.comp_apply]
  intro h
  simp only [ghostComponent]
  apply_fun Ideal.quotEquivOfEq (Ideal.span_singleton_pow _ (n + 1))
  simp only [RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply, ghostMap_apply,
    quotEquivOfEq_mk, 

Depends on / 依赖: Function, Function.comp_apply, Ideal.quotEquivOfEq, Ideal.span_singleton_pow, Pi.evalRingHom_apply, RingHom, RingHom.coe_comp, RingHom.comp_apply, RingHom.mem_ker, apply_fun, coe_comp, comp_apply, eq_zero_iff_dvd, evalRingHom_apply, ghostComponent, ghostMap_apply, map_eq_zero_iff, map_zero, mem_ker, pow_dvd_ghostComponent_of_dvd_coeff
-/
theorem ker_map_le_ker_mk_comp_ghostComponent (n : Nat) :
    RingHom.ker (WittVector.map (Ideal.Quotient.mk 𝔭)) <=
    RingHom.ker (((Ideal.Quotient.mk (𝔭 ^ (n + 1)))).comp
    (WittVector.ghostComponent (p := p) n)) := by
  intro x
  simp only [RingHom.mem_ker, map_eq_zero_iff, RingHom.comp_apply]
  intro h
  simp only [ghostComponent]
  apply_fun Ideal.quotEquivOfEq (Ideal.span_singleton_pow _ (n + 1))
  simp only [RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply, ghostMap_apply,
    quotEquivOfEq_mk, map_zero]
  simp only [eq_zero_iff_dvd] at h ⊢
  exact pow_dvd_ghostComponent_of_dvd_coeff (fun _ _ => h _)

/--
Definition of `ghostComponentModPPow` / `ghostComponentModPPow` 的定义

English:
definition ghostComponentModPPow
  signature: (n : Nat)
  body: RingHom.liftOfSurjective (WittVector.map (Ideal.Quotient.mk 𝔭))
    (map_surjective _ Ideal.Quotient.mk_surjective) ⟨((Ideal.Quotient.mk (𝔭 ^ (n + 1)))).comp
      (WittVector.ghostComponent n), ker_map_le_ker_mk_comp_ghostComponent n⟩

@[simp]

中文:
定义 ghostComponentModPPow
  签名: (n : 自然数)
  定义体: RingHom.liftOfSurjective (WittVector.map (Ideal.Quotient.mk 𝔭))
    (map_surjective _ Ideal.Quotient.mk_surjective) ⟨((Ideal.Quotient.mk (𝔭 ^ (n + 1)))).comp
      (WittVector.ghostComponent n), ker_map_le_ker_mk_comp_ghostComponent n⟩

@[simp]

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.liftOfSurjective, WittVector, WittVector.ghostComponent, WittVector.map, ghostComponent, ker_map_le_ker_mk_comp_ghostComponent, liftOfSurjective, map_surjective, mk_surjective
-/
def ghostComponentModPPow (n : Nat) : 𝕎 (R ⧸ 𝔭) ->+* R ⧸ 𝔭 ^ (n + 1) :=
  RingHom.liftOfSurjective (WittVector.map (Ideal.Quotient.mk 𝔭))
    (map_surjective _ Ideal.Quotient.mk_surjective) ⟨((Ideal.Quotient.mk (𝔭 ^ (n + 1)))).comp
      (WittVector.ghostComponent n), ker_map_le_ker_mk_comp_ghostComponent n⟩

@[simp]
/--
theorem `ghostComponentModPPow_map_mk` / 定理 `ghostComponentModPPow_map_mk`

English:
theorem ghostComponentModPPow_map_mk
  given: (n : Nat) (x : 𝕎 R)
  proof: RingHom.liftOfSurjective_comp_apply ..

@[simp]

中文:
定理 ghostComponentModPPow_map_mk
  条件: (n : 自然数) (x : 𝕎 R)
  证明: RingHom.liftOfSurjective_comp_apply ..

@[simp]

Depends on / 依赖: RingHom, RingHom.liftOfSurjective_comp_apply, liftOfSurjective_comp_apply
-/
theorem ghostComponentModPPow_map_mk (n : Nat) (x : 𝕎 R) :
    ghostComponentModPPow n (WittVector.map (Ideal.Quotient.mk 𝔭) x) =
    WittVector.ghostComponent n x :=
  RingHom.liftOfSurjective_comp_apply ..

@[simp]
/--
theorem `quotEquivOfEq_ghostComponentModPPow` / 定理 `quotEquivOfEq_ghostComponentModPPow`

English:
theorem quotEquivOfEq_ghostComponentModPPow
  given: (x : 𝕎 (R ⧸ 𝔭)) (h : 𝔭 ^ (0 + 1) = 𝔭)
  proof: by
  obtain ⟨y, hy⟩ := map_surjective _ Ideal.Quotient.mk_surjective x
  simp [← hy, ghostComponent_apply]

中文:
定理 quotEquivOfEq_ghostComponentModPPow
  条件: (x : 𝕎 (R ⧸ 𝔭)) (h : 𝔭 ^ (0 + 1) = 𝔭)
  证明: by
  obtain ⟨y, hy⟩ := map_surjective _ Ideal.Quotient.mk_surjective x
  simp [← hy, ghostComponent_apply]

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, ghostComponent_apply, map_surjective, mk_surjective
-/
theorem quotEquivOfEq_ghostComponentModPPow (x : 𝕎 (R ⧸ 𝔭)) (h : 𝔭 ^ (0 + 1) = 𝔭) :
    quotEquivOfEq h (ghostComponentModPPow 0 x) = ghostComponent 0 x := by
  obtain ⟨y, hy⟩ := map_surjective _ Ideal.Quotient.mk_surjective x
  simp [← hy, ghostComponent_apply]

variable [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
-- local notation 𝔭 does not work in [IsAdicComplete (span {(p : R)}) R]

@[simp]
/--
theorem `ghostComponentModPPow_teichmuller_coeff` / 定理 `ghostComponentModPPow_teichmuller_coeff`

English:
theorem ghostComponentModPPow_teichmuller_coeff
  given: (n : Nat) (x : R♭)
  proof: by
  simpa using ghostComponentModPPow_map_mk n
    (teichmuller p ((((_root_.frobeniusEquiv _ p).symm ^ n) x).untilt))

中文:
定理 ghostComponentModPPow_teichmuller_coeff
  条件: (n : 自然数) (x : R♭)
  证明: by
  simpa using ghostComponentModPPow_map_mk n
    (teichmuller p ((((_root_.frobeniusEquiv _ p).symm ^ n) x).untilt))

Depends on / 依赖: _root_, _root_.frobeniusEquiv, frobeniusEquiv, ghostComponentModPPow_map_mk, teichmuller, untilt
-/
theorem ghostComponentModPPow_teichmuller_coeff (n : Nat) (x : R♭) :
    ghostComponentModPPow n (teichmuller p (PreTilt.coeff n x)) =
    Ideal.Quotient.mk (𝔭 ^ (n + 1)) x.untilt := by
  simpa using ghostComponentModPPow_map_mk n
    (teichmuller p ((((_root_.frobeniusEquiv _ p).symm ^ n) x).untilt))

variable (R p) in
/--
Definition of `fontaineThetaModPPow` / `fontaineThetaModPPow` 的定义

English:
definition fontaineThetaModPPow
  signature: (n : Nat)
  body: (ghostComponentModPPow n).comp (((WittVector.map (PreTilt.coeff 0))).comp
    (WittVector.map ((_root_.frobeniusEquiv (R♭) p).symm ^ n : R♭ ->+* R♭)))

@[simp]

中文:
定义 fontaineThetaModPPow
  签名: (n : 自然数)
  定义体: (ghostComponentModPPow n).comp (((WittVector.map (PreTilt.coeff 0))).comp
    (WittVector.map ((_root_.frobeniusEquiv (R♭) p).symm ^ n : R♭ ->+* R♭)))

@[simp]

Depends on / 依赖: PreTilt, PreTilt.coeff, WittVector, WittVector.map, _root_, _root_.frobeniusEquiv, frobeniusEquiv, ghostComponentModPPow
-/
def fontaineThetaModPPow (n : Nat) : 𝕎 R♭ ->+* R ⧸ 𝔭 ^ (n + 1) :=
  (ghostComponentModPPow n).comp (((WittVector.map (PreTilt.coeff 0))).comp
    (WittVector.map ((_root_.frobeniusEquiv (R♭) p).symm ^ n : R♭ ->+* R♭)))

@[simp]
/--
theorem `fontaineThetaModPPow_teichmuller` / 定理 `fontaineThetaModPPow_teichmuller`

English:
theorem fontaineThetaModPPow_teichmuller
  given: (n : Nat) (x : R♭)
  proof: by
  simp [fontaineThetaModPPow]

中文:
定理 fontaineThetaModPPow_teichmuller
  条件: (n : 自然数) (x : R♭)
  证明: by
  simp [fontaineThetaModPPow]

Depends on / 依赖: fontaineThetaModPPow
-/
theorem fontaineThetaModPPow_teichmuller (n : Nat) (x : R♭) :
    fontaineThetaModPPow R p n (teichmuller p x) = Ideal.Quotient.mk _ x.untilt := by
  simp [fontaineThetaModPPow]

/--
theorem `factorPowSucc_comp_fontaineThetaModPPow` / 定理 `factorPowSucc_comp_fontaineThetaModPPow`

English:
theorem factorPowSucc_comp_fontaineThetaModPPow
  given: (n : Nat)
  proof: by
  apply eq_of_apply_teichmuller_eq ((factorPowSucc _ _).comp (fontaineThetaModPPow R p (n + 1)))
    (fontaineThetaModPPow R p n)
  · use n + 1
    have : p = Ideal.Quotient.mk (𝔭 ^ (n + 1)) p := by
      simp [map_natCast]
    rw [this]; rw [← map_pow]; rw [Ideal.Quotient.eq_zero_iff_mem]
    ex

中文:
定理 factorPowSucc_comp_fontaineThetaModPPow
  条件: (n : 自然数)
  证明: by
  apply eq_of_apply_teichmuller_eq ((factorPowSucc _ _).comp (fontaineThetaModPPow R p (n + 1)))
    (fontaineThetaModPPow R p n)
  · use n + 1
    have : p = Ideal.Quotient.mk (𝔭 ^ (n + 1)) p := by
      simp [map_natCast]
    rw [this]; rw [← map_pow]; rw [Ideal.Quotient.eq_zero_iff_mem]
    ex

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, Ideal.pow_mem_pow, Quotient, eq_of_apply_teichmuller_eq, eq_zero_iff_mem, factorPowSucc, fontaineThetaModPPow, map_natCast, map_pow, mem_span_singleton_self, pow_mem_pow
-/
theorem factorPowSucc_comp_fontaineThetaModPPow (n : Nat) :
    (factorPowSucc _ _).comp (fontaineThetaModPPow R p (n + 1)) = fontaineThetaModPPow R p n := by
  apply eq_of_apply_teichmuller_eq ((factorPowSucc _ _).comp (fontaineThetaModPPow R p (n + 1)))
    (fontaineThetaModPPow R p n)
  · use n + 1
    have : p = Ideal.Quotient.mk (𝔭 ^ (n + 1)) p := by
      simp [map_natCast]
    rw [this]; rw [← map_pow]; rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (mem_span_singleton_self _) _
  simp [fontaineThetaModPPow]

/--
theorem `factorPowSucc_fontaineThetaModPPow_eq` / 定理 `factorPowSucc_fontaineThetaModPPow_eq`

English:
theorem factorPowSucc_fontaineThetaModPPow_eq
  given: (n : Nat) (x : 𝕎 R♭)
  proof: by
  simp [← factorPowSucc_comp_fontaineThetaModPPow n]

中文:
定理 factorPowSucc_fontaineThetaModPPow_eq
  条件: (n : 自然数) (x : 𝕎 R♭)
  证明: by
  simp [← factorPowSucc_comp_fontaineThetaModPPow n]

Depends on / 依赖: factorPowSucc_comp_fontaineThetaModPPow
-/
theorem factorPowSucc_fontaineThetaModPPow_eq (n : Nat) (x : 𝕎 R♭) :
    factorPowSucc _ _ ((fontaineThetaModPPow R p (n + 1)) x) = fontaineThetaModPPow R p n x := by
  simp [← factorPowSucc_comp_fontaineThetaModPPow n]

open IsAdicComplete

variable (R p) in
/--
Definition of `fontaineTheta` / `fontaineTheta` 的定义

English:
definition fontaineTheta
  signature: : 𝕎 R♭ ->+* R
  body: Order.succ_strictMono.liftRingHom 𝔭 _ (factorPowSucc_comp_fontaineThetaModPPow _)

中文:
定义 fontaineTheta
  签名: : 𝕎 R♭ ->+* R
  定义体: Order.succ_strictMono.liftRingHom 𝔭 _ (factorPowSucc_comp_fontaineThetaModPPow _)

Depends on / 依赖: Order.succ_strictMono.liftRingHom, factorPowSucc_comp_fontaineThetaModPPow, liftRingHom, succ_strictMono
-/
def fontaineTheta : 𝕎 R♭ ->+* R :=
  Order.succ_strictMono.liftRingHom 𝔭 _ (factorPowSucc_comp_fontaineThetaModPPow _)

/--
theorem `mk_pow_fontaineTheta` / 定理 `mk_pow_fontaineTheta`

English:
theorem mk_pow_fontaineTheta
  given: (n : Nat) (x : 𝕎 R♭)
  proof: Order.succ_strictMono.mk_liftRingHom 𝔭 _ (factorPowSucc_comp_fontaineThetaModPPow _) x

中文:
定理 mk_pow_fontaineTheta
  条件: (n : 自然数) (x : 𝕎 R♭)
  证明: Order.succ_strictMono.mk_liftRingHom 𝔭 _ (factorPowSucc_comp_fontaineThetaModPPow _) x

Depends on / 依赖: Order.succ_strictMono.mk_liftRingHom, factorPowSucc_comp_fontaineThetaModPPow, mk_liftRingHom, succ_strictMono
-/
theorem mk_pow_fontaineTheta (n : Nat) (x : 𝕎 R♭) :
    Ideal.Quotient.mk (𝔭 ^ (n + 1)) (fontaineTheta R p x) = fontaineThetaModPPow R p n x :=
  Order.succ_strictMono.mk_liftRingHom 𝔭 _ (factorPowSucc_comp_fontaineThetaModPPow _) x

/--
theorem `mk_fontaineTheta` / 定理 `mk_fontaineTheta`

English:
theorem mk_fontaineTheta
  given: (x : 𝕎 R♭)
  proof: by
  have := mk_pow_fontaineTheta 0 x
  simp only [Nat.reduceAdd] at this
  apply_fun Ideal.quotEquivOfEq (pow_one (p : R) ▸ Ideal.span_singleton_pow (p : R) 1) at this
  simp only [quotEquivOfEq_mk] at this
  rw [this]
  simp [fontaineThetaModPPow, ghostComponent_apply, RingHom.one_def]

@[simp]

中文:
定理 mk_fontaineTheta
  条件: (x : 𝕎 R♭)
  证明: by
  have := mk_pow_fontaineTheta 0 x
  simp only [Nat.reduceAdd] at this
  apply_fun Ideal.quotEquivOfEq (pow_one (p : R) ▸ Ideal.span_singleton_pow (p : R) 1) at this
  simp only [quotEquivOfEq_mk] at this
  rw [this]
  simp [fontaineThetaModPPow, ghostComponent_apply, RingHom.one_def]

@[simp]

Depends on / 依赖: Ideal.quotEquivOfEq, Ideal.span_singleton_pow, Nat.reduceAdd, RingHom, RingHom.one_def, apply_fun, fontaineThetaModPPow, ghostComponent_apply, mk_pow_fontaineTheta, one_def, pow_one, quotEquivOfEq, quotEquivOfEq_mk, reduceAdd, span_singleton_pow
-/
theorem mk_fontaineTheta (x : 𝕎 R♭) :
    Ideal.Quotient.mk 𝔭 (fontaineTheta R p x) = PreTilt.coeff 0 (x.coeff 0) := by
  have := mk_pow_fontaineTheta 0 x
  simp only [Nat.reduceAdd] at this
  apply_fun Ideal.quotEquivOfEq (pow_one (p : R) ▸ Ideal.span_singleton_pow (p : R) 1) at this
  simp only [quotEquivOfEq_mk] at this
  rw [this]
  simp [fontaineThetaModPPow, ghostComponent_apply, RingHom.one_def]

@[simp]
/--
theorem `fontaineTheta_teichmuller` / 定理 `fontaineTheta_teichmuller`

English:
theorem fontaineTheta_teichmuller
  given: (x : R♭)
  statement: fontaineTheta R p (teichmuller p x) = x.untilt
  proof: by
  rw [IsHausdorff.eq_iff_smodEq (I := 𝔭)]
  simp only [smul_eq_mul, mul_top]
  intro n
  cases n
  · simp
  · simp [SModEq, mk_pow_fontaineTheta]

中文:
定理 fontaineTheta_teichmuller
  条件: (x : R♭)
  结论: fontaineTheta R p (teichmuller p x) = x.untilt
  证明: by
  rw [IsHausdorff.eq_iff_smodEq (I := 𝔭)]
  simp only [smul_eq_mul, mul_top]
  intro n
  cases n
  · simp
  · simp [SModEq, mk_pow_fontaineTheta]

Depends on / 依赖: IsHausdorff, IsHausdorff.eq_iff_smodEq, SModEq, eq_iff_smodEq, mk_pow_fontaineTheta, mul_top, smul_eq_mul
-/
theorem fontaineTheta_teichmuller (x : R♭) : fontaineTheta R p (teichmuller p x) = x.untilt := by
  rw [IsHausdorff.eq_iff_smodEq (I := 𝔭)]
  simp only [smul_eq_mul, mul_top]
  intro n
  cases n
  · simp
  · simp [SModEq, mk_pow_fontaineTheta]

end WittVector

variable [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

/--
theorem `surjective_fontaineTheta` / 定理 `surjective_fontaineTheta`

English:
theorem surjective_fontaineTheta
  given: (hF : Function.Surjective (frobenius (ModP R p) p))
  proof: by
  have : Ideal.map (fontaineTheta R p) (span {(p : 𝕎 R♭)}) = 𝔭 := by
    simp [map_span]
  have _ : IsHausdorff ((span {(p : 𝕎 R♭)}).map (fontaineTheta R p)) R := by
    rw [this]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (fontaineTheta R p) (I := span {(p : 𝕎 R♭)})
  simp o

中文:
定理 surjective_fontaineTheta
  条件: (hF : 函数.满射 (frobenius (ModP R p) p))
  证明: by
  have : Ideal.map (fontaineTheta R p) (span {(p : 𝕎 R♭)}) = 𝔭 := by
    simp [map_span]
  have _ : IsHausdorff ((span {(p : 𝕎 R♭)}).map (fontaineTheta R p)) R := by
    rw [this]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (fontaineTheta R p) (I := span {(p : 𝕎 R♭)})
  simp o

Depends on / 依赖: Function, Function.Surjective, Ideal.Quotient.mk, Ideal.map, Ideal.map_span, IsHausdorff, Quotient, RingHom, RingHom.coe_comp, Set.image_singleton, Surjective, coe_comp, fontaineTheta, image_singleton, infer_instance, map_natCast, map_span, surjective_of_mk_map_comp_surjective
-/
theorem surjective_fontaineTheta (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (fontaineTheta R p) := by
  have : Ideal.map (fontaineTheta R p) (span {(p : 𝕎 R♭)}) = 𝔭 := by
    simp [map_span]
  have _ : IsHausdorff ((span {(p : 𝕎 R♭)}).map (fontaineTheta R p)) R := by
    rw [this]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (fontaineTheta R p) (I := span {(p : 𝕎 R♭)})
  simp only [RingHom.coe_comp]
  suffices h : Function.Surjective (Ideal.Quotient.mk 𝔭 ∘ fontaineTheta R p) by
    rwa [Ideal.map_span, Set.image_singleton, map_natCast]
  have : Ideal.Quotient.mk 𝔭 ∘ fontaineTheta R p = (fun x =>
      PreTilt.coeff 0 x) ∘ fun (x : 𝕎 R♭) => (x.coeff 0) := by
    ext
    simp [mk_fontaineTheta]
  rw [this]
  apply Function.Surjective.comp
  · exact Perfection.coeff_surjective hF 0
  · exact WittVector.coeff_surjective 0
