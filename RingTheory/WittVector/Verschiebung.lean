/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.IsPoly

/-!
## The Verschiebung operator

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

open MvPolynomial

variable {p : Nat} {R S : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

/--
Definition of `verschiebungFun` / `verschiebungFun` 的定义

English:
definition verschiebungFun
  signature: (x : 𝕎 R)
  body: @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)

中文:
定义 verschiebungFun
  签名: (x : 𝕎 R)
  定义体: @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)

Depends on / 依赖: x.coeff
-/
def verschiebungFun (x : 𝕎 R) : 𝕎 R :=
  @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)

/--
theorem `verschiebungFun_coeff` / 定理 `verschiebungFun_coeff`

English:
theorem verschiebungFun_coeff
  given: (x : 𝕎 R) (n : Nat)
  proof: by
  simp only [verschiebungFun]

中文:
定理 verschiebungFun_coeff
  条件: (x : 𝕎 R) (n : 自然数)
  证明: by
  simp only [verschiebungFun]

Depends on / 依赖: verschiebungFun
-/
theorem verschiebungFun_coeff (x : 𝕎 R) (n : Nat) :
    (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) := by
  simp only [verschiebungFun]

/--
theorem `verschiebungFun_coeff_zero` / 定理 `verschiebungFun_coeff_zero`

English:
theorem verschiebungFun_coeff_zero
  given: (x : 𝕎 R)
  statement: (verschiebungFun x).coeff 0 = 0
  proof: by
  rw [verschiebungFun_coeff]; rw [if_pos rfl]

@[simp]

中文:
定理 verschiebungFun_coeff_zero
  条件: (x : 𝕎 R)
  结论: (verschiebungFun x).coeff 0 = 0
  证明: by
  rw [verschiebungFun_coeff]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: if_pos, verschiebungFun_coeff
-/
theorem verschiebungFun_coeff_zero (x : 𝕎 R) : (verschiebungFun x).coeff 0 = 0 := by
  rw [verschiebungFun_coeff]; rw [if_pos rfl]

@[simp]
/--
theorem `verschiebungFun_coeff_succ` / 定理 `verschiebungFun_coeff_succ`

English:
theorem verschiebungFun_coeff_succ
  given: (x : 𝕎 R) (n : Nat)
  proof: rfl

@[ghost_simps]

中文:
定理 verschiebungFun_coeff_succ
  条件: (x : 𝕎 R) (n : 自然数)
  证明: rfl

@[ghost_simps]
-/
theorem verschiebungFun_coeff_succ (x : 𝕎 R) (n : Nat) :
    (verschiebungFun x).coeff n.succ = x.coeff n :=
  rfl

@[ghost_simps]
/--
theorem `ghostComponent_zero_verschiebungFun` / 定理 `ghostComponent_zero_verschiebungFun`

English:
theorem ghostComponent_zero_verschiebungFun
  given: [hp : Fact p.Prime] (x : 𝕎 R)
  proof: by
  rw [ghostComponent_apply]; rw [aeval_wittPolynomial]; rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [verschiebungFun_coeff_zero]; rw [pow_zero]; rw [pow_zero]; rw [pow_one]; rw [one_mul]

@[ghost_simps]

中文:
定理 ghostComponent_zero_verschiebungFun
  条件: [hp : Fact p.素] (x : 𝕎 R)
  证明: by
  rw [ghostComponent_apply]; rw [aeval_wittPolynomial]; rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [verschiebungFun_coeff_zero]; rw [pow_zero]; rw [pow_zero]; rw [pow_one]; rw [one_mul]

@[ghost_simps]

Depends on / 依赖: Finset, Finset.range_one, Finset.sum_singleton, aeval_wittPolynomial, ghostComponent_apply, one_mul, pow_one, pow_zero, range_one, sum_singleton, verschiebungFun_coeff_zero
-/
theorem ghostComponent_zero_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) :
    ghostComponent 0 (verschiebungFun x) = 0 := by
  rw [ghostComponent_apply]; rw [aeval_wittPolynomial]; rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [verschiebungFun_coeff_zero]; rw [pow_zero]; rw [pow_zero]; rw [pow_one]; rw [one_mul]

@[ghost_simps]
/--
theorem `ghostComponent_verschiebungFun` / 定理 `ghostComponent_verschiebungFun`

English:
theorem ghostComponent_verschiebungFun
  given: [hp : Fact p.Prime] (x : 𝕎 R) (n : Nat)
  proof: by
  simp only [ghostComponent_apply, aeval_wittPolynomial]
  rw [Finset.sum_range_succ']; rw [verschiebungFun_coeff]; rw [if_pos rfl]; rw [zero_pow (pow_ne_zero _ hp.1.ne_zero)]; rw [mul_zero]; rw [add_zero]; rw [Finset.mul_sum]; rw [Finset.sum_congr rfl]
  rintro i -
  simp only [pow_succ', versch

中文:
定理 ghostComponent_verschiebungFun
  条件: [hp : Fact p.素] (x : 𝕎 R) (n : 自然数)
  证明: by
  simp only [ghostComponent_apply, aeval_wittPolynomial]
  rw [Finset.sum_range_succ']; rw [verschiebungFun_coeff]; rw [if_pos rfl]; rw [zero_pow (pow_ne_zero _ hp.1.ne_zero)]; rw [mul_zero]; rw [add_zero]; rw [Finset.mul_sum]; rw [Finset.sum_congr rfl]
  rintro i -
  simp only [pow_succ', versch

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_congr, Finset.sum_range_succ, Nat.succ_sub_succ_eq_sub, add_zero, aeval_wittPolynomial, ghostComponent_apply, if_pos, mul_assoc, mul_sum, mul_zero, ne_zero, pow_ne_zero, pow_succ, succ_sub_succ_eq_sub, sum_congr, sum_range_succ, verschiebungFun_coeff, verschiebungFun_coeff_succ
-/
theorem ghostComponent_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) (n : Nat) :
    ghostComponent (n + 1) (verschiebungFun x) = p * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial]
  rw [Finset.sum_range_succ']; rw [verschiebungFun_coeff]; rw [if_pos rfl]; rw [zero_pow (pow_ne_zero _ hp.1.ne_zero)]; rw [mul_zero]; rw [add_zero]; rw [Finset.mul_sum]; rw [Finset.sum_congr rfl]
  rintro i -
  simp only [pow_succ', verschiebungFun_coeff_succ, Nat.succ_sub_succ_eq_sub, mul_assoc]

/--
Definition of `verschiebungPoly` / `verschiebungPoly` 的定义

English:
definition verschiebungPoly
  signature: (n : Nat)
  body: if n = 0 then 0 else X (n - 1)

@[simp]

中文:
定义 verschiebungPoly
  签名: (n : 自然数)
  定义体: if n = 0 then 0 else X (n - 1)

@[simp]
-/
def verschiebungPoly (n : Nat) : MvPolynomial Nat Int :=
  if n = 0 then 0 else X (n - 1)

@[simp]
/--
theorem `verschiebungPoly_zero` / 定理 `verschiebungPoly_zero`

English:
theorem verschiebungPoly_zero
  statement: verschiebungPoly 0 = 0
  proof: rfl

中文:
定理 verschiebungPoly_zero
  结论: verschiebungPoly 0 = 0
  证明: rfl
-/
theorem verschiebungPoly_zero : verschiebungPoly 0 = 0 :=
  rfl

/--
theorem `aeval_verschiebung_poly'` / 定理 `aeval_verschiebung_poly'`

English:
theorem aeval_verschiebung_poly'
  given: (x : 𝕎 R) (n : Nat)
  proof: by
  rcases n with - | n
  · simp only [verschiebungPoly, ite_true, map_zero, verschiebungFun_coeff_zero]
  · rw [verschiebungPoly, verschiebungFun_coeff_succ, if_neg n.succ_ne_zero, aeval_X,
      add_tsub_cancel_right]

中文:
定理 aeval_verschiebung_poly'
  条件: (x : 𝕎 R) (n : 自然数)
  证明: by
  rcases n with - | n
  · simp only [verschiebungPoly, ite_true, map_zero, verschiebungFun_coeff_zero]
  · rw [verschiebungPoly, verschiebungFun_coeff_succ, if_neg n.succ_ne_zero, aeval_X,
      add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, aeval_X, if_neg, ite_true, map_zero, n.succ_ne_zero, succ_ne_zero, verschiebungFun_coeff_succ, verschiebungFun_coeff_zero, verschiebungPoly
-/
theorem aeval_verschiebung_poly' (x : 𝕎 R) (n : Nat) :
    aeval x.coeff (verschiebungPoly n) = (verschiebungFun x).coeff n := by
  rcases n with - | n
  · simp only [verschiebungPoly, ite_true, map_zero, verschiebungFun_coeff_zero]
  · rw [verschiebungPoly, verschiebungFun_coeff_succ, if_neg n.succ_ne_zero, aeval_X,
      add_tsub_cancel_right]

variable (p)

/--
Instance `verschiebungFun_isPoly` / 实例 `verschiebungFun_isPoly`

English:
instance verschiebungFun_isPoly
  signature: : IsPoly p fun R _Rcr => @verschiebungFun p R _Rcr
  body: by
  use verschiebungPoly
  simp only [aeval_verschiebung_poly', forall₃_true_iff]

中文:
实例 verschiebungFun_isPoly
  签名: : 是Poly p fun R _Rcr => @verschiebungFun p R _Rcr
  定义体: by
  use verschiebungPoly
  simp only [aeval_verschiebung_poly', forall₃_true_iff]

Depends on / 依赖: aeval_verschiebung_poly, verschiebungPoly
-/
instance verschiebungFun_isPoly : IsPoly p fun R _Rcr => @verschiebungFun p R _Rcr := by
  use verschiebungPoly
  simp only [aeval_verschiebung_poly', forall₃_true_iff]

-- We add this example as a verification that Lean 4's instance resolution can handle the `IsPoly`
-- typeclass, whereas Lean 3 needed a bespoke `@[is_poly]` attribute.
example (p : Nat) (f : ⦃R : Type _⦄ -> [CommRing R] -> WittVector p R -> WittVector p R) [IsPoly p f] :
    IsPoly p (fun (R : Type*) (I : CommRing R) => verschiebungFun ∘ (@f R I)) :=
  inferInstance

variable {p}
variable [hp : Fact p.Prime]

/--
Definition of `verschiebung` / `verschiebung` 的定义

English:
definition verschiebung
  signature: : 𝕎 R ->+ 𝕎 R where
  body: verschiebungFun
  map_zero' := by
    ext ⟨⟩ <;> rw [verschiebungFun_coeff] <;>
      simp only [zero_coeff, ite_self]
  map_add' := by
    ghost_calc _ _
    rintro ⟨⟩ <;> ghost_simp

中文:
定义 verschiebung
  签名: : 𝕎 R ->+ 𝕎 R where
  定义体: verschiebungFun
  map_zero' := by
    ext ⟨⟩ <;> rw [verschiebungFun_coeff] <;>
      simp only [zero_coeff, ite_self]
  map_add' := by
    ghost_calc _ _
    rintro ⟨⟩ <;> ghost_simp

Depends on / 依赖: verschiebungFun
-/
noncomputable def verschiebung : 𝕎 R ->+ 𝕎 R where
  toFun := verschiebungFun
  map_zero' := by
    ext ⟨⟩ <;> rw [verschiebungFun_coeff] <;>
      simp only [zero_coeff, ite_self]
  map_add' := by
    ghost_calc _ _
    rintro ⟨⟩ <;> ghost_simp

/-- `WittVector.verschiebung` is a polynomial function. -/
@[is_poly]
/--
theorem `verschiebung_isPoly` / 定理 `verschiebung_isPoly`

English:
theorem verschiebung_isPoly
  statement: IsPoly p fun _ _ => verschiebung (p := p)
  proof: verschiebungFun_isPoly p

中文:
定理 verschiebung_isPoly
  结论: 是Poly p fun _ _ => verschiebung (p := p)
  证明: verschiebungFun_isPoly p
-/
theorem verschiebung_isPoly : IsPoly p fun _ _ => verschiebung (p := p) :=
  verschiebungFun_isPoly p

/-- verschiebung is a natural transformation -/
@[simp]
/--
theorem `map_verschiebung` / 定理 `map_verschiebung`

English:
theorem map_verschiebung
  given: (f : R ->+* S) (x : 𝕎 R)
  proof: by
  ext ⟨-, -⟩
  · exact f.map_zero
  · rfl

@[ghost_simps]

中文:
定理 map_verschiebung
  条件: (f : R ->+* S) (x : 𝕎 R)
  证明: by
  ext ⟨-, -⟩
  · exact f.map_zero
  · rfl

@[ghost_simps]

Depends on / 依赖: f.map_zero, map_zero
-/
theorem map_verschiebung (f : R ->+* S) (x : 𝕎 R) :
    map f (verschiebung x) = verschiebung (map f x) := by
  ext ⟨-, -⟩
  · exact f.map_zero
  · rfl

@[ghost_simps]
/--
theorem `ghostComponent_zero_verschiebung` / 定理 `ghostComponent_zero_verschiebung`

English:
theorem ghostComponent_zero_verschiebung
  given: (x : 𝕎 R)
  statement: ghostComponent 0 (verschiebung x) = 0
  proof: ghostComponent_zero_verschiebungFun _

@[ghost_simps]

中文:
定理 ghostComponent_zero_verschiebung
  条件: (x : 𝕎 R)
  结论: ghostComponent 0 (verschiebung x) = 0
  证明: ghostComponent_zero_verschiebungFun _

@[ghost_simps]

Depends on / 依赖: Equiv.Set.univ, ghostComponent_zero_verschiebungFun
-/
theorem ghostComponent_zero_verschiebung (x : 𝕎 R) : ghostComponent 0 (verschiebung x) = 0 :=
  ghostComponent_zero_verschiebungFun _

@[ghost_simps]
/--
theorem `ghostComponent_verschiebung` / 定理 `ghostComponent_verschiebung`

English:
theorem ghostComponent_verschiebung
  given: (x : 𝕎 R) (n : Nat)
  proof: ghostComponent_verschiebungFun _ _

@[simp]

中文:
定理 ghostComponent_verschiebung
  条件: (x : 𝕎 R) (n : 自然数)
  证明: ghostComponent_verschiebungFun _ _

@[simp]

Depends on / 依赖: Equiv.Set.prod, ghostComponent_verschiebungFun
-/
theorem ghostComponent_verschiebung (x : 𝕎 R) (n : Nat) :
    ghostComponent (n + 1) (verschiebung x) = p * ghostComponent n x :=
  ghostComponent_verschiebungFun _ _

@[simp]
/--
theorem `verschiebung_coeff_zero` / 定理 `verschiebung_coeff_zero`

English:
theorem verschiebung_coeff_zero
  given: (x : 𝕎 R)
  statement: (verschiebung x).coeff 0 = 0
  proof: rfl

中文:
定理 verschiebung_coeff_zero
  条件: (x : 𝕎 R)
  结论: (verschiebung x).coeff 0 = 0
  证明: rfl
-/
theorem verschiebung_coeff_zero (x : 𝕎 R) : (verschiebung x).coeff 0 = 0 :=
  rfl

-- simp_nf complains if this is simp
/--
theorem `verschiebung_coeff_add_one` / 定理 `verschiebung_coeff_add_one`

English:
theorem verschiebung_coeff_add_one
  given: (x : 𝕎 R) (n : Nat)
  proof: rfl

@[simp]

中文:
定理 verschiebung_coeff_add_one
  条件: (x : 𝕎 R) (n : 自然数)
  证明: rfl

@[simp]
-/
theorem verschiebung_coeff_add_one (x : 𝕎 R) (n : Nat) :
    (verschiebung x).coeff (n + 1) = x.coeff n :=
  rfl

@[simp]
/--
theorem `verschiebung_coeff_succ` / 定理 `verschiebung_coeff_succ`

English:
theorem verschiebung_coeff_succ
  given: (x : 𝕎 R) (n : Nat)
  statement: (verschiebung x).coeff n.succ = x.coeff n
  proof: rfl

中文:
定理 verschiebung_coeff_succ
  条件: (x : 𝕎 R) (n : 自然数)
  结论: (verschiebung x).coeff n.succ = x.coeff n
  证明: rfl
-/
theorem verschiebung_coeff_succ (x : 𝕎 R) (n : Nat) : (verschiebung x).coeff n.succ = x.coeff n :=
  rfl

variable (p R) in
/--
theorem `verschiebung_injective` / 定理 `verschiebung_injective`

English:
theorem verschiebung_injective
  statement: Function.Injective (verschiebung : 𝕎 R -> 𝕎 R)
  proof: by
  rw [injective_iff_map_eq_zero]
  intro w h
  ext n
  rw [← verschiebung_coeff_succ]; rw [h]
  simp only [zero_coeff]

中文:
定理 verschiebung_injective
  结论: 函数.单射 (verschiebung : 𝕎 R -> 𝕎 R)
  证明: by
  rw [injective_iff_map_eq_zero]
  intro w h
  ext n
  rw [← verschiebung_coeff_succ]; rw [h]
  simp only [zero_coeff]

Depends on / 依赖: injective_iff_map_eq_zero, verschiebung_coeff_succ, zero_coeff
-/
theorem verschiebung_injective : Function.Injective (verschiebung : 𝕎 R -> 𝕎 R) := by
  rw [injective_iff_map_eq_zero]
  intro w h
  ext n
  rw [← verschiebung_coeff_succ]; rw [h]
  simp only [zero_coeff]

/--
theorem `aeval_verschiebungPoly` / 定理 `aeval_verschiebungPoly`

English:
theorem aeval_verschiebungPoly
  given: (x : 𝕎 R) (n : Nat)
  proof: aeval_verschiebung_poly' x n

@[simp]

中文:
定理 aeval_verschiebungPoly
  条件: (x : 𝕎 R) (n : 自然数)
  证明: aeval_verschiebung_poly' x n

@[simp]

Depends on / 依赖: aeval_verschiebung_poly
-/
theorem aeval_verschiebungPoly (x : 𝕎 R) (n : Nat) :
    aeval x.coeff (verschiebungPoly n) = (verschiebung x).coeff n :=
  aeval_verschiebung_poly' x n

@[simp]
/--
theorem `bind₁_verschiebungPoly_wittPolynomial` / 定理 `bind₁_verschiebungPoly_wittPolynomial`

English:
theorem bind₁_verschiebungPoly_wittPolynomial
  given: (n : Nat)
  proof: by
  apply MvPolynomial.funext
  intro x
  split_ifs with hn
  · simp only [hn, wittPolynomial_zero, bind₁_X_right, verschiebungPoly_zero, map_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one]; rw [add_tsub_cancel_right]
    simp only [map_mul]
    rw [map_na

中文:
定理 bind₁_verschiebungPoly_wittPolynomial
  条件: (n : 自然数)
  证明: by
  apply MvPolynomial.funext
  intro x
  split_ifs with hn
  · simp only [hn, wittPolynomial_zero, bind₁_X_right, verschiebungPoly_zero, map_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one]; rw [add_tsub_cancel_right]
    simp only [map_mul]
    rw [map_na

Depends on / 依赖: MvPolynomial, MvPolynomial.funext, Nat.exists_eq_succ_of_ne_zero, Nat.succ_eq_add_one, RingHom, RingHom.ext_int, add_tsub_cancel_right, aeval_verschiebungPoly, exists_eq_succ_of_ne_zero, ext_int, ghostComponent, map_mul, map_natCast, map_zero, split_ifs, succ_eq_add_one, verschiebung, verschiebungPoly_zero, wittPolynomial_zero
-/
theorem bind₁_verschiebungPoly_wittPolynomial (n : Nat) :
    bind₁ verschiebungPoly (wittPolynomial p Int n) =
      if n = 0 then 0 else p * wittPolynomial p Int (n - 1) := by
  apply MvPolynomial.funext
  intro x
  split_ifs with hn
  · simp only [hn, wittPolynomial_zero, bind₁_X_right, verschiebungPoly_zero, map_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one]; rw [add_tsub_cancel_right]
    simp only [map_mul]
    rw [map_natCast]; rw [hom_bind₁]
    calc
      _ = ghostComponent (n + 1) (verschiebung <| mk p x) := by
       apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
       funext k
       simp only [← aeval_verschiebungPoly]
       exact eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
      _ = _ := by rw [ghostComponent_verschiebung]; rfl

end

end WittVector
