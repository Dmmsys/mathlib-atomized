/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.NumberTheory.Padics.RingHoms

/-!

# Comparison isomorphism between `WittVector p (ZMod p)` and `ℤ_[p]`

We construct a ring isomorphism between `WittVector p (ZMod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `ZMod (p^n)`.

## Main declarations

* `WittVector.toZModPow`: a family of compatible ring homs `𝕎 (ZMod p) → ZMod (p^k)`
* `WittVector.equiv`: the isomorphism

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


noncomputable section

variable {p : Nat} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace TruncatedWittVector

variable (p) (n : Nat) (R : Type*) [CommRing R]

/--
theorem `eq_of_le_of_cast_pow_eq_zero` / 定理 `eq_of_le_of_cast_pow_eq_zero`

English:
theorem eq_of_le_of_cast_pow_eq_zero
  statement: [CharP R p] (i : Nat) (hin : i <= n)
  proof: by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi; clear hpi
  have : (p : TruncatedWittVector p n R) ^ i = WittVector.truncate n ((p : 𝕎 R) ^ i) := by
    rw [map_pow]; rw [map_natCast]
  rw [this]; rw [ne_eq]; rw [TruncatedWittVector.ext_iff]; rw [not_forall]; clear this
  use ⟨i, hin⟩


中文:
定理 eq_of_le_of_cast_pow_eq_zero
  结论: [CharP R p] (i : 自然数) (hin : i <= n)
  证明: by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi; clear hpi
  have : (p : TruncatedWittVector p n R) ^ i = WittVector.truncate n ((p : 𝕎 R) ^ i) := by
    rw [map_pow]; rw [map_natCast]
  rw [this]; rw [ne_eq]; rw [TruncatedWittVector.ext_iff]; rw [not_forall]; clear this
  use ⟨i, hin⟩


Depends on / 依赖: CharP.nontrivial_of_char_ne_one, Fin.val_mk, Nontrivial, TruncatedWittVector, TruncatedWittVector.ext_iff, WittVector, WittVector.coeff_p_pow, WittVector.coeff_truncate, WittVector.truncate, coeff_p_pow, coeff_truncate, coeff_zero, contrapose, ext_iff, lt_of_le_of_ne, map_natCast, map_pow, ne_eq, ne_one, nontrivial_of_char_ne_one
-/
theorem eq_of_le_of_cast_pow_eq_zero [CharP R p] (i : Nat) (hin : i <= n)
    (hpi : (p : TruncatedWittVector p n R) ^ i = 0) : i = n := by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi; clear hpi
  have : (p : TruncatedWittVector p n R) ^ i = WittVector.truncate n ((p : 𝕎 R) ^ i) := by
    rw [map_pow]; rw [map_natCast]
  rw [this]; rw [ne_eq]; rw [TruncatedWittVector.ext_iff]; rw [not_forall]; clear this
  use ⟨i, hin⟩
  rw [WittVector.coeff_truncate]; rw [coeff_zero]; rw [Fin.val_mk]; rw [WittVector.coeff_p_pow]
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.1.ne_one
  exact one_ne_zero

section Iso

variable {R}

/--
theorem `card_zmod` / 定理 `card_zmod`

English:
theorem card_zmod
  statement: Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n
  proof: by
  rw [card]; rw [ZMod.card]

中文:
定理 card_zmod
  结论: Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n
  证明: by
  rw [card]; rw [ZMod.card]

Depends on / 依赖: ZMod.card
-/
theorem card_zmod : Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n := by
  rw [card]; rw [ZMod.card]

/--
theorem `charP_zmod` / 定理 `charP_zmod`

English:
theorem charP_zmod
  statement: CharP (TruncatedWittVector p n (ZMod p)) (p ^ n)
  proof: charP_of_prime_pow_injective _ _ _ (card_zmod _ _) (eq_of_le_of_cast_pow_eq_zero p n (ZMod p))

中文:
定理 charP_zmod
  结论: CharP (TruncatedWittVector p n (ZMod p)) (p ^ n)
  证明: charP_of_prime_pow_injective _ _ _ (card_zmod _ _) (eq_of_le_of_cast_pow_eq_zero p n (ZMod p))

Depends on / 依赖: card_zmod, charP_of_prime_pow_injective, eq_of_le_of_cast_pow_eq_zero
-/
theorem charP_zmod : CharP (TruncatedWittVector p n (ZMod p)) (p ^ n) :=
  charP_of_prime_pow_injective _ _ _ (card_zmod _ _) (eq_of_le_of_cast_pow_eq_zero p n (ZMod p))

attribute [local instance] charP_zmod

/--
Definition of `zmodEquivTrunc` / `zmodEquivTrunc` 的定义

English:
definition zmodEquivTrunc
  signature: : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p)
  body: ZMod.ringEquiv (TruncatedWittVector p n (ZMod p)) (card_zmod _ _)

中文:
定义 zmodEquivTrunc
  签名: : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p)
  定义体: ZMod.ringEquiv (TruncatedWittVector p n (ZMod p)) (card_zmod _ _)

Depends on / 依赖: TruncatedWittVector, ZMod.ringEquiv, card_zmod, ringEquiv
-/
def zmodEquivTrunc : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p) :=
  ZMod.ringEquiv (TruncatedWittVector p n (ZMod p)) (card_zmod _ _)

/--
theorem `zmodEquivTrunc_apply` / 定理 `zmodEquivTrunc_apply`

English:
theorem zmodEquivTrunc_apply
  given: {x : ZMod (p ^ n)}
  proof: rfl

中文:
定理 zmodEquivTrunc_apply
  条件: {x : ZMod (p ^ n)}
  证明: rfl

Depends on / 依赖: TruncatedWittVector
-/
theorem zmodEquivTrunc_apply {x : ZMod (p ^ n)} :
    zmodEquivTrunc p n x =
      ZMod.castHom (m := p ^ n) (by rfl) (TruncatedWittVector p n (ZMod p)) x :=
  rfl

/--
theorem `commutes` / 定理 `commutes`

English:
theorem commutes
  given: {m : Nat} (hm : n <= m)
  proof: RingHom.ext_zmod _ _

中文:
定理 commutes
  条件: {m : 自然数} (hm : n <= m)
  证明: RingHom.ext_zmod _ _

Depends on / 依赖: RingHom, RingHom.ext_zmod, ext_zmod
-/
theorem commutes {m : Nat} (hm : n <= m) :
    (truncate hm).comp (zmodEquivTrunc p m).toRingHom =
      (zmodEquivTrunc p n).toRingHom.comp (ZMod.castHom (pow_dvd_pow p hm) _) :=
  RingHom.ext_zmod _ _

/--
theorem `commutes'` / 定理 `commutes'`

English:
theorem commutes'
  given: {m : Nat} (hm : n <= m) (x : ZMod (p ^ m))
  proof: show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm]; rfl

中文:
定理 commutes'
  条件: {m : 自然数} (hm : n <= m) (x : ZMod (p ^ m))
  证明: show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm]; rfl

Depends on / 依赖: commutes, toRingHom, truncate, zmodEquivTrunc
-/
theorem commutes' {m : Nat} (hm : n <= m) (x : ZMod (p ^ m)) :
    truncate hm (zmodEquivTrunc p m x) = zmodEquivTrunc p n (ZMod.castHom (pow_dvd_pow p hm) _ x) :=
  show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm]; rfl

/--
theorem `commutes_symm'` / 定理 `commutes_symm'`

English:
theorem commutes_symm'
  given: {m : Nat} (hm : n <= m) (x : TruncatedWittVector p m (ZMod p))
  proof: by
  apply (zmodEquivTrunc p n).injective
  rw [← commutes' _ _ hm]
  simp

中文:
定理 commutes_symm'
  条件: {m : 自然数} (hm : n <= m) (x : TruncatedWittVector p m (ZMod p))
  证明: by
  apply (zmodEquivTrunc p n).injective
  rw [← commutes' _ _ hm]
  simp

Depends on / 依赖: commutes, injective, zmodEquivTrunc
-/
theorem commutes_symm' {m : Nat} (hm : n <= m) (x : TruncatedWittVector p m (ZMod p)) :
    (zmodEquivTrunc p n).symm (truncate hm x) =
      ZMod.castHom (pow_dvd_pow p hm) _ ((zmodEquivTrunc p m).symm x) := by
  apply (zmodEquivTrunc p n).injective
  rw [← commutes' _ _ hm]
  simp

/--
theorem `commutes_symm` / 定理 `commutes_symm`

English:
theorem commutes_symm
  given: {m : Nat} (hm : n <= m)
  proof: by
  ext; apply commutes_symm'

中文:
定理 commutes_symm
  条件: {m : 自然数} (hm : n <= m)
  证明: by
  ext; apply commutes_symm'

Depends on / 依赖: commutes_symm
-/
theorem commutes_symm {m : Nat} (hm : n <= m) :
    (zmodEquivTrunc p n).symm.toRingHom.comp (truncate hm) =
      (ZMod.castHom (pow_dvd_pow p hm) _).comp (zmodEquivTrunc p m).symm.toRingHom := by
  ext; apply commutes_symm'

end Iso

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (p)

/--
Definition of `toZModPow` / `toZModPow` 的定义

English:
definition toZModPow
  signature: (k : Nat)
  body: (zmodEquivTrunc p k).symm.toRingHom.comp (truncate k)

中文:
定义 toZModPow
  签名: (k : 自然数)
  定义体: (zmodEquivTrunc p k).symm.toRingHom.comp (truncate k)

Depends on / 依赖: symm.toRingHom.comp, toRingHom, truncate, zmodEquivTrunc
-/
def toZModPow (k : Nat) : 𝕎 (ZMod p) ->+* ZMod (p ^ k) :=
  (zmodEquivTrunc p k).symm.toRingHom.comp (truncate k)

/--
theorem `toZModPow_compat` / 定理 `toZModPow_compat`

English:
theorem toZModPow_compat
  given: (m n : Nat) (h : m <= n)
  proof: calc
    (ZMod.castHom _ (ZMod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n))
    _ = ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) := by
      rw [commutes_symm]; rw [RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).s

中文:
定理 toZModPow_compat
  条件: (m n : 自然数) (h : m <= n)
  证明: calc
    (ZMod.castHom _ (ZMod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n))
    _ = ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) := by
      rw [commutes_symm]; rw [RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).s

Depends on / 依赖: RingHom, RingHom.comp_assoc, TruncatedWittVector, TruncatedWittVector.truncate, ZMod.castHom, castHom, commutes_symm, comp_assoc, symm.toRingHom.comp, toRingHom, truncate, truncate_comp_wittVector_truncate, zmodEquivTrunc
-/
theorem toZModPow_compat (m n : Nat) (h : m <= n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPow p m :=
  calc
    (ZMod.castHom _ (ZMod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n))
    _ = ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) := by
      rw [commutes_symm]; rw [RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).symm.toRingHom.comp (truncate m) := by
      rw [RingHom.comp_assoc]; rw [truncate_comp_wittVector_truncate]

/--
Definition of `toPadicInt` / `toPadicInt` 的定义

English:
definition toPadicInt
  signature: : 𝕎 (ZMod p) ->+* Int_[p]
  body: PadicInt.lift toZModPow_compat p

中文:
定义 toPadicInt
  签名: : 𝕎 (ZMod p) ->+* 整数_[p]
  定义体: PadicInt.lift toZModPow_compat p

Depends on / 依赖: PadicInt, PadicInt.lift, toZModPow_compat
-/
def toPadicInt : 𝕎 (ZMod p) ->+* Int_[p] :=
PadicInt.lift toZModPow_compat p

/--
theorem `zmodEquivTrunc_compat` / 定理 `zmodEquivTrunc_compat`

English:
theorem zmodEquivTrunc_compat
  given: (k₁ k₂ : Nat) (hk : k₁ <= k₂)
  proof: by
  rw [← RingHom.comp_assoc]; rw [commutes]; rw [RingHom.comp_assoc]; rw [PadicInt.zmod_cast_comp_toZModPow _ _ hk]

中文:
定理 zmodEquivTrunc_compat
  条件: (k₁ k₂ : 自然数) (hk : k₁ <= k₂)
  证明: by
  rw [← RingHom.comp_assoc]; rw [commutes]; rw [RingHom.comp_assoc]; rw [PadicInt.zmod_cast_comp_toZModPow _ _ hk]

Depends on / 依赖: PadicInt, PadicInt.zmod_cast_comp_toZModPow, RingHom, RingHom.comp_assoc, commutes, comp_assoc, zmod_cast_comp_toZModPow
-/
theorem zmodEquivTrunc_compat (k₁ k₂ : Nat) (hk : k₁ <= k₂) :
    (TruncatedWittVector.truncate hk).comp
        ((zmodEquivTrunc p k₂).toRingHom.comp (PadicInt.toZModPow k₂)) =
      (zmodEquivTrunc p k₁).toRingHom.comp (PadicInt.toZModPow k₁) := by
  rw [← RingHom.comp_assoc]; rw [commutes]; rw [RingHom.comp_assoc]; rw [PadicInt.zmod_cast_comp_toZModPow _ _ hk]

/--
Definition of `fromPadicInt` / `fromPadicInt` 的定义

English:
definition fromPadicInt
  signature: : Int_[p] ->+* 𝕎 (ZMod p)
  body: (WittVector.lift fun k => (zmodEquivTrunc p k).toRingHom.comp (PadicInt.toZModPow k))
    zmodEquivTrunc_compat _

中文:
定义 fromPadicInt
  签名: : 整数_[p] ->+* 𝕎 (ZMod p)
  定义体: (WittVector.lift fun k => (zmodEquivTrunc p k).toRingHom.comp (PadicInt.toZModPow k))
    zmodEquivTrunc_compat _

Depends on / 依赖: PadicInt, PadicInt.toZModPow, WittVector, WittVector.lift, toRingHom, toRingHom.comp, toZModPow, zmodEquivTrunc, zmodEquivTrunc_compat
-/
def fromPadicInt : Int_[p] ->+* 𝕎 (ZMod p) :=
(WittVector.lift fun k => (zmodEquivTrunc p k).toRingHom.comp (PadicInt.toZModPow k))
    zmodEquivTrunc_compat _

/--
theorem `toPadicInt_comp_fromPadicInt` / 定理 `toPadicInt_comp_fromPadicInt`

English:
theorem toPadicInt_comp_fromPadicInt
  statement: (toPadicInt p).comp (fromPadicInt p) = RingHom.id Int_[p]
  proof: by
  rw [← PadicInt.toZModPow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc]; rw [toPadicInt]; rw [PadicInt.lift_spec]
  simp only [fromPadicInt, toZModPow, RingHom.comp_id]
  rw [RingHom.comp_assoc]; rw [truncate_comp_lift]; rw [← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_to

中文:
定理 toPadicInt_comp_fromPadicInt
  结论: (toPadic整数 p).comp (fromPadic整数 p) = RingHom.id 整数_[p]
  证明: by
  rw [← PadicInt.toZModPow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc]; rw [toPadicInt]; rw [PadicInt.lift_spec]
  simp only [fromPadicInt, toZModPow, RingHom.comp_id]
  rw [RingHom.comp_assoc]; rw [truncate_comp_lift]; rw [← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_to

Depends on / 依赖: PadicInt, PadicInt.lift_spec, PadicInt.toZModPow_eq_iff_ext, RingEquiv, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom, RingHom.comp_assoc, RingHom.comp_id, RingHom.id_comp, comp_assoc, comp_id, fromPadicInt, id_comp, lift_spec, symm_toRingHom_comp_toRingHom, toPadicInt, toZModPow, toZModPow_eq_iff_ext, truncate_comp_lift
-/
theorem toPadicInt_comp_fromPadicInt : (toPadicInt p).comp (fromPadicInt p) = RingHom.id Int_[p] := by
  rw [← PadicInt.toZModPow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc]; rw [toPadicInt]; rw [PadicInt.lift_spec]
  simp only [fromPadicInt, toZModPow, RingHom.comp_id]
  rw [RingHom.comp_assoc]; rw [truncate_comp_lift]; rw [← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]

/--
theorem `toPadicInt_comp_fromPadicInt_ext` / 定理 `toPadicInt_comp_fromPadicInt_ext`

English:
theorem toPadicInt_comp_fromPadicInt_ext
  given: (x)
  proof: by
  rw [toPadicInt_comp_fromPadicInt]

中文:
定理 toPadicInt_comp_fromPadicInt_ext
  条件: (x)
  证明: by
  rw [toPadicInt_comp_fromPadicInt]

Depends on / 依赖: toPadicInt_comp_fromPadicInt
-/
theorem toPadicInt_comp_fromPadicInt_ext (x) :
    (toPadicInt p).comp (fromPadicInt p) x = RingHom.id Int_[p] x := by
  rw [toPadicInt_comp_fromPadicInt]

/--
theorem `fromPadicInt_comp_toPadicInt` / 定理 `fromPadicInt_comp_toPadicInt`

English:
theorem fromPadicInt_comp_toPadicInt
  proof: by
  apply WittVector.hom_ext
  intro n
  rw [fromPadicInt]; rw [← RingHom.comp_assoc]; rw [truncate_comp_lift]; rw [RingHom.comp_assoc]
  simp only [toPadicInt, toZModPow, RingHom.comp_id, PadicInt.lift_spec, RingHom.id_comp, ←
    RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom]

中文:
定理 fromPadicInt_comp_toPadicInt
  证明: by
  apply WittVector.hom_ext
  intro n
  rw [fromPadicInt]; rw [← RingHom.comp_assoc]; rw [truncate_comp_lift]; rw [RingHom.comp_assoc]
  simp only [toPadicInt, toZModPow, RingHom.comp_id, PadicInt.lift_spec, RingHom.id_comp, ←
    RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom]

Depends on / 依赖: PadicInt, PadicInt.lift_spec, RingEquiv, RingEquiv.toRingHom_comp_symm_toRingHom, RingHom, RingHom.comp_assoc, RingHom.comp_id, RingHom.id_comp, WittVector, WittVector.hom_ext, comp_assoc, comp_id, fromPadicInt, hom_ext, id_comp, lift_spec, toPadicInt, toRingHom_comp_symm_toRingHom, toZModPow, truncate_comp_lift
-/
theorem fromPadicInt_comp_toPadicInt :
    (fromPadicInt p).comp (toPadicInt p) = RingHom.id (𝕎 (ZMod p)) := by
  apply WittVector.hom_ext
  intro n
  rw [fromPadicInt]; rw [← RingHom.comp_assoc]; rw [truncate_comp_lift]; rw [RingHom.comp_assoc]
  simp only [toPadicInt, toZModPow, RingHom.comp_id, PadicInt.lift_spec, RingHom.id_comp, ←
    RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom]

/--
theorem `fromPadicInt_comp_toPadicInt_ext` / 定理 `fromPadicInt_comp_toPadicInt_ext`

English:
theorem fromPadicInt_comp_toPadicInt_ext
  given: (x)
  proof: by
  rw [fromPadicInt_comp_toPadicInt]

中文:
定理 fromPadicInt_comp_toPadicInt_ext
  条件: (x)
  证明: by
  rw [fromPadicInt_comp_toPadicInt]

Depends on / 依赖: fromPadicInt_comp_toPadicInt
-/
theorem fromPadicInt_comp_toPadicInt_ext (x) :
    (fromPadicInt p).comp (toPadicInt p) x = RingHom.id (𝕎 (ZMod p)) x := by
  rw [fromPadicInt_comp_toPadicInt]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : 𝕎 (ZMod p) ≃+* Int_[p] where
  body: toPadicInt p
  invFun := fromPadicInt p
  left_inv := fromPadicInt_comp_toPadicInt_ext _
  right_inv := toPadicInt_comp_fromPadicInt_ext _
  map_mul' := map_mul _
  map_add' := map_add _

中文:
定义 equiv
  签名: : 𝕎 (ZMod p) ≃+* 整数_[p] where
  定义体: toPadicInt p
  invFun := fromPadicInt p
  left_inv := fromPadicInt_comp_toPadicInt_ext _
  right_inv := toPadicInt_comp_fromPadicInt_ext _
  map_mul' := map_mul _
  map_add' := map_add _

Depends on / 依赖: toPadicInt
-/
def equiv : 𝕎 (ZMod p) ≃+* Int_[p] where
  toFun := toPadicInt p
  invFun := fromPadicInt p
  left_inv := fromPadicInt_comp_toPadicInt_ext _
  right_inv := toPadicInt_comp_fromPadicInt_ext _
  map_mul' := map_mul _
  map_add' := map_add _

end WittVector
