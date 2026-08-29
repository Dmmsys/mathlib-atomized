/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Infima/suprema in ordered monoids and groups

In this file we prove a few facts like “The infimum of `-s` is `-` the supremum of `s`”.

## TODO

`sSup (s • t) = sSup s • sSup t` and `sInf (s • t) = sInf s • sInf t` hold as well but
`CovariantClass` is currently not polymorphic enough to state it.
-/

public section

open Function Set
open scoped Pointwise

variable {M : Type*}

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice M]

section One
variable [One M]

/--
lemma `csSup_one` / 引理 `csSup_one`

English:
lemma csSup_one
  statement: sSup (1 : Set M) = 1
  proof: csSup_singleton _

中文:
引理 csSup_one
  结论: sSup (1 : 集合 M) = 1
  证明: csSup_singleton _
-/
@[to_additive (attr := simp)] lemma csSup_one : sSup (1 : Set M) = 1 := csSup_singleton _
/--
lemma `csInf_one` / 引理 `csInf_one`

English:
lemma csInf_one
  statement: sInf (1 : Set M) = 1
  proof: csInf_singleton _

中文:
引理 csInf_one
  结论: sInf (1 : 集合 M) = 1
  证明: csInf_singleton _
-/
@[to_additive (attr := simp)] lemma csInf_one : sInf (1 : Set M) = 1 := csInf_singleton _

end One

section Group
variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

@[to_additive]
/--
lemma `csSup_inv` / 引理 `csSup_inv`

English:
lemma csSup_inv
  given: (hs₀ : s.Nonempty) (hs₁ : BddBelow s)
  statement: sSup s⁻¹ = (sInf s)⁻¹
  proof: by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csInf' hs₀ hs₁).symm

@[to_additive]

中文:
引理 csSup_inv
  条件: (hs₀ : s.非空) (hs₁ : BddBelow s)
  结论: sSup s⁻¹ = (sInf s)⁻¹
  证明: by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csInf' hs₀ hs₁).symm

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, image_inv_eq_inv, map_csInf
-/
lemma csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csInf' hs₀ hs₁).symm

@[to_additive]
/--
lemma `csInf_inv` / 引理 `csInf_inv`

English:
lemma csInf_inv
  given: (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
  statement: sInf s⁻¹ = (sSup s)⁻¹
  proof: by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csSup' hs₀ hs₁).symm

@[to_additive]

中文:
引理 csInf_inv
  条件: (hs₀ : s.非空) (hs₁ : BddAbove s)
  结论: sInf s⁻¹ = (sSup s)⁻¹
  证明: by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csSup' hs₀ hs₁).symm

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, image_inv_eq_inv, map_csSup
-/
lemma csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csSup' hs₀ hs₁).symm

@[to_additive]
/--
lemma `csSup_mul` / 引理 `csSup_mul`

English:
lemma csSup_mul
  given: (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t)
  proof: csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]

中文:
引理 csSup_mul
  条件: (hs₀ : s.非空) (hs₁ : BddAbove s) (ht₀ : t.非空) (ht₁ : BddAbove t)
  证明: csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, OrderIso.mulRight, csSup_image2_eq_csSup_csSup, mulLeft, mulRight, to_galoisConnection
-/
lemma csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sSup (s * t) = sSup s * sSup t :=
  csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]
/--
lemma `csInf_mul` / 引理 `csInf_mul`

English:
lemma csInf_mul
  given: (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t)
  proof: csInf_image2_eq_csInf_csInf (fun _ => (OrderIso.mulRight _).symm.to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]

中文:
引理 csInf_mul
  条件: (hs₀ : s.非空) (hs₁ : BddBelow s) (ht₀ : t.非空) (ht₁ : BddBelow t)
  证明: csInf_image2_eq_csInf_csInf (fun _ => (OrderIso.mulRight _).symm.to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, OrderIso.mulRight, csInf_image2_eq_csInf_csInf, mulLeft, mulRight, symm.to_galoisConnection, to_galoisConnection
-/
lemma csInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sInf (s * t) = sInf s * sInf t :=
  csInf_image2_eq_csInf_csInf (fun _ => (OrderIso.mulRight _).symm.to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]
/--
lemma `csSup_div` / 引理 `csSup_div`

English:
lemma csSup_div
  given: (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t)
  proof: by
  rw [div_eq_mul_inv]; rw [csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv]; rw [csSup_inv ht₀ ht₁]; rw [div_eq_mul_inv]

@[to_additive]

中文:
引理 csSup_div
  条件: (hs₀ : s.非空) (hs₁ : BddAbove s) (ht₀ : t.非空) (ht₁ : BddBelow t)
  证明: by
  rw [div_eq_mul_inv]; rw [csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv]; rw [csSup_inv ht₀ ht₁]; rw [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: csSup_inv, csSup_mul, div_eq_mul_inv
-/
lemma csSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sSup (s / t) = sSup s / sInf t := by
  rw [div_eq_mul_inv]; rw [csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv]; rw [csSup_inv ht₀ ht₁]; rw [div_eq_mul_inv]

@[to_additive]
/--
lemma `csInf_div` / 引理 `csInf_div`

English:
lemma csInf_div
  given: (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t)
  proof: by
  rw [div_eq_mul_inv]; rw [csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv]; rw [csInf_inv ht₀ ht₁]; rw [div_eq_mul_inv]

中文:
引理 csInf_div
  条件: (hs₀ : s.非空) (hs₁ : BddBelow s) (ht₀ : t.非空) (ht₁ : BddAbove t)
  证明: by
  rw [div_eq_mul_inv]; rw [csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv]; rw [csInf_inv ht₀ ht₁]; rw [div_eq_mul_inv]

Depends on / 依赖: csInf_inv, csInf_mul, div_eq_mul_inv
-/
lemma csInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sInf (s / t) = sInf s / sSup t := by
  rw [div_eq_mul_inv]; rw [csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv]; rw [csInf_inv ht₀ ht₁]; rw [div_eq_mul_inv]

end Group
end ConditionallyCompleteLattice

section CompleteLattice
variable [CompleteLattice M]

section One
variable [One M]

/--
lemma `sSup_one` / 引理 `sSup_one`

English:
lemma sSup_one
  statement: sSup (1 : Set M) = 1
  proof: sSup_singleton

中文:
引理 sSup_one
  结论: sSup (1 : 集合 M) = 1
  证明: sSup_singleton
-/
@[to_additive] lemma sSup_one : sSup (1 : Set M) = 1 := sSup_singleton
/--
lemma `sInf_one` / 引理 `sInf_one`

English:
lemma sInf_one
  statement: sInf (1 : Set M) = 1
  proof: sInf_singleton

中文:
引理 sInf_one
  结论: sInf (1 : 集合 M) = 1
  证明: sInf_singleton
-/
@[to_additive] lemma sInf_one : sInf (1 : Set M) = 1 := sInf_singleton

end One

section Group
variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

@[to_additive]
/--
lemma `sSup_inv` / 引理 `sSup_inv`

English:
lemma sSup_inv
  given: (s : Set M)
  statement: sSup s⁻¹ = (sInf s)⁻¹
  proof: by
  rw [← image_inv_eq_inv]; rw [sSup_image]
  exact ((OrderIso.inv M).map_sInf _).symm

@[to_additive]

中文:
引理 sSup_inv
  条件: (s : 集合 M)
  结论: sSup s⁻¹ = (sInf s)⁻¹
  证明: by
  rw [← image_inv_eq_inv]; rw [sSup_image]
  exact ((OrderIso.inv M).map_sInf _).symm

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, image_inv_eq_inv, map_sInf, sSup_image
-/
lemma sSup_inv (s : Set M) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv]; rw [sSup_image]
  exact ((OrderIso.inv M).map_sInf _).symm

@[to_additive]
/--
lemma `sInf_inv` / 引理 `sInf_inv`

English:
lemma sInf_inv
  given: (s : Set M)
  statement: sInf s⁻¹ = (sSup s)⁻¹
  proof: by
  rw [← image_inv_eq_inv]; rw [sInf_image]
  exact ((OrderIso.inv M).map_sSup _).symm

@[to_additive]

中文:
引理 sInf_inv
  条件: (s : 集合 M)
  结论: sInf s⁻¹ = (sSup s)⁻¹
  证明: by
  rw [← image_inv_eq_inv]; rw [sInf_image]
  exact ((OrderIso.inv M).map_sSup _).symm

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, image_inv_eq_inv, map_sSup, sInf_image
-/
lemma sInf_inv (s : Set M) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv]; rw [sInf_image]
  exact ((OrderIso.inv M).map_sSup _).symm

@[to_additive]
/--
lemma `sSup_mul` / 引理 `sSup_mul`

English:
lemma sSup_mul
  statement: sSup (s * t) = sSup s * sSup t
  proof: (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection

@[to_additive]

中文:
引理 sSup_mul
  结论: sSup (s * t) = sSup s * sSup t
  证明: (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, OrderIso.mulRight, mulLeft, mulRight, sSup_image2_eq_sSup_sSup, to_galoisConnection
-/
lemma sSup_mul : sSup (s * t) = sSup s * sSup t :=
  (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection

@[to_additive]
/--
lemma `sInf_mul` / 引理 `sInf_mul`

English:
lemma sInf_mul
  statement: sInf (s * t) = sInf s * sInf t
  proof: (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection

@[to_additive]

中文:
引理 sInf_mul
  结论: sInf (s * t) = sInf s * sInf t
  证明: (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, OrderIso.mulRight, mulLeft, mulRight, sInf_image2_eq_sInf_sInf, symm.to_galoisConnection, to_galoisConnection
-/
lemma sInf_mul : sInf (s * t) = sInf s * sInf t :=
  (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection

@[to_additive]
/--
lemma `sSup_div` / 引理 `sSup_div`

English:
lemma sSup_div
  statement: sSup (s / t) = sSup s / sInf t
  proof: by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]

@[to_additive]

中文:
引理 sSup_div
  结论: sSup (s / t) = sSup s / sInf t
  证明: by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, sSup_inv, sSup_mul, simp_rw
-/
lemma sSup_div : sSup (s / t) = sSup s / sInf t := by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]

@[to_additive]
/--
lemma `sInf_div` / 引理 `sInf_div`

English:
lemma sInf_div
  statement: sInf (s / t) = sInf s / sSup t
  proof: by simp_rw [div_eq_mul_inv, sInf_mul, sInf_inv]

中文:
引理 sInf_div
  结论: sInf (s / t) = sInf s / sSup t
  证明: by simp_rw [div_eq_mul_inv, sInf_mul, sInf_inv]

Depends on / 依赖: div_eq_mul_inv, sInf_inv, sInf_mul, simp_rw
-/
lemma sInf_div : sInf (s / t) = sInf s / sSup t := by simp_rw [div_eq_mul_inv, sInf_mul, sInf_inv]

end Group
end CompleteLattice
