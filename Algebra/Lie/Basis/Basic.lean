/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# Bases of semisimple Lie algebras

In this file we define bases of semisimple Lie algebras. Given an indexing type `ι`, a basis of a
Lie algebra consists of a non-degenerate matrix of integers `A` indexed by `ι × ι` and generators
`h i`, `e i`, `f i` indexed by `ι`, each forming an `sl₂` triple, and satisfying the Chevalley-Serre
relations:
* `⁅h i, h j⁆ = 0`
* `⁅h j, e i⁆ = A i j • e i`
* `⁅h j, f i⁆ = -A i j • f i`
* `⁅e i, f j⁆ = 0` (for `i ≠ j`)

This concept appears not to have a name in the informal literature and so we call it simply a basis.
With further axioms (constraining the structure constants which appear in products of the form
`⁅e i, e j⁆`, `⁅f i, f j⁆`) one obtains the concept of a Weyl or Chevalley basis.
See e.g., [serre1965](Ch. V, §4, §6).

## Main definitions / results:

* `LieAlgebra.Basis`: the concept of a basis for a Lie algebra.
* `LieAlgebra.Basis.cartanMatrix_base_eq`: the matrix of a `LieAlgebra.Basis` is the Cartan matrix
  of the associated based root system.

## TODO

* Show that every semisimple Lie algebra has a basis.
* Define Weyl, Chevalley bases.

-/

@[expose] public section

open Function LieSubalgebra Module Set

noncomputable section

namespace LieAlgebra

/-- A basis for a semisimple Lie algebra distinguishes a natural Cartan subalgebra and a base
for the associated root system. -/
@[ext]
/--
Definition of `Basis` / `Basis` 的定义

English:
structure Basis
  parameters: (ι : Type*) {R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  axioms and operations (13):
    - A : Matrix ι ι Int
    - h : ι -> L
    - e : ι -> L
    - f : ι -> L
    - cartan_eq_lieSpan : H = lieSpan R L (range h)
    - span_ef : lieSpan R L (range e union range f) = ⊤
    - linInd : LinearIndependent R h
    - nondegen : A.Nondegenerate -- TODO Replace with `(b.A.det : R) ≠ 0` to support positive char
    - sl2((i : ι)) : IsSl2Triple (h i) (e i) (f i)
    - lie_h_h((i j : ι)) : ⁅h i, h j⁆ = 0
    - lie_h_e((i j : ι)) : ⁅h j, e i⁆ = A i j • e i
    - lie_h_f((i j : ι)) : ⁅h j, f i⁆ = -A i j • f i
    - lie_e_f_ne((i j : ι) (hij : i != j)) : ⁅e i, f j⁆ = 0

中文:
结构 Basis
  参数: (ι : 类型) {R L : 类型} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  公理与运算 (13 个):
    - A : Matrix ι ι 整数
    - h : ι -> L
    - e : ι -> L
    - f : ι -> L
    - cartan_eq_lieSpan : H = lieSpan R L (range h)
    - span_ef : lieSpan R L (range e union range f) = ⊤
    - linInd : LinearIndependent R h
    - nondegen : A.Nondegenerate -- TODO Replace with `(b.A.det : R) ≠ 0` to support positive char
    - sl2((i : ι)) : IsSl2Triple (h i) (e i) (f i)
    - lie_h_h((i j : ι)) : ⁅h i, h j⁆ = 0
    - lie_h_e((i j : ι)) : ⁅h j, e i⁆ = A i j • e i
    - lie_h_f((i j : ι)) : ⁅h j, f i⁆ = -A i j • f i
    - lie_e_f_ne((i j : ι) (hij : i != j)) : ⁅e i, f j⁆ = 0
-/
structure Basis (ι : Type*) {R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
    (H : LieSubalgebra R L) where
  /-- The Cartan matrix. -/
  A : Matrix ι ι Int
  /-- The basis for the Cartan subalgebra. -/
  h : ι -> L
  /-- The generators of the upper Borel subalgebra. -/
  e : ι -> L
  /-- The generators of the lower Borel subalgebra. -/
  f : ι -> L
  cartan_eq_lieSpan : H = lieSpan R L (range h)
  span_ef : lieSpan R L (range e union range f) = ⊤
  linInd : LinearIndependent R h
  nondegen : A.Nondegenerate -- TODO Replace with `(b.A.det : R) ≠ 0` to support positive char
  sl2 (i : ι) : IsSl2Triple (h i) (e i) (f i)
  lie_h_h (i j : ι) : ⁅h i, h j⁆ = 0
  lie_h_e (i j : ι) : ⁅h j, e i⁆ = A i j • e i
  lie_h_f (i j : ι) : ⁅h j, f i⁆ = -A i j • f i
  lie_e_f_ne (i j : ι) (hij : i != j) : ⁅e i, f j⁆ = 0

namespace Basis

section CommRing

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} (b : Basis ι H)

/--
lemma `A_diag_eq_two` / 引理 `A_diag_eq_two`

English:
lemma A_diag_eq_two
  given: [IsAddTorsionFree L] (i : ι)
  statement: b.A i i = 2
  proof: by
  have : NoZeroSMulDivisors Int L := IsAddTorsionFree.to_noZeroSMulDivisors_int
  have aux : (b.A i i - 2) • b.e i = 0 := by
    rw [sub_smul]; rw [ofNat_smul_eq_nsmul]; rw [← (b.sl2 i).lie_h_e_nsmul]; rw [b.lie_h_e i i]; abel
  rwa [IsAddTorsionFree.zsmul_eq_zero_iff_left (b.sl2 i).e_ne_zero, su

中文:
引理 A_diag_eq_two
  条件: [IsAddTorsionFree L] (i : ι)
  结论: b.A i i = 2
  证明: by
  have : NoZeroSMulDivisors Int L := IsAddTorsionFree.to_noZeroSMulDivisors_int
  have aux : (b.A i i - 2) • b.e i = 0 := by
    rw [sub_smul]; rw [ofNat_smul_eq_nsmul]; rw [← (b.sl2 i).lie_h_e_nsmul]; rw [b.lie_h_e i i]; abel
  rwa [IsAddTorsionFree.zsmul_eq_zero_iff_left (b.sl2 i).e_ne_zero, su
-/
@[simp] lemma A_diag_eq_two [IsAddTorsionFree L] (i : ι) : b.A i i = 2 := by
  have : NoZeroSMulDivisors Int L := IsAddTorsionFree.to_noZeroSMulDivisors_int
  have aux : (b.A i i - 2) • b.e i = 0 := by
    rw [sub_smul]; rw [ofNat_smul_eq_nsmul]; rw [← (b.sl2 i).lie_h_e_nsmul]; rw [b.lie_h_e i i]; abel
  rwa [IsAddTorsionFree.zsmul_eq_zero_iff_left (b.sl2 i).e_ne_zero, sub_eq_zero] at aux

/--
lemma `coe_cartan_eq_span` / 引理 `coe_cartan_eq_span`

English:
lemma coe_cartan_eq_span
  proof: by
  conv_lhs => rw [b.cartan_eq_lieSpan]
  apply coe_lieSpan_eq_span_of_forall_lie_eq_zero
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

include b in

中文:
引理 coe_cartan_eq_span
  证明: by
  conv_lhs => rw [b.cartan_eq_lieSpan]
  apply coe_lieSpan_eq_span_of_forall_lie_eq_zero
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

include b in

Depends on / 依赖: b.cartan_eq_lieSpan, b.lie_h_h, cartan_eq_lieSpan, coe_lieSpan_eq_span_of_forall_lie_eq_zero, conv_lhs, lie_h_h
-/
lemma coe_cartan_eq_span :
    H = Submodule.span R (range b.h) := by
  conv_lhs => rw [b.cartan_eq_lieSpan]
  apply coe_lieSpan_eq_span_of_forall_lie_eq_zero
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

include b in
/--
theorem `isLieAbelian_cartan` / 定理 `isLieAbelian_cartan`

English:
theorem isLieAbelian_cartan
  statement: IsLieAbelian H
  proof: by
  rw [b.cartan_eq_lieSpan]; rw [isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

中文:
定理 isLieAbelian_cartan
  结论: IsLieAbelian H
  证明: by
  rw [b.cartan_eq_lieSpan]; rw [isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

Depends on / 依赖: b.cartan_eq_lieSpan, b.lie_h_h, cartan_eq_lieSpan, isLieAbelian_lieSpan_iff, lie_h_h
-/
theorem isLieAbelian_cartan : IsLieAbelian H := by
  rw [b.cartan_eq_lieSpan]; rw [isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : Basis ι H where
  body: b.A
  h := -b.h
  e := b.f
  f := b.e
  cartan_eq_lieSpan := by
    rw [← neg_range']; rw [lieSpan_neg]
    exact b.cartan_eq_lieSpan
  nondegen := b.nondegen
  linInd := b.linInd.neg
  sl2 i := (b.sl2 i).symm
  lie_h_h i j := by rw [Pi.neg_apply, Pi.neg_apply, neg_lie, lie_neg, b.lie_h_h i j, neg_n

中文:
定义 symm
  签名: : Basis ι H where
  定义体: b.A
  h := -b.h
  e := b.f
  f := b.e
  cartan_eq_lieSpan := by
    rw [← neg_range']; rw [lieSpan_neg]
    exact b.cartan_eq_lieSpan
  nondegen := b.nondegen
  linInd := b.linInd.neg
  sl2 i := (b.sl2 i).symm
  lie_h_h i j := by rw [Pi.neg_apply, Pi.neg_apply, neg_lie, lie_neg, b.lie_h_h i j, neg_n
-/
@[simps -fullyApplied] def symm : Basis ι H where
  A := b.A
  h := -b.h
  e := b.f
  f := b.e
  cartan_eq_lieSpan := by
    rw [← neg_range']; rw [lieSpan_neg]
    exact b.cartan_eq_lieSpan
  nondegen := b.nondegen
  linInd := b.linInd.neg
  sl2 i := (b.sl2 i).symm
  lie_h_h i j := by rw [Pi.neg_apply, Pi.neg_apply, neg_lie, lie_neg, b.lie_h_h i j, neg_neg]
  lie_h_e i j := by rw [Pi.neg_apply, neg_lie, b.lie_h_f i j, neg_smul, neg_neg]
  lie_h_f i j := by rw [Pi.neg_apply, neg_lie, b.lie_h_e, neg_smul]
  lie_e_f_ne i j h := by rw [← lie_skew, neg_eq_zero, b.lie_e_f_ne j i h.symm]
  span_ef := by rw [union_comm, b.span_ef]

/--
lemma `symm_symm` / 引理 `symm_symm`

English:
lemma symm_symm
  statement: b.symm.symm = b
  proof: by aesop

中文:
引理 symm_symm
  结论: b.symm.symm = b
  证明: by aesop
-/
@[simp] lemma symm_symm : b.symm.symm = b := by aesop

/--
Definition of `h'` / `h'` 的定义

English:
definition h'
  signature: (i : ι)
  body: ⟨b.h i, b.cartan_eq_lieSpan ▸ subset_lieSpan mem_range_self i⟩

中文:
定义 h'
  签名: (i : ι)
  定义体: ⟨b.h i, b.cartan_eq_lieSpan ▸ subset_lieSpan mem_range_self i⟩

Depends on / 依赖: b.cartan_eq_lieSpan, cartan_eq_lieSpan, mem_range_self, subset_lieSpan
-/
def h' (i : ι) : H := ⟨b.h i, b.cartan_eq_lieSpan ▸ subset_lieSpan mem_range_self i⟩

/--
lemma `symm_h'` / 引理 `symm_h'`

English:
lemma symm_h'
  given: (i : ι)
  statement: (b.symm.h' i) = -b.h' i
  proof: rfl

中文:
引理 symm_h'
  条件: (i : ι)
  结论: (b.symm.h' i) = -b.h' i
  证明: rfl
-/
@[simp] lemma symm_h' (i : ι) : (b.symm.h' i) = -b.h' i := rfl

/--
lemma `cartan_lie_mem_lieSpan_e` / 引理 `cartan_lie_mem_lieSpan_e`

English:
lemma cartan_lie_mem_lieSpan_e
  statement: {x y : L}
  proof: by
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [← mem_toSubmodule]; rw [b.coe_cartan_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      rw [b.lie_h_e]
apply zsmul_mem subset_lieSpan 

中文:
引理 cartan_lie_mem_lieSpan_e
  结论: {x y : L}
  证明: by
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [← mem_toSubmodule]; rw [b.coe_cartan_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      rw [b.lie_h_e]
apply zsmul_mem subset_lieSpan 
-/
private lemma cartan_lie_mem_lieSpan_e {x y : L}
    (hx : x in H) (hy : y in lieSpan R L (range b.e)) :
    ⁅x, y⁆ in lieSpan R L (range b.e) := by
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [← mem_toSubmodule]; rw [b.coe_cartan_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      rw [b.lie_h_e]
apply zsmul_mem subset_lieSpan mem_range_self i
    | zero => simp
    | add v w _ _ hv hw => simpa using add_mem hv hw
    | smul t v _ hv => simpa using LieSubalgebra.smul_mem _ t hv
  | zero => simp
  | add u v _ _ hu hv => simpa using add_mem hu hv
  | smul t u _ hu => simpa using LieSubalgebra.smul_mem _ t hu
  | lie u v hu hv hu' hv' =>
    rw [leibniz_lie]; rw [← lie_skew _ v]; rw [neg_add_eq_sub]
    exact sub_mem (LieSubalgebra.lie_mem _ hu hv') (LieSubalgebra.lie_mem _ hv hu')

/--
Definition of `borelUpper` / `borelUpper` 的定义

English:
definition borelUpper
  signature: : LieSubmodule R H L where
  body: lieSpan R L range b.e
  lie_mem {x y} hy := by
    obtain ⟨x, hx⟩ := x
    simpa using b.cartan_lie_mem_lieSpan_e hx hy

中文:
定义 borelUpper
  签名: : LieSubmodule R H L where
  定义体: lieSpan R L range b.e
  lie_mem {x y} hy := by
    obtain ⟨x, hx⟩ := x
    simpa using b.cartan_lie_mem_lieSpan_e hx hy

Depends on / 依赖: lieSpan
-/
def borelUpper : LieSubmodule R H L where
__ := lieSpan R L range b.e
  lie_mem {x y} hy := by
    obtain ⟨x, hx⟩ := x
    simpa using b.cartan_lie_mem_lieSpan_e hx hy

/--
Definition of `borelLower` / `borelLower` 的定义

English:
definition borelLower
  signature: : LieSubmodule R H L where
  body: lieSpan R L range b.f
  lie_mem := b.symm.borelUpper.lie_mem

中文:
定义 borelLower
  签名: : LieSubmodule R H L where
  定义体: lieSpan R L range b.f
  lie_mem := b.symm.borelUpper.lie_mem

Depends on / 依赖: lieSpan
-/
def borelLower : LieSubmodule R H L where
__ := lieSpan R L range b.f
  lie_mem := b.symm.borelUpper.lie_mem

/--
lemma `iSup_cartan_borelLower_borelUpper_eq_top_aux` / 引理 `iSup_cartan_borelLower_borelUpper_eq_top_aux`

English:
lemma iSup_cartan_borelLower_borelUpper_eq_top_aux
  proof: by
  have (i : ι) (x : L) (hx : x in lieSpan R L (range b.f)) :
      ⁅b.e i, x⁆ in H.toLieSubmodule ⊔ b.borelLower := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      rcases eq_or_ne i j with rfl | hij
      · rw [(b.sl2 i).lie_e_f]


中文:
引理 iSup_cartan_borelLower_borelUpper_eq_top_aux
  证明: by
  have (i : ι) (x : L) (hx : x in lieSpan R L (range b.f)) :
      ⁅b.e i, x⁆ in H.toLieSubmodule ⊔ b.borelLower := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      rcases eq_or_ne i j with rfl | hij
      · rw [(b.sl2 i).lie_e_f]

-/
private lemma iSup_cartan_borelLower_borelUpper_eq_top_aux
    {y z : L} (hy : y in lieSpan R L (range b.e)) (hz : z in lieSpan R L (range b.f)) :
    ⁅y, z⁆ in H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper := by
  have (i : ι) (x : L) (hx : x in lieSpan R L (range b.f)) :
      ⁅b.e i, x⁆ in H.toLieSubmodule ⊔ b.borelLower := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      rcases eq_or_ne i j with rfl | hij
      · rw [(b.sl2 i).lie_e_f]
        apply LieSubmodule.mem_sup_left
        nth_rw 1 [mem_toLieSubmodule, b.cartan_eq_lieSpan]
exact LieSubalgebra.subset_lieSpan mem_range_self i
      · simp [b.lie_e_f_ne _ _ hij]
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add]; exact add_mem hu hv
    | smul t u _ hu => rw [lie_smul]; exact SMulMemClass.smul_mem t hu
    | lie u v hu hv hu' hv' =>
      obtain ⟨w₁, hw₁, w₂, hw₂, hwu⟩ : exists y in H, exists z in b.borelLower, y + z = ⁅b.e i, u⁆ := by
        simpa only [LieSubmodule.mem_sup] using! hu'
      obtain ⟨w₃, hw₃, w₄, hw₄, hwv⟩ : exists y in H, exists z in b.borelLower, y + z = ⁅b.e i, v⁆ := by
        simpa only [LieSubmodule.mem_sup] using! hv'
      rw [leibniz_lie]; rw [← hwu]; rw [← hwv]; rw [lie_add]; rw [add_lie]; rw [← add_assoc]
      repeat apply add_mem
· exact LieSubmodule.mem_sup_right b.borelLower.lie_mem (x := ⟨w₁, hw₁⟩) hv
· exact LieSubmodule.mem_sup_right LieSubalgebra.lie_mem _ hw₂ hv
      · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right b.borelLower.lie_mem (x := ⟨w₃, hw₃⟩) hu
      · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right LieSubalgebra.lie_mem _ hw₄ hu
  induction hy using lieSpan_induction generalizing z with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
exact LieSubmodule.mem_sup_left this i z hz
  | zero => simp
  | add u v _ _ hu hv => rw [add_lie]; exact add_mem (hu hz) (hv hz)
  | smul t u _ hu => rw [smul_lie]; exact SMulMemClass.smul_mem t (hu hz)
  | lie u v hu hv hu' hv' =>
    rw [lie_lie]
    apply sub_mem
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        existsᵉ (yc in H) (yl in lieSpan R L (range b.f)) (yu in lieSpan R L (range b.e)),
        yc + yl + yu = ⁅v, z⁆ := by simpa [LieSubmodule.mem_sup] using! hv' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hu
      · exact hu' hyl
      · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right LieSubalgebra.lie_mem _ hyu hu
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        existsᵉ (yc in H) (yl in lieSpan R L (range b.f)) (yu in lieSpan R L (range b.e)),
        yc + yl + yu = ⁅u, z⁆ := by simpa [LieSubmodule.mem_sup] using! hu' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hv
      · exact hv' hyl
      · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right LieSubalgebra.lie_mem _ hyu hv

/--
lemma `iSup_cartan_borelLower_borelUpper_eq_top` / 引理 `iSup_cartan_borelLower_borelUpper_eq_top`

English:
lemma iSup_cartan_borelLower_borelUpper_eq_top
  proof: by
  suffices H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper = ⊤ by simpa
  refine eq_top_iff.mpr fun x hx => ?_
  replace hx : x in lieSpan R L (range b.e union range b.f) := by simp [b.span_ef]
  induction hx using lieSpan_induction with
  | mem u hu =>
    rcases (mem_union _ _ _).mpr hu with hu 

中文:
引理 iSup_cartan_borelLower_borelUpper_eq_top
  证明: by
  suffices H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper = ⊤ by simpa
  refine eq_top_iff.mpr fun x hx => ?_
  replace hx : x in lieSpan R L (range b.e union range b.f) := by simp [b.span_ef]
  induction hx using lieSpan_induction with
  | mem u hu =>
    rcases (mem_union _ _ _).mpr hu with hu 

Depends on / 依赖: H.toLieSubmodule, LieSubmodule, LieSubmodule.mem_sup_left, LieSubmodule.mem_sup_right, add_mem, b.borelLower, b.borelUpper, b.span_ef, borelLower, borelUpper, eq_top_iff, eq_top_iff.mpr, lieSpan, lieSpan_induction, mem_sup_left, mem_sup_right, mem_union, replace, span_ef, subset_lieSpan
-/
lemma iSup_cartan_borelLower_borelUpper_eq_top :
    iSup ![H.toLieSubmodule, b.borelLower, b.borelUpper] = ⊤ := by
  suffices H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper = ⊤ by simpa
  refine eq_top_iff.mpr fun x hx => ?_
  replace hx : x in lieSpan R L (range b.e union range b.f) := by simp [b.span_ef]
  induction hx using lieSpan_induction with
  | mem u hu =>
    rcases (mem_union _ _ _).mpr hu with hu | hu
· exact LieSubmodule.mem_sup_right subset_lieSpan hu
· exact LieSubmodule.mem_sup_left LieSubmodule.mem_sup_right subset_lieSpan hu
  | zero => simp
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul t u _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    obtain ⟨yc, hyc, yl, hyl, yu, hyu, rfl⟩ :
        existsᵉ (yc in H) (yl in lieSpan R L (range b.f)) (yu in lieSpan R L (range b.e)),
          yc + yl + yu = u := by simpa [LieSubmodule.mem_sup] using! hu
    obtain ⟨zc, hzc, zl, hzl, zu, hzu, rfl⟩ :
        existsᵉ (zc in H) (zl in lieSpan R L (range b.f)) (zu in lieSpan R L (range b.e)),
          zc + zl + zu = v := by simpa [LieSubmodule.mem_sup] using! hv
    simp only [lie_add, add_lie, ← add_assoc]
    repeat apply add_mem
· exact LieSubmodule.mem_sup_left LieSubmodule.mem_sup_left lie_mem _ hyc hzc
    · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_left LieSubmodule.mem_sup_right
        b.borelLower.lie_mem (x := ⟨zc, hzc⟩) hyl
    · rw [← lie_skew, neg_mem_iff]
exact LieSubmodule.mem_sup_right b.borelUpper.lie_mem (x := ⟨zc, hzc⟩) hyu
· exact LieSubmodule.mem_sup_left LieSubmodule.mem_sup_right
        b.borelLower.lie_mem (x := ⟨yc, hyc⟩) hzl
· exact LieSubmodule.mem_sup_left LieSubmodule.mem_sup_right lie_mem _ hyl hzl
    · exact b.iSup_cartan_borelLower_borelUpper_eq_top_aux hyu hzl
· exact LieSubmodule.mem_sup_right b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hzu
    · rw [← lie_skew, neg_mem_iff]
      exact b.iSup_cartan_borelLower_borelUpper_eq_top_aux hzu hyl
· exact LieSubmodule.mem_sup_right lie_mem _ hyu hzu

variable [Fintype ι]

/--
Definition of `baseSupp` / `baseSupp` 的定义

English:
definition baseSupp
  signature: (i : ι)
  body: ∑ j, b.A i j •
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord j

中文:
定义 baseSupp
  签名: (i : ι)
  定义体: ∑ j, b.A i j •
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord j

Depends on / 依赖: Basis.span, LinearEquiv, LinearEquiv.ofEq, b.coe_cartan_eq_span, b.linInd, coe_cartan_eq_span, linInd
-/
def baseSupp (i : ι) : Dual R H :=
  ∑ j, b.A i j •
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord j

/--
lemma `baseSupp_apply_h'` / 引理 `baseSupp_apply_h'`

English:
lemma baseSupp_apply_h'
  given: (i j : ι)
  proof: by
  classical
  simp only [baseSupp, LinearMap.coe_sum, Finset.sum_apply]
  let e := LinearEquiv.ofEq _ _ b.coe_cartan_eq_span
  let f (k : ι) : R := b.A i k • (Basis.span b.linInd).repr (e <| b.h' j) k
  change ∑ k, f k = _
  have : f = fun k => if j = k then (b.A i k : R) else 0 := by
    have : 

中文:
引理 baseSupp_apply_h'
  条件: (i j : ι)
  证明: by
  classical
  simp only [baseSupp, LinearMap.coe_sum, Finset.sum_apply]
  let e := LinearEquiv.ofEq _ _ b.coe_cartan_eq_span
  let f (k : ι) : R := b.A i k • (Basis.span b.linInd).repr (e <| b.h' j) k
  change ∑ k, f k = _
  have : f = fun k => if j = k then (b.A i k : R) else 0 := by
    have : 
-/
@[simp] lemma baseSupp_apply_h' (i j : ι) :
    b.baseSupp i (b.h' j) = b.A i j := by
  classical
  simp only [baseSupp, LinearMap.coe_sum, Finset.sum_apply]
  let e := LinearEquiv.ofEq _ _ b.coe_cartan_eq_span
  let f (k : ι) : R := b.A i k • (Basis.span b.linInd).repr (e <| b.h' j) k
  change ∑ k, f k = _
  have : f = fun k => if j = k then (b.A i k : R) else 0 := by
    have : (Basis.span b.linInd).repr (e <| b.h' j) = .single j 1 := Basis.span_repr_eq_single _ _
    ext k
    simp [f, this, Finsupp.single_apply]
  simp [this]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `symm_baseSupp` / 引理 `symm_baseSupp`

English:
lemma symm_baseSupp
  proof: by
  let b₁ : Module.Basis ι R H :=
    (Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm
  let b₂ : Module.Basis ι R H :=
    (Basis.span b.linInd.neg).map (LinearEquiv.ofEq _ _ b.symm.coe_cartan_eq_span).symm
  suffices b₁.coord = -b₂.coord by
    ext1 i
    change ∑ j, b.

中文:
引理 symm_baseSupp
  证明: by
  let b₁ : Module.Basis ι R H :=
    (Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm
  let b₂ : Module.Basis ι R H :=
    (Basis.span b.linInd.neg).map (LinearEquiv.ofEq _ _ b.symm.coe_cartan_eq_span).symm
  suffices b₁.coord = -b₂.coord by
    ext1 i
    change ∑ j, b.
-/
@[simp] lemma symm_baseSupp :
    b.symm.baseSupp = -b.baseSupp := by
  let b₁ : Module.Basis ι R H :=
    (Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm
  let b₂ : Module.Basis ι R H :=
    (Basis.span b.linInd.neg).map (LinearEquiv.ofEq _ _ b.symm.coe_cartan_eq_span).symm
  suffices b₁.coord = -b₂.coord by
    ext1 i
    change ∑ j, b.A i j • b₂.coord j = - ∑ j, b.A i j • b₁.coord j
    simp [this]
  simp only [b₁, b₂, Basis.span_neg b.linInd]
  aesop

/--
lemma `linearIndependent_baseSupp` / 引理 `linearIndependent_baseSupp`

English:
lemma linearIndependent_baseSupp
  given: [IsDomain R] [CharZero R]
  proof: by
  classical
  have : ((Int.castRingHom R).mapMatrix b.A).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero]; rw [← RingHom.map_det]
    simpa using! b.nondegen.det_ne_zero
  let v : ι -> Dual R H :=
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).co

中文:
引理 linearIndependent_baseSupp
  条件: [IsDomain R] [CharZero R]
  证明: by
  classical
  have : ((Int.castRingHom R).mapMatrix b.A).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero]; rw [← RingHom.map_det]
    simpa using! b.nondegen.det_ne_zero
  let v : ι -> Dual R H :=
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).co

Depends on / 依赖: Basis.linearIndependent_coord, Basis.span, Int.castRingHom, Int.cast_smul_eq_zsmul, LinearEquiv, LinearEquiv.ofEq, LinearIndependent, Matrix, Matrix.nondegenerate_iff_det_ne_zero, Nondegenerate, RingHom, RingHom.map_det, b.coe_cartan_eq_span, b.linInd, b.nondegen.det_ne_zero, castRingHom, cast_smul_eq_zsmul, classical, coe_cartan_eq_span, det_ne_zero
-/
lemma linearIndependent_baseSupp [IsDomain R] [CharZero R] :
    LinearIndependent R b.baseSupp := by
  classical
  have : ((Int.castRingHom R).mapMatrix b.A).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero]; rw [← RingHom.map_det]
    simpa using! b.nondegen.det_ne_zero
  let v : ι -> Dual R H :=
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord
  have hv : LinearIndependent R v := Basis.linearIndependent_coord _
  simpa [Int.cast_smul_eq_zsmul] using! hv.sum_smul_of_nondegenerate this

/--
lemma `baseSupp_apply_smul_e` / 引理 `baseSupp_apply_smul_e`

English:
lemma baseSupp_apply_smul_e
  given: (i : ι) (x : H)
  proof: by
  obtain ⟨x, hx⟩ := x
  simp only [coe_bracket_of_module]
  have hx' : x in Submodule.span R (range b.h) := by
    rwa [← LieSubalgebra.mem_toSubmodule, b.coe_cartan_eq_span] at hx
  induction hx' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    change b.baseSupp 

中文:
引理 baseSupp_apply_smul_e
  条件: (i : ι) (x : H)
  证明: by
  obtain ⟨x, hx⟩ := x
  simp only [coe_bracket_of_module]
  have hx' : x in Submodule.span R (range b.h) := by
    rwa [← LieSubalgebra.mem_toSubmodule, b.coe_cartan_eq_span] at hx
  induction hx' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    change b.baseSupp 
-/
@[simp] lemma baseSupp_apply_smul_e (i : ι) (x : H) :
    b.baseSupp i x • b.e i = ⁅x, b.e i⁆ := by
  obtain ⟨x, hx⟩ := x
  simp only [coe_bracket_of_module]
  have hx' : x in Submodule.span R (range b.h) := by
    rwa [← LieSubalgebra.mem_toSubmodule, b.coe_cartan_eq_span] at hx
  induction hx' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    change b.baseSupp i (b.h' j) • _ = _
    simp [b.lie_h_e, Int.cast_smul_eq_zsmul]
  | zero => change b.baseSupp i 0 • _ = _; simp
  | add u v hu hv hu' hv' =>
    rw [← coe_cartan_eq_span]; rw [LieSubalgebra.mem_toSubmodule] at hu hv
    rw [← AddMemClass.mk_add_mk _ u v hu hv]
    simp only [map_add, add_smul, add_lie] at hu' hv' ⊢
    rw [hu']; rw [hv']
  | smul t u hu hv' =>
    rw [← coe_cartan_eq_span]; rw [LieSubalgebra.mem_toSubmodule] at hu
    rw [← SetLike.mk_smul_mk _ t u hu]; rw [map_smul]; rw [smul_assoc]; rw [hv']; rw [smul_lie]

/--
lemma `baseSupp_apply_smul_f` / 引理 `baseSupp_apply_smul_f`

English:
lemma baseSupp_apply_smul_f
  given: (i : ι) (x : H)
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_smul]; rw [← LinearMap.neg_apply]
  have := b.symm.baseSupp_apply_smul_e i x
  simp only [symm_baseSupp, Pi.neg_apply, symm_e] at this
  exact this

中文:
引理 baseSupp_apply_smul_f
  条件: (i : ι) (x : H)
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_smul]; rw [← LinearMap.neg_apply]
  have := b.symm.baseSupp_apply_smul_e i x
  simp only [symm_baseSupp, Pi.neg_apply, symm_e] at this
  exact this
-/
@[simp] lemma baseSupp_apply_smul_f (i : ι) (x : H) :
    b.baseSupp i x • b.f i = -⁅x, b.f i⁆ := by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_smul]; rw [← LinearMap.neg_apply]
  have := b.symm.baseSupp_apply_smul_e i x
  simp only [symm_baseSupp, Pi.neg_apply, symm_e] at this
  exact this

variable [IsDomain R] [CharZero R]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `borelUpper_le_biSup` / 引理 `borelUpper_le_biSup`

English:
lemma borelUpper_le_biSup
  proof: b.isLieAbelian_cartan
    b.borelUpper <= ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) := by
  let := b.isLieAbelian_cartan
  classical
  intro x hx
  replace hx : x in lieSpan R L (range b.e) := by simpa [borelUpper] using hx
  induction hx using lieSpan_induction with
  | m

中文:
引理 borelUpper_le_biSup
  证明: b.isLieAbelian_cartan
    b.borelUpper <= ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) := by
  let := b.isLieAbelian_cartan
  classical
  intro x hx
  replace hx : x in lieSpan R L (range b.e) := by simpa [borelUpper] using hx
  induction hx using lieSpan_induction with
  | m

Depends on / 依赖: b.isLieAbelian_cartan, isLieAbelian_cartan
-/
lemma borelUpper_le_biSup :
    letI := b.isLieAbelian_cartan
    b.borelUpper <= ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) := by
  let := b.isLieAbelian_cartan
  classical
  intro x hx
  replace hx : x in lieSpan R L (range b.e) := by simpa [borelUpper] using hx
  induction hx using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    apply LieSubmodule.mem_iSup_of_mem (Pi.single i 1)
    simp only [ne_eq, Pi.single_eq_zero_iff, one_ne_zero, not_false_eq_true, nsmul_eq_mul, iSup_pos,
      LieModule.mem_genWeightSpace, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply,
      Subtype.forall, toEnd_mk]
    exact fun y hy => ⟨1, by simp [Pi.single_apply]⟩
  | zero => simp
  | add _ _ _ _ hu hv => exact add_mem hu hv
  | smul t _ _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    let s : Set (H -> R) := {χ | exists n : ι -> Nat, n != 0 ∧ χ = ∑ i, n i • b.baseSupp i}
    have hs : forall χ₁ in s, forall χ₂ in s, χ₁ + χ₂ in s := by
      rintro - ⟨n₁, hn₁, rfl⟩ - ⟨n₂, hn₂, rfl⟩
      refine ⟨n₁ + n₂, by simp [hn₁], ?_⟩
      ext; simp [add_smul, Finset.sum_add_distrib]
    let e : {n : ι -> Nat | n != 0} ≃ s :=
.ofBijective (fun n => ⟨∑ i, n.val i • b.baseSupp i, n.val, n.property, by ext; simp⟩) by
      refine ⟨fun n₁ n₂ h => ?_, fun χ => ?_⟩
      · ext i
        have := b.linearIndependent_baseSupp.restrict_scalars' Nat
        refine Fintype.linearIndependent_iffₛ.mp this n₁ n₂ ?_ i
        ext v
        rw [Subtype.mk.injEq] at h
        simpa using congr_fun h v
      · use ⟨χ.property.choose, χ.property.choose_spec.1⟩
        ext i
        simpa using congr_fun χ.property.choose_spec.2.symm i
    replace hu : u in ⨆ χ, ⨆ (_ : χ in s), rootSpace H χ := by
      convert! hu; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    replace hv : v in ⨆ χ, ⨆ (_ : χ in s), rootSpace H χ := by
      convert! hv; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    convert! mem_biSup_genWeightSpace_of hs hu hv
    rw [iSup_subtype']; rw [iSup_subtype']; rw [← e.iSup_comp]; rfl

/--
lemma `borelLower_le_biSup` / 引理 `borelLower_le_biSup`

English:
lemma borelLower_le_biSup
  proof: b.isLieAbelian_cartan
    b.borelLower <= ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) := by
  simpa only [symm_baseSupp] using! b.symm.borelUpper_le_biSup

中文:
引理 borelLower_le_biSup
  证明: b.isLieAbelian_cartan
    b.borelLower <= ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) := by
  simpa only [symm_baseSupp] using! b.symm.borelUpper_le_biSup

Depends on / 依赖: b.isLieAbelian_cartan, isLieAbelian_cartan
-/
lemma borelLower_le_biSup :
    letI := b.isLieAbelian_cartan
    b.borelLower <= ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) := by
  simpa only [symm_baseSupp] using! b.symm.borelUpper_le_biSup

/--
lemma `cartan_borelLower_borelUpper_le` / 引理 `cartan_borelLower_borelUpper_le`

English:
lemma cartan_borelLower_borelUpper_le
  proof: b.isLieAbelian_cartan
    letI U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i)
    ![H.toLieSubmodule, b.borelLower, b.borelUpper] <= ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_c

中文:
引理 cartan_borelLower_borelUpper_le
  证明: b.isLieAbelian_cartan
    letI U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i)
    ![H.toLieSubmodule, b.borelLower, b.borelUpper] <= ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_c
-/
private lemma cartan_borelLower_borelUpper_le :
    letI := b.isLieAbelian_cartan
    letI U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i)
    ![H.toLieSubmodule, b.borelLower, b.borelUpper] <= ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  intro i
  fin_cases i
  · exact toLieSubmodule_le_rootSpace_zero R L H
  · exact b.borelLower_le_biSup
  · exact b.borelUpper_le_biSup

variable [IsTorsionFree R L]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `iSupIndep_rootSpace` / 引理 `iSupIndep_rootSpace`

English:
lemma iSupIndep_rootSpace
  proof: b.isLieAbelian_cartan
    letI U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i)
    iSupIndep ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  set U := ⨆ (n : ι -> Nat) (_ : n 

中文:
引理 iSupIndep_rootSpace
  证明: b.isLieAbelian_cartan
    letI U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i)
    iSupIndep ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  set U := ⨆ (n : ι -> Nat) (_ : n 

Depends on / 依赖: b.isLieAbelian_cartan, isLieAbelian_cartan
-/
lemma iSupIndep_rootSpace :
    letI := b.isLieAbelian_cartan
    letI U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i)
    iSupIndep ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  set U := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) with hU
  set V := ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) with hV
  set s0 : Set (H -> R) := {0} with hs0
  set sU : Set (H -> R) := {f | exists n : ι -> Nat, n != 0 ∧ f = ∑ i, n i • (-b.baseSupp) i} with hsU
  set sV : Set (H -> R) := {f | exists n : ι -> Nat, n != 0 ∧ f = ∑ i, n i • b.baseSupp i} with hsV
  have hs0' : rootSpace H 0 = ⨆ i in s0, LieModule.genWeightSpace L i := by simp [hs0]
  have hsU' : U = ⨆ i in sU, LieModule.genWeightSpace L i := by
    simp only [hU, hsU, mem_ofPred_eq, iSup_exists, iSup_and, iSup_comm (ι := H -> R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hsV' : V = ⨆ i in sV, LieModule.genWeightSpace L i := by
    simp only [hV, hsV, mem_ofPred_eq, iSup_exists, iSup_and, iSup_comm (ι := H -> R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hU0 : Disjoint s0 sU := by
    suffices forall g in sU, g != 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg => ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : exists n : ι -> Nat, n != 0 ∧ g = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hg
    rw [neg_eq_zero]; rw [LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
exact hn funext fun i => by simpa using this i
  have hV0 : Disjoint s0 sV := by
    suffices forall g in sV, g != 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg => ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : exists n : ι -> Nat, n != 0 ∧ g = ∑ i, n i • b.baseSupp i := by
      simpa [hsV] using hg
    rw [LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
exact hn funext fun i => by simpa using this i
  have hUV : Disjoint sU sV := by
    refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg => ?_
    rintro rfl
    obtain ⟨n, hn, hn'⟩ : exists n : ι -> Nat, n != 0 ∧ f = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hf
    obtain ⟨m, hm, rfl⟩ : exists m : ι -> Nat, m != 0 ∧ f = ∑ i, m i • b.baseSupp i := by
      simpa [hsV] using hg
    replace hn' : ∑ i, (((↑) : Nat -> R) ∘ (m + n)) i • b.baseSupp i = 0 := by
      rw [eq_neg_iff_add_eq_zero] at hn'
      change ⇑(∑ i, m i • b.baseSupp i + ∑ i, n i • b.baseSupp i) = 0 at hn'
      simp_rw [LinearMap.coe_zero_iff, ← Finset.sum_add_distrib, ← add_smul, ← Pi.add_apply,
        ← Nat.cast_smul_eq_nsmul R] at hn'
      exact hn'
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ (m + n)) hn'
refine hn funext fun i => ?_
    specialize this i
    rw [comp_apply]; rw [Nat.cast_eq_zero]; rw [Pi.add_apply]; rw [Nat.add_eq_zero_iff] at this
    simpa using this.2
  have key := LieModule.iSupIndep_genWeightSpace R H L
  have h₀ : Disjoint (rootSpace H 0) (U ⊔ V) := by
    convert! key.disjoint_biSup_biSup (hU0.union_right hV0)
    rw [iSup_union]; rw [hsU']; rw [hsV']
  have h₁ : Disjoint U (V ⊔ rootSpace H 0) := by
    convert! key.disjoint_biSup_biSup (hUV.union_right hU0.symm)
    rw [iSup_union]; rw [hs0']; rw [hsV']
  have h₂ : Disjoint V (rootSpace H 0 ⊔ U) := by
    convert! key.disjoint_biSup_biSup (Disjoint.union_left hV0 hUV).symm
    rw [iSup_union]; rw [hs0']; rw [hsU']
  simp [iSupIndep_fin_three, h₀, h₁, h₂]

set_option linter.unusedFintypeInType false in
/--
lemma `cartan_eq` / 引理 `cartan_eq`

English:
lemma cartan_eq
  proof: b.isLieAbelian_cartan
    H.toLieSubmodule = rootSpace H 0 :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 0

中文:
引理 cartan_eq
  证明: b.isLieAbelian_cartan
    H.toLieSubmodule = rootSpace H 0 :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 0

Depends on / 依赖: b.isLieAbelian_cartan, isLieAbelian_cartan
-/
lemma cartan_eq :
    letI := b.isLieAbelian_cartan
    H.toLieSubmodule = rootSpace H 0 :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 0

/--
lemma `borelLower_eq` / 引理 `borelLower_eq`

English:
lemma borelLower_eq
  proof: b.isLieAbelian_cartan
    b.borelLower = ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 1

中文:
引理 borelLower_eq
  证明: b.isLieAbelian_cartan
    b.borelLower = ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 1

Depends on / 依赖: b.isLieAbelian_cartan, isLieAbelian_cartan
-/
lemma borelLower_eq :
    letI := b.isLieAbelian_cartan
    b.borelLower = ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 1

/--
lemma `borelUpper_eq` / 引理 `borelUpper_eq`

English:
lemma borelUpper_eq
  proof: b.isLieAbelian_cartan
    b.borelUpper = ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 2

中文:
引理 borelUpper_eq
  证明: b.isLieAbelian_cartan
    b.borelUpper = ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 2

Depends on / 依赖: b.isLieAbelian_cartan, isLieAbelian_cartan
-/
lemma borelUpper_eq :
    letI := b.isLieAbelian_cartan
    b.borelUpper = ⨆ (n : ι -> Nat) (_ : n != 0), rootSpace H (∑ i, n i • b.baseSupp i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 2

set_option linter.unusedFintypeInType false in
include b in
/--
lemma `isCartanSubalgebra` / 引理 `isCartanSubalgebra`

English:
lemma isCartanSubalgebra
  given: [IsNoetherian R L]
  statement: H.IsCartanSubalgebra
  proof: by
  let := b.isLieAbelian_cartan
  rw [← eq_rootSpace_zero_iff_isCartan]; rw [b.cartan_eq]

中文:
引理 isCartanSubalgebra
  条件: [IsNoetherian R L]
  结论: H.IsCartanSubalgebra
  证明: by
  let := b.isLieAbelian_cartan
  rw [← eq_rootSpace_zero_iff_isCartan]; rw [b.cartan_eq]

Depends on / 依赖: b.cartan_eq, b.isLieAbelian_cartan, cartan_eq, eq_rootSpace_zero_iff_isCartan, isLieAbelian_cartan
-/
lemma isCartanSubalgebra [IsNoetherian R L] : H.IsCartanSubalgebra := by
  let := b.isLieAbelian_cartan
  rw [← eq_rootSpace_zero_iff_isCartan]; rw [b.cartan_eq]

end CommRing

end Basis

end LieAlgebra
