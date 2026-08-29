/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
- `transferCenterPow`: The transfer homomorphism `G →* center G`.

## Main results
- `transferCenterPow_apply`:
  The transfer homomorphism `G →* center G` is given by `g ↦ g ^ (center G).index`.
- `ker_transferSylow_isComplement'`: Burnside's transfer (or normal `p`-complement) theorem:
  If `hP : N(P) ≤ C(P)`, then `(transfer P hP).ker` is a normal `p`-complement.
-/

@[expose] public noncomputable section


variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A] (ϕ : H ->* A)

namespace Subgroup

namespace leftTransversals

open Finset MulAction

open scoped Pointwise

variable (R S T : H.LeftTransversal) [FiniteIndex H]

/-- The difference of two left transversals -/
@[to_additive /-- The difference of two left transversals -/]
/--
Definition of `diff` / `diff` 的定义

English:
definition diff
  signature: : A
  body: let α := S.2.leftQuotientEquiv
  let β := T.2.leftQuotientEquiv
  let _ := H.fintypeQuotientOfFiniteIndex
  ∏ q : G ⧸ H, ϕ
      ⟨(α q : G)⁻¹ * β q,
QuotientGroup.leftRel_apply.mp
          Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]

中文:
定义 diff
  签名: : A
  定义体: let α := S.2.leftQuotientEquiv
  let β := T.2.leftQuotientEquiv
  let _ := H.fintypeQuotientOfFiniteIndex
  ∏ q : G ⧸ H, ϕ
      ⟨(α q : G)⁻¹ * β q,
QuotientGroup.leftRel_apply.mp
          Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]

Depends on / 依赖: H.fintypeQuotientOfFiniteIndex, Quotient, Quotient.exact, QuotientGroup, QuotientGroup.leftRel_apply.mp, fintypeQuotientOfFiniteIndex, leftQuotientEquiv, leftRel_apply, symm_apply_apply
-/
def diff : A :=
  let α := S.2.leftQuotientEquiv
  let β := T.2.leftQuotientEquiv
  let _ := H.fintypeQuotientOfFiniteIndex
  ∏ q : G ⧸ H, ϕ
      ⟨(α q : G)⁻¹ * β q,
QuotientGroup.leftRel_apply.mp
          Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]
/--
theorem `diff_mul_diff` / 定理 `diff_mul_diff`

English:
theorem diff_mul_diff
  statement: diff ϕ R S * diff ϕ S T = diff ϕ R T
  proof: prod_mul_distrib.symm.trans
    (prod_congr rfl fun q _ =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by simp_rw [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left])))

@[to_additive]

中文:
定理 diff_mul_diff
  结论: diff ϕ R S * diff ϕ S T = diff ϕ R T
  证明: prod_mul_distrib.symm.trans
    (prod_congr rfl fun q _ =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by simp_rw [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left])))

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext_iff, coe_mul, congr_arg, ext_iff, map_mul, mul_assoc, mul_inv_cancel_left, prod_congr, prod_mul_distrib, prod_mul_distrib.symm.trans, simp_rw, symm.trans
-/
theorem diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
  prod_mul_distrib.symm.trans
    (prod_congr rfl fun q _ =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by simp_rw [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left])))

@[to_additive]
/--
theorem `diff_self` / 定理 `diff_self`

English:
theorem diff_self
  statement: diff ϕ T T = 1
  proof: mul_eq_left.mp (diff_mul_diff ϕ T T T)

@[to_additive]

中文:
定理 diff_self
  结论: diff ϕ T T = 1
  证明: mul_eq_left.mp (diff_mul_diff ϕ T T T)

@[to_additive]

Depends on / 依赖: diff_mul_diff, mul_eq_left, mul_eq_left.mp
-/
theorem diff_self : diff ϕ T T = 1 :=
  mul_eq_left.mp (diff_mul_diff ϕ T T T)

@[to_additive]
/--
theorem `diff_inv` / 定理 `diff_inv`

English:
theorem diff_inv
  statement: (diff ϕ S T)⁻¹ = diff ϕ T S
  proof: inv_eq_of_mul_eq_one_right (diff_mul_diff ϕ S T S).trans diff_self ϕ S

@[to_additive]

中文:
定理 diff_inv
  结论: (diff ϕ S T)⁻¹ = diff ϕ T S
  证明: inv_eq_of_mul_eq_one_right (diff_mul_diff ϕ S T S).trans diff_self ϕ S

@[to_additive]

Depends on / 依赖: diff_mul_diff, diff_self, inv_eq_of_mul_eq_one_right
-/
theorem diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one_right (diff_mul_diff ϕ S T S).trans diff_self ϕ S

@[to_additive]
/--
theorem `smul_diff_smul` / 定理 `smul_diff_smul`

English:
theorem smul_diff_smul
  given: (g : G)
  statement: diff ϕ (g • S) (g • T) = diff ϕ S T
  proof: let _ := H.fintypeQuotientOfFiniteIndex
  Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun _ => by
    simp only [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, toPerm_symm_apply]

中文:
定理 smul_diff_smul
  条件: (g : G)
  结论: diff ϕ (g • S) (g • T) = diff ϕ S T
  证明: let _ := H.fintypeQuotientOfFiniteIndex
  Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun _ => by
    simp only [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, toPerm_symm_apply]

Depends on / 依赖: Fintype, Fintype.prod_equiv, H.fintypeQuotientOfFiniteIndex, MulAction, MulAction.toPerm, fintypeQuotientOfFiniteIndex, inv_mul_cancel_left, mul_assoc, mul_inv_rev, prod_equiv, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, toPerm, toPerm_symm_apply
-/
theorem smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
  let _ := H.fintypeQuotientOfFiniteIndex
  Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun _ => by
    simp only [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, toPerm_symm_apply]

end leftTransversals

open Equiv Function MulAction ZMod

variable (g : G)

variable (H) in
/--
Definition of `transferFunction` / `transferFunction` 的定义

English:
definition transferFunction
  signature: : G ⧸ H -> G
  body: fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) * (quotientEquivSigmaZMod H g q).1.out.out

中文:
定义 transferFunction
  签名: : G ⧸ H -> G
  定义体: fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) * (quotientEquivSigmaZMod H g q).1.out.out
-/
def transferFunction : G ⧸ H -> G := fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) * (quotientEquivSigmaZMod H g q).1.out.out

/--
lemma `transferFunction_apply` / 引理 `transferFunction_apply`

English:
lemma transferFunction_apply
  given: (q : G ⧸ H)
  proof: rfl

中文:
引理 transferFunction_apply
  条件: (q : G ⧸ H)
  证明: rfl
-/
lemma transferFunction_apply (q : G ⧸ H) :
    transferFunction H g q =
      g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) *
        (quotientEquivSigmaZMod H g q).1.out.out := rfl

/--
lemma `coe_transferFunction` / 引理 `coe_transferFunction`

English:
lemma coe_transferFunction
  given: (q : G ⧸ H)
  statement: ↑(transferFunction H g q) = q
  proof: by
  rw [transferFunction_apply]; rw [← smul_eq_mul]; rw [Quotient.coe_smul_out]; rw [← quotientEquivSigmaZMod_symm_apply]; rw [Sigma.eta]; rw [symm_apply_apply]

中文:
引理 coe_transferFunction
  条件: (q : G ⧸ H)
  结论: ↑(transferFunction H g q) = q
  证明: by
  rw [transferFunction_apply]; rw [← smul_eq_mul]; rw [Quotient.coe_smul_out]; rw [← quotientEquivSigmaZMod_symm_apply]; rw [Sigma.eta]; rw [symm_apply_apply]

Depends on / 依赖: Quotient, Quotient.coe_smul_out, Sigma.eta, coe_smul_out, quotientEquivSigmaZMod_symm_apply, smul_eq_mul, symm_apply_apply, transferFunction_apply
-/
lemma coe_transferFunction (q : G ⧸ H) : ↑(transferFunction H g q) = q := by
  rw [transferFunction_apply]; rw [← smul_eq_mul]; rw [Quotient.coe_smul_out]; rw [← quotientEquivSigmaZMod_symm_apply]; rw [Sigma.eta]; rw [symm_apply_apply]

variable (H) in
/--
Definition of `transferSet` / `transferSet` 的定义

English:
definition transferSet
  signature: : Set G
  body: Set.range (transferFunction H g)

中文:
定义 transferSet
  签名: : 集合 G
  定义体: Set.range (transferFunction H g)

Depends on / 依赖: Set.range, transferFunction
-/
def transferSet : Set G := Set.range (transferFunction H g)

/--
lemma `mem_transferSet` / 引理 `mem_transferSet`

English:
lemma mem_transferSet
  given: (q : G ⧸ H)
  statement: transferFunction H g q in transferSet H g
  proof: ⟨q, rfl⟩

中文:
引理 mem_transferSet
  条件: (q : G ⧸ H)
  结论: transferFunction H g q in transferSet H g
  证明: ⟨q, rfl⟩
-/
lemma mem_transferSet (q : G ⧸ H) : transferFunction H g q in transferSet H g := ⟨q, rfl⟩

variable (H) in
/--
Definition of `transferTransversal` / `transferTransversal` 的定义

English:
definition transferTransversal
  signature: : H.LeftTransversal
  body: ⟨transferSet H g, isComplement_range_left (coe_transferFunction g)⟩

中文:
定义 transferTransversal
  签名: : H.LeftTransversal
  定义体: ⟨transferSet H g, isComplement_range_left (coe_transferFunction g)⟩

Depends on / 依赖: coe_transferFunction, isComplement_range_left, transferSet
-/
def transferTransversal : H.LeftTransversal :=
  ⟨transferSet H g, isComplement_range_left (coe_transferFunction g)⟩

/--
lemma `transferTransversal_apply` / 引理 `transferTransversal_apply`

English:
lemma transferTransversal_apply
  given: (q : G ⧸ H)
  proof: IsComplement.leftQuotientEquiv_apply (coe_transferFunction g) q

中文:
引理 transferTransversal_apply
  条件: (q : G ⧸ H)
  证明: IsComplement.leftQuotientEquiv_apply (coe_transferFunction g) q

Depends on / 依赖: IsComplement, IsComplement.leftQuotientEquiv_apply, coe_transferFunction, leftQuotientEquiv_apply
-/
lemma transferTransversal_apply (q : G ⧸ H) :
    ↑((transferTransversal H g).2.leftQuotientEquiv q) = transferFunction H g q :=
  IsComplement.leftQuotientEquiv_apply (coe_transferFunction g) q

/--
lemma `transferTransversal_apply'` / 引理 `transferTransversal_apply'`

English:
lemma transferTransversal_apply'
  statement: (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
  proof: by
  rw [transferTransversal_apply]; rw [transferFunction_apply]; rw [← quotientEquivSigmaZMod_symm_apply]; rw [apply_symm_apply]

中文:
引理 transferTransversal_apply'
  结论: (q : orbitRel.商 (zpowers g) (G ⧸ H))
  证明: by
  rw [transferTransversal_apply]; rw [transferFunction_apply]; rw [← quotientEquivSigmaZMod_symm_apply]; rw [apply_symm_apply]

Depends on / 依赖: apply_symm_apply, quotientEquivSigmaZMod_symm_apply, transferFunction_apply, transferTransversal_apply
-/
lemma transferTransversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑((transferTransversal H g).2.leftQuotientEquiv (g ^ (cast k : Int) • q.out)) =
      g ^ (cast k : Int) * q.out.out := by
  rw [transferTransversal_apply]; rw [transferFunction_apply]; rw [← quotientEquivSigmaZMod_symm_apply]; rw [apply_symm_apply]

/--
lemma `transferTransversal_apply''` / 引理 `transferTransversal_apply''`

English:
lemma transferTransversal_apply''
  statement: (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
  proof: by
  rw [smul_apply_eq_smul_apply_inv_smul]; rw [transferTransversal_apply]; rw [transferFunction_apply]; rw [←
    mul_smul]; rw [← zpow_neg_one]; rw [← zpow_add]; rw [quotientEquivSigmaZMod_apply]; rw [smul_eq_mul]; rw [← mul_assoc]; rw [← zpow_one_add]; rw [Int.cast_add]; rw [Int.cast_neg]; rw [Int.cast_one]; rw [intCast_cast]; rw [cast_id']; rw [id]; rw [←
    sub_eq_neg_add]; rw [cast_sub_one]; rw [add_sub_cancel]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, zpow_natCast]
  · rw [if_neg hk, if_neg hk]

中文:
引理 transferTransversal_apply''
  结论: (q : orbitRel.商 (zpowers g) (G ⧸ H))
  证明: by
  rw [smul_apply_eq_smul_apply_inv_smul]; rw [transferTransversal_apply]; rw [transferFunction_apply]; rw [←
    mul_smul]; rw [← zpow_neg_one]; rw [← zpow_add]; rw [quotientEquivSigmaZMod_apply]; rw [smul_eq_mul]; rw [← mul_assoc]; rw [← zpow_one_add]; rw [Int.cast_add]; rw [Int.cast_neg]; rw [Int.cast_one]; rw [intCast_cast]; rw [cast_id']; rw [id]; rw [←
    sub_eq_neg_add]; rw [cast_sub_one]; rw [add_sub_cancel]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, zpow_natCast]
  · rw [if_neg hk, if_neg hk]

Depends on / 依赖: Int.cast_add, Int.cast_neg, Int.cast_one, add_sub_cancel, cast_add, cast_id, cast_neg, cast_one, cast_sub_one, if_neg, if_pos, intCast_cast, mul_assoc, mul_smul, quotientEquivSigmaZMod_apply, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, sub_eq_neg_add, transferFunction_apply, transferTransversal_apply
-/
lemma transferTransversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑((g • transferTransversal H g).2.leftQuotientEquiv (g ^ (cast k : Int) • q.out)) =
      if k = 0 then g ^ minimalPeriod (g • ·) q.out * q.out.out
      else g ^ (cast k : Int) * q.out.out := by
  rw [smul_apply_eq_smul_apply_inv_smul]; rw [transferTransversal_apply]; rw [transferFunction_apply]; rw [←
    mul_smul]; rw [← zpow_neg_one]; rw [← zpow_add]; rw [quotientEquivSigmaZMod_apply]; rw [smul_eq_mul]; rw [← mul_assoc]; rw [← zpow_one_add]; rw [Int.cast_add]; rw [Int.cast_neg]; rw [Int.cast_one]; rw [intCast_cast]; rw [cast_id']; rw [id]; rw [←
    sub_eq_neg_add]; rw [cast_sub_one]; rw [add_sub_cancel]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, zpow_natCast]
  · rw [if_neg hk, if_neg hk]

end Subgroup

namespace MonoidHom

open MulAction Subgroup Subgroup.leftTransversals

/-- Given `ϕ : H →* A` from `H : Subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive /-- Given `ϕ : H →+ A` from `H : AddSubgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`. -/]
/--
Definition of `transfer` / `transfer` 的定义

English:
definition transfer
  signature: [FiniteIndex H]
  body: let T : H.LeftTransversal := default
  { toFun := fun g => diff ϕ T (g • T)
    map_one' := by rw [one_smul, diff_self]
    map_mul' := fun g h => by rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

中文:
定义 transfer
  签名: [FiniteIndex H]
  定义体: let T : H.LeftTransversal := default
  { toFun := fun g => diff ϕ T (g • T)
    map_one' := by rw [one_smul, diff_self]
    map_mul' := fun g h => by rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

Depends on / 依赖: H.LeftTransversal, LeftTransversal, diff_mul_diff, diff_self, map_mul, map_one, mul_smul, one_smul, smul_diff_smul
-/
def transfer [FiniteIndex H] : G ->* A :=
  let T : H.LeftTransversal := default
  { toFun := fun g => diff ϕ T (g • T)
    map_one' := by rw [one_smul, diff_self]
    map_mul' := fun g h => by rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

variable (T : H.LeftTransversal)

@[to_additive]
/--
theorem `transfer_def` / 定理 `transfer_def`

English:
theorem transfer_def
  given: [FiniteIndex H] (g : G)
  statement: transfer ϕ g = diff ϕ T (g • T)
  proof: by
  rw [transfer]; rw [← diff_mul_diff]; rw [← smul_diff_smul]; rw [mul_comm]; rw [diff_mul_diff] <;> rfl

中文:
定理 transfer_def
  条件: [FiniteIndex H] (g : G)
  结论: transfer ϕ g = diff ϕ T (g • T)
  证明: by
  rw [transfer]; rw [← diff_mul_diff]; rw [← smul_diff_smul]; rw [mul_comm]; rw [diff_mul_diff] <;> rfl

Depends on / 依赖: diff_mul_diff, mul_comm, smul_diff_smul, transfer
-/
theorem transfer_def [FiniteIndex H] (g : G) : transfer ϕ g = diff ϕ T (g • T) := by
  rw [transfer]; rw [← diff_mul_diff]; rw [← smul_diff_smul]; rw [mul_comm]; rw [diff_mul_diff] <;> rfl

/--
theorem `transfer_eq_prod_quotient_orbitRel_zpowers_quot` / 定理 `transfer_eq_prod_quotient_orbitRel_zpowers_quot`

English:
theorem transfer_eq_prod_quotient_orbitRel_zpowers_quot
  statement: [FiniteIndex H] (g : G)
  proof: by
  let := H.fintypeQuotientOfFiniteIndex
  calc
    transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transferTransversal H g) g
    _ = _ := ((quotientEquivSigmaZMod H g).symm.prod_comp _).symm
    _ = _ := Finset.prod_sigma _ _ _
    _ = _ := by
      refine Fintype.prod_congr _ _ (fun q => ?_)
      simp only [quotientEquivSigmaZMod_symm_apply, transferTransversal_apply',
        transferTransversal_apply'']
      rw [Fintype.prod_eq_single (0 : ZMod (Function.minimalPeriod (g • ·) q.out)) _]
      · simp only [if_pos, ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
      · intro k hk
        simp only [if_neg hk, inv_mul_cancel]
        exact map_one ϕ

中文:
定理 transfer_eq_prod_quotient_orbitRel_zpowers_quot
  结论: [FiniteIndex H] (g : G)
  证明: by
  let := H.fintypeQuotientOfFiniteIndex
  calc
    transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transferTransversal H g) g
    _ = _ := ((quotientEquivSigmaZMod H g).symm.prod_comp _).symm
    _ = _ := Finset.prod_sigma _ _ _
    _ = _ := by
      refine Fintype.prod_congr _ _ (fun q => ?_)
      simp only [quotientEquivSigmaZMod_symm_apply, transferTransversal_apply',
        transferTransversal_apply'']
      rw [Fintype.prod_eq_single (0 : ZMod (Function.minimalPeriod (g • ·) q.out)) _]
      · simp only [if_pos, ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
      · intro k hk
        simp only [if_neg hk, inv_mul_cancel]
        exact map_one ϕ

Depends on / 依赖: Finset, Finset.prod_sigma, Fintype, Fintype.prod_congr, Fintype.prod_eq_single, Function, Function.minimalPeriod, H.fintypeQuotientOfFiniteIndex, ZMod.cast_zero, cast_zero, fintypeQuotientOfFiniteIndex, if_pos, minimalPeriod, prod_comp, prod_congr, prod_eq_single, prod_sigma, q.out, quotientEquivSigmaZMod, quotientEquivSigmaZMod_symm_apply
-/
theorem transfer_eq_prod_quotient_orbitRel_zpowers_quot [FiniteIndex H] (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] :
    transfer ϕ g =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ H)),
        ϕ
          ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem H g q.out⟩ := by
  let := H.fintypeQuotientOfFiniteIndex
  calc
    transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transferTransversal H g) g
    _ = _ := ((quotientEquivSigmaZMod H g).symm.prod_comp _).symm
    _ = _ := Finset.prod_sigma _ _ _
    _ = _ := by
      refine Fintype.prod_congr _ _ (fun q => ?_)
      simp only [quotientEquivSigmaZMod_symm_apply, transferTransversal_apply',
        transferTransversal_apply'']
      rw [Fintype.prod_eq_single (0 : ZMod (Function.minimalPeriod (g • ·) q.out)) _]
      · simp only [if_pos, ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
      · intro k hk
        simp only [if_neg hk, inv_mul_cancel]
        exact map_one ϕ

open scoped IsMulCommutative in
/--
theorem `transfer_eq_pow_aux` / 定理 `transfer_eq_pow_aux`

English:
theorem transfer_eq_pow_aux
  statement: (g : G)
  proof: by
  by_cases hH : H.index = 0
  · rw [hH, pow_zero]
    exact H.one_mem
  let := fintypeOfIndexNeZero hH
  classical
    replace key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g ^ k in H := fun k g₀ hk =>
      (congr_arg (· in H) (key k g₀ hk)).mp hk
    replace key : forall q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q in H := fun q =>
      key (Function.minimalPeriod (g • ·) q) q.out
        (QuotientGroup.out_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) -> zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod (g • ·) q.out
    have hf : forall q, f q in H.subgroupOf (zpowers g) := fun q => key q.out
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q in Finset.univ) => hf q
    simpa only [f, Finset.prod_pow_eq_pow_sum, index_eq_sum_minimalPeriod H g] using! key

中文:
定理 transfer_eq_pow_aux
  结论: (g : G)
  证明: by
  by_cases hH : H.index = 0
  · rw [hH, pow_zero]
    exact H.one_mem
  let := fintypeOfIndexNeZero hH
  classical
    replace key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g ^ k in H := fun k g₀ hk =>
      (congr_arg (· in H) (key k g₀ hk)).mp hk
    replace key : forall q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q in H := fun q =>
      key (Function.minimalPeriod (g • ·) q) q.out
        (QuotientGroup.out_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) -> zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod (g • ·) q.out
    have hf : forall q, f q in H.subgroupOf (zpowers g) := fun q => key q.out
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q in Finset.univ) => hf q
    simpa only [f, Finset.prod_pow_eq_pow_sum, index_eq_sum_minimalPeriod H g] using! key

Depends on / 依赖: Function, Function.minimalPeriod, H.index, H.one_mem, Quotient, QuotientGroup, QuotientGroup.out_conj_pow_minimalPeriod_mem, classical, congr_arg, fintypeOfIndexNeZero, minimalPeriod, one_mem, orbitRel, out_conj_pow_minimalPeriod_mem, pow_zero, q.out, replace, zpowers
-/
theorem transfer_eq_pow_aux (g : G)
    (key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    g ^ H.index in H := by
  by_cases hH : H.index = 0
  · rw [hH, pow_zero]
    exact H.one_mem
  let := fintypeOfIndexNeZero hH
  classical
    replace key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g ^ k in H := fun k g₀ hk =>
      (congr_arg (· in H) (key k g₀ hk)).mp hk
    replace key : forall q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q in H := fun q =>
      key (Function.minimalPeriod (g • ·) q) q.out
        (QuotientGroup.out_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) -> zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod (g • ·) q.out
    have hf : forall q, f q in H.subgroupOf (zpowers g) := fun q => key q.out
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q in Finset.univ) => hf q
    simpa only [f, Finset.prod_pow_eq_pow_sum, index_eq_sum_minimalPeriod H g] using! key

open scoped IsMulCommutative in
/--
theorem `transfer_eq_pow` / 定理 `transfer_eq_pow`

English:
theorem transfer_eq_pow
  statement: [FiniteIndex H] (g : G)
  proof: by
  classical
    let := H.fintypeQuotientOfFiniteIndex
    change forall (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ in H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
    rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot]; rw [← Finset.prod_map_toList]; rw [← Function.comp_def ϕ]; rw [List.prod_map_hom]
    refine congrArg ϕ (Subtype.coe_injective ?_)
    dsimp only
    rw [H.coe_mk]; rw [← (zpowers g).coe_mk g (mem_zpowers g)]; rw [← (zpowers g).coe_pow]; rw [index_eq_sum_minimalPeriod H g]; rw [← Finset.prod_pow_eq_pow_sum]; rw [← Finset.prod_map_toList]
    simp only [Subgroup.val_list_prod, List.map_map]
    congr 2
    funext
    apply key

中文:
定理 transfer_eq_pow
  结论: [FiniteIndex H] (g : G)
  证明: by
  classical
    let := H.fintypeQuotientOfFiniteIndex
    change forall (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ in H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
    rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot]; rw [← Finset.prod_map_toList]; rw [← Function.comp_def ϕ]; rw [List.prod_map_hom]
    refine congrArg ϕ (Subtype.coe_injective ?_)
    dsimp only
    rw [H.coe_mk]; rw [← (zpowers g).coe_mk g (mem_zpowers g)]; rw [← (zpowers g).coe_pow]; rw [index_eq_sum_minimalPeriod H g]; rw [← Finset.prod_pow_eq_pow_sum]; rw [← Finset.prod_map_toList]
    simp only [Subgroup.val_list_prod, List.map_map]
    congr 2
    funext
    apply key

Depends on / 依赖: Finset, Finset.prod_map_toList, Finset.prod_pow_eq_pow_sum, Function, Function.comp_def, H.coe_mk, H.fintypeQuotientOfFiniteIndex, List.prod_map_hom, Subtype, Subtype.coe_injective, classical, coe_injective, coe_mk, coe_pow, comp_def, fintypeQuotientOfFiniteIndex, index_eq_sum_minimalPeriod, mem_zpowers, prod_map_hom, prod_map_toList
-/
theorem transfer_eq_pow [FiniteIndex H] (g : G)
    (key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ := by
  classical
    let := H.fintypeQuotientOfFiniteIndex
    change forall (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ in H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
    rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot]; rw [← Finset.prod_map_toList]; rw [← Function.comp_def ϕ]; rw [List.prod_map_hom]
    refine congrArg ϕ (Subtype.coe_injective ?_)
    dsimp only
    rw [H.coe_mk]; rw [← (zpowers g).coe_mk g (mem_zpowers g)]; rw [← (zpowers g).coe_pow]; rw [index_eq_sum_minimalPeriod H g]; rw [← Finset.prod_pow_eq_pow_sum]; rw [← Finset.prod_map_toList]
    simp only [Subgroup.val_list_prod, List.map_map]
    congr 2
    funext
    apply key

open scoped IsMulCommutative in
/--
theorem `transfer_center_eq_pow` / 定理 `transfer_center_eq_pow`

English:
theorem transfer_center_eq_pow
  given: [FiniteIndex (center G)] (g : G)
  proof: transfer_eq_pow (id (center G)) g fun k _ hk => by rw [← mul_right_inj, ← hk.comm,
    mul_inv_cancel_right]

中文:
定理 transfer_center_eq_pow
  条件: [FiniteIndex (center G)] (g : G)
  证明: transfer_eq_pow (id (center G)) g fun k _ hk => by rw [← mul_right_inj, ← hk.comm,
    mul_inv_cancel_right]

Depends on / 依赖: center, hk.comm, mul_inv_cancel_right, mul_right_inj, transfer_eq_pow
-/
theorem transfer_center_eq_pow [FiniteIndex (center G)] (g : G) :
    transfer (MonoidHom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
  transfer_eq_pow (id (center G)) g fun k _ hk => by rw [← mul_right_inj, ← hk.comm,
    mul_inv_cancel_right]

variable (G) in
/--
Definition of `transferCenterPow` / `transferCenterPow` 的定义

English:
definition transferCenterPow
  signature: [FiniteIndex (center G)]
  body: ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' a b := by simp_rw [← show forall _, (_ : center G) = _ from transfer_center_eq_pow, map_mul]

@[simp]

中文:
定义 transferCenterPow
  签名: [FiniteIndex (center G)]
  定义体: ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' a b := by simp_rw [← show forall _, (_ : center G) = _ from transfer_center_eq_pow, map_mul]

@[simp]

Depends on / 依赖: center, pow_index_mem
-/
def transferCenterPow [FiniteIndex (center G)] : G ->* center G where
  toFun g := ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' a b := by simp_rw [← show forall _, (_ : center G) = _ from transfer_center_eq_pow, map_mul]

@[simp]
/--
theorem `transferCenterPow_apply` / 定理 `transferCenterPow_apply`

English:
theorem transferCenterPow_apply
  given: [FiniteIndex (center G)] (g : G)
  proof: rfl

中文:
定理 transferCenterPow_apply
  条件: [FiniteIndex (center G)] (g : G)
  证明: rfl
-/
theorem transferCenterPow_apply [FiniteIndex (center G)] (g : G) :
    ↑(transferCenterPow G g) = g ^ (center G).index :=
  rfl

section BurnsideTransfer

variable {p : Nat} (P : Sylow p G) (hP : normalizer P <= centralizer (P : Set G))
include hP

open scoped IsMulCommutative in
/--
Definition of `transferSylow` / `transferSylow` 的定义

English:
definition transferSylow
  signature: [P.FiniteIndex]
  body: haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  transfer (MonoidHom.id P)

中文:
定义 transferSylow
  签名: [P.FiniteIndex]
  定义体: haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  transfer (MonoidHom.id P)

Depends on / 依赖: IsMulCommutative, MonoidHom, MonoidHom.id, Subtype, Subtype.ext, le_normalizer, transfer
-/
def transferSylow [P.FiniteIndex] : G ->* P :=
  haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  transfer (MonoidHom.id P)

variable [Fact p.Prime] [Finite (Sylow p G)]

/--
theorem `transferSylow_eq_pow_aux` / 定理 `transferSylow_eq_pow_aux`

English:
theorem transferSylow_eq_pow_aux
  statement: (g : G) (hg : g in P) (k : Nat) (g₀ : G)
  proof: by
  have : IsMulCommutative P :=
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  replace hg := P.pow_mem hg k
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h
  exact h.trans (Commute.inv_mul_cancel (hP hn (g ^ k) hg).symm)

中文:
定理 transferSylow_eq_pow_aux
  结论: (g : G) (hg : g in P) (k : 自然数) (g₀ : G)
  证明: by
  have : IsMulCommutative P :=
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  replace hg := P.pow_mem hg k
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h
  exact h.trans (Commute.inv_mul_cancel (hP hn (g ^ k) hg).symm)

Depends on / 依赖: Commute, Commute.inv_mul_cancel, IsMulCommutative, P.conj_eq_normalizer_conj_of_mem, P.pow_mem, Subtype, Subtype.ext, conj_eq_normalizer_conj_of_mem, h.trans, inv_mul_cancel, le_normalizer, pow_mem, replace
-/
theorem transferSylow_eq_pow_aux (g : G) (hg : g in P) (k : Nat) (g₀ : G)
    (h : g₀⁻¹ * g ^ k * g₀ in P) : g₀⁻¹ * g ^ k * g₀ = g ^ k := by
  have : IsMulCommutative P :=
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  replace hg := P.pow_mem hg k
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h
  exact h.trans (Commute.inv_mul_cancel (hP hn (g ^ k) hg).symm)

variable [P.FiniteIndex]

open scoped IsMulCommutative in
/--
theorem `transferSylow_eq_pow` / 定理 `transferSylow_eq_pow`

English:
theorem transferSylow_eq_pow
  given: (g : G) (hg : g in P)
  proof: haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
transfer_eq_pow _ _ transferSylow_eq_pow_aux P hP g hg

中文:
定理 transferSylow_eq_pow
  条件: (g : G) (hg : g in P)
  证明: haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
transfer_eq_pow _ _ transferSylow_eq_pow_aux P hP g hg

Depends on / 依赖: IsMulCommutative, Subtype, Subtype.ext, le_normalizer, transferSylow_eq_pow_aux, transfer_eq_pow
-/
theorem transferSylow_eq_pow (g : G) (hg : g in P) :
    transferSylow P hP g =
      ⟨g ^ P.index, transfer_eq_pow_aux g (transferSylow_eq_pow_aux P hP g hg)⟩ :=
  haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
transfer_eq_pow _ _ transferSylow_eq_pow_aux P hP g hg

/--
theorem `transferSylow_domRestrict_eq_pow` / 定理 `transferSylow_domRestrict_eq_pow`

English:
theorem transferSylow_domRestrict_eq_pow
  statement: ⇑((transferSylow P hP).domRestrict (P : Subgroup G)) =
  proof: funext fun g => transferSylow_eq_pow P hP g g.2

@[deprecated (since := "2026-07-19")]
alias transferSylow_restrict_eq_pow := transferSylow_domRestrict_eq_pow

中文:
定理 transferSylow_domRestrict_eq_pow
  结论: ⇑((transferSylow P hP).domRestrict (P : 子群 G)) =
  证明: funext fun g => transferSylow_eq_pow P hP g g.2

@[deprecated (since := "2026-07-19")]
alias transferSylow_restrict_eq_pow := transferSylow_domRestrict_eq_pow

Depends on / 依赖: transferSylow_eq_pow
-/
theorem transferSylow_domRestrict_eq_pow : ⇑((transferSylow P hP).domRestrict (P : Subgroup G)) =
    (fun x : P => x ^ (P : Subgroup G).index) :=
  funext fun g => transferSylow_eq_pow P hP g g.2

@[deprecated (since := "2026-07-19")]
alias transferSylow_restrict_eq_pow := transferSylow_domRestrict_eq_pow

/--
theorem `ker_transferSylow_isComplement'` / 定理 `ker_transferSylow_isComplement'`

English:
theorem ker_transferSylow_isComplement'
  statement: IsComplement' (transferSylow P hP).ker P
  proof: by
  have hf : Function.Bijective ((transferSylow P hP).domRestrict (P : Subgroup G)) :=
    (transferSylow_domRestrict_eq_pow P hP).symm ▸ (P.2.powEquiv' P.not_dvd_index).bijective
  rw [Function.Bijective]; rw [← range_eq_top]; rw [domRestrict_range] at hf
  have := range_eq_top.mp (top_le_iff.mp (hf.2.ge.trans
    (map_le_range (transferSylow P hP) P)))
  rw [← (comap_injective this).eq_iff]; rw [comap_top]; rw [comap_map_eq]; rw [sup_comm]; rw [SetLike.ext'_iff]; rw [normal_mul]; rw [← ker_eq_bot_iff]; rw [← map_subtype_inj]; rw [ker_domRestrict]; rw [subgroupOf_map_subtype]; rw [Subgroup.map_bot]; rw [coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2

中文:
定理 ker_transferSylow_isComplement'
  结论: IsComplement' (transferSylow P hP).ker P
  证明: by
  have hf : Function.Bijective ((transferSylow P hP).domRestrict (P : Subgroup G)) :=
    (transferSylow_domRestrict_eq_pow P hP).symm ▸ (P.2.powEquiv' P.not_dvd_index).bijective
  rw [Function.Bijective]; rw [← range_eq_top]; rw [domRestrict_range] at hf
  have := range_eq_top.mp (top_le_iff.mp (hf.2.ge.trans
    (map_le_range (transferSylow P hP) P)))
  rw [← (comap_injective this).eq_iff]; rw [comap_top]; rw [comap_map_eq]; rw [sup_comm]; rw [SetLike.ext'_iff]; rw [normal_mul]; rw [← ker_eq_bot_iff]; rw [← map_subtype_inj]; rw [ker_domRestrict]; rw [subgroupOf_map_subtype]; rw [Subgroup.map_bot]; rw [coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2

Depends on / 依赖: Bijective, Function, Function.Bijective, P.not_dvd_index, SetLike, SetLike.ext, Subgroup, _iff, bijective, comap_injective, comap_map_eq, comap_top, domRestrict, domRestrict_range, eq_iff, ge.trans, ker_eq_bot_iff, map_le_range, normal_mul, not_dvd_index
-/
theorem ker_transferSylow_isComplement' : IsComplement' (transferSylow P hP).ker P := by
  have hf : Function.Bijective ((transferSylow P hP).domRestrict (P : Subgroup G)) :=
    (transferSylow_domRestrict_eq_pow P hP).symm ▸ (P.2.powEquiv' P.not_dvd_index).bijective
  rw [Function.Bijective]; rw [← range_eq_top]; rw [domRestrict_range] at hf
  have := range_eq_top.mp (top_le_iff.mp (hf.2.ge.trans
    (map_le_range (transferSylow P hP) P)))
  rw [← (comap_injective this).eq_iff]; rw [comap_top]; rw [comap_map_eq]; rw [sup_comm]; rw [SetLike.ext'_iff]; rw [normal_mul]; rw [← ker_eq_bot_iff]; rw [← map_subtype_inj]; rw [ker_domRestrict]; rw [subgroupOf_map_subtype]; rw [Subgroup.map_bot]; rw [coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2

/--
theorem `not_dvd_card_ker_transferSylow` / 定理 `not_dvd_card_ker_transferSylow`

English:
theorem not_dvd_card_ker_transferSylow
  statement: ¬p ∣ Nat.card (transferSylow P hP).ker
  proof: (ker_transferSylow_isComplement' P hP).index_eq_card ▸ P.not_dvd_index

中文:
定理 not_dvd_card_ker_transferSylow
  结论: ¬p ∣ 自然数.card (transferSylow P hP).ker
  证明: (ker_transferSylow_isComplement' P hP).index_eq_card ▸ P.not_dvd_index

Depends on / 依赖: P.not_dvd_index, index_eq_card, ker_transferSylow_isComplement, not_dvd_index
-/
theorem not_dvd_card_ker_transferSylow : ¬p ∣ Nat.card (transferSylow P hP).ker :=
  (ker_transferSylow_isComplement' P hP).index_eq_card ▸ P.not_dvd_index

/--
theorem `ker_transferSylow_disjoint` / 定理 `ker_transferSylow_disjoint`

English:
theorem ker_transferSylow_disjoint
  given: (Q : Subgroup G) (hQ : IsPGroup p Q)
  proof: disjoint_iff.mpr
card_eq_one.mp
      (hQ.to_le inf_le_right).card_eq_or_dvd.resolve_right fun h =>
not_dvd_card_ker_transferSylow P hP h.trans card_dvd_of_le inf_le_left

中文:
定理 ker_transferSylow_disjoint
  条件: (Q : 子群 G) (hQ : 是p群 p Q)
  证明: disjoint_iff.mpr
card_eq_one.mp
      (hQ.to_le inf_le_right).card_eq_or_dvd.resolve_right fun h =>
not_dvd_card_ker_transferSylow P hP h.trans card_dvd_of_le inf_le_left

Depends on / 依赖: card_dvd_of_le, card_eq_one, card_eq_one.mp, card_eq_or_dvd, card_eq_or_dvd.resolve_right, disjoint_iff, disjoint_iff.mpr, h.trans, hQ.to_le, inf_le_left, inf_le_right, not_dvd_card_ker_transferSylow, resolve_right, to_le
-/
theorem ker_transferSylow_disjoint (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Disjoint (transferSylow P hP).ker Q :=
disjoint_iff.mpr
card_eq_one.mp
      (hQ.to_le inf_le_right).card_eq_or_dvd.resolve_right fun h =>
not_dvd_card_ker_transferSylow P hP h.trans card_dvd_of_le inf_le_left

end BurnsideTransfer

end MonoidHom

namespace IsCyclic

open Subgroup

-- we could suppress the variable `p`, but that might introduce `motive not type correct` issues.
variable {G : Type*} [Group G] [Finite G] {p : Nat} (hp : (Nat.card G).minFac = p) {P : Sylow p G}

include hp in
/--
theorem `normalizer_le_centralizer` / 定理 `normalizer_le_centralizer`

English:
theorem normalizer_le_centralizer
  given: (hP : IsCyclic P)
  proof: by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (normalizer _) (centralizer P)]
  have := Fact.mk (Nat.minFac_prime hn)
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker]; rw [← index]; rw [← relIndex] at key
  refine relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  rcases eq_zero_or_pos k with h0 | h0
  · rw [hP.card_mulAut, hk, h0, pow_zero, Nat.totient_one]
    apply Nat.coprime_one_right
  rw [hP.card_mulAut]; rw [hk]; rw [Nat.totient_prime_pow Fact.out h0]
  refine (Nat.Coprime.pow_right _ ?_).mul_right ?_
  · apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left _ P.le_centralizer)
    apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
    rw [Nat.coprime_comm]; rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact P.not_dvd_index
· apply Nat.Coprime.coprime_dvd_left relIndex_dvd_card ..
apply Nat.Coprime.coprime_dvd_left card_subgroup_dvd_card _
    have h1 := Nat.gcd_dvd_left (Nat.card G) ((Nat.card G).minFac - 1)
    have h2 := Nat.gcd_le_right (n := (Nat.card G).minFac - 1) (Nat.card G)
      (tsub_pos_iff_lt.mpr (Nat.minFac_prime hn).one_lt)
    contrapose! h2
    refine Nat.sub_one_lt_of_le (Nat.card G).minFac_pos (Nat.minFac_le_of_dvd ?_ h1)
    exact (Nat.two_le_iff _).mpr ⟨ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h1, h2⟩

include hp in

中文:
定理 normalizer_le_centralizer
  条件: (hP : 是循环 P)
  证明: by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (normalizer _) (centralizer P)]
  have := Fact.mk (Nat.minFac_prime hn)
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker]; rw [← index]; rw [← relIndex] at key
  refine relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  rcases eq_zero_or_pos k with h0 | h0
  · rw [hP.card_mulAut, hk, h0, pow_zero, Nat.totient_one]
    apply Nat.coprime_one_right
  rw [hP.card_mulAut]; rw [hk]; rw [Nat.totient_prime_pow Fact.out h0]
  refine (Nat.Coprime.pow_right _ ?_).mul_right ?_
  · apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left _ P.le_centralizer)
    apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
    rw [Nat.coprime_comm]; rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact P.not_dvd_index
· apply Nat.Coprime.coprime_dvd_left relIndex_dvd_card ..
apply Nat.Coprime.coprime_dvd_left card_subgroup_dvd_card _
    have h1 := Nat.gcd_dvd_left (Nat.card G) ((Nat.card G).minFac - 1)
    have h2 := Nat.gcd_le_right (n := (Nat.card G).minFac - 1) (Nat.card G)
      (tsub_pos_iff_lt.mpr (Nat.minFac_prime hn).one_lt)
    contrapose! h2
    refine Nat.sub_one_lt_of_le (Nat.card G).minFac_pos (Nat.minFac_le_of_dvd ?_ h1)
    exact (Nat.two_le_iff _).mpr ⟨ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h1, h2⟩

include hp in

Depends on / 依赖: Fact.mk, Nat.card, Nat.card_eq_one_iff_unique.mp, Nat.eq_one_of_dvd_coprimes, Nat.minFac_prime, P.normalizerMonoidHom, QuotientGroup, QuotientGroup.kerLift_injective, Subsingleton, Subsingleton.elim, card_dvd_of_injective, card_eq_one_iff_unique, card_mul, centralizer, dvd_rfl, eq_one_of_dvd_coprimes, eq_zero_or_pos, exists_card_eq, hP.card_mul, kerLift_injective
-/
theorem normalizer_le_centralizer (hP : IsCyclic P) :
    normalizer P <= centralizer (P : Set G) := by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (normalizer _) (centralizer P)]
  have := Fact.mk (Nat.minFac_prime hn)
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker]; rw [← index]; rw [← relIndex] at key
  refine relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  rcases eq_zero_or_pos k with h0 | h0
  · rw [hP.card_mulAut, hk, h0, pow_zero, Nat.totient_one]
    apply Nat.coprime_one_right
  rw [hP.card_mulAut]; rw [hk]; rw [Nat.totient_prime_pow Fact.out h0]
  refine (Nat.Coprime.pow_right _ ?_).mul_right ?_
  · apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left _ P.le_centralizer)
    apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
    rw [Nat.coprime_comm]; rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact P.not_dvd_index
· apply Nat.Coprime.coprime_dvd_left relIndex_dvd_card ..
apply Nat.Coprime.coprime_dvd_left card_subgroup_dvd_card _
    have h1 := Nat.gcd_dvd_left (Nat.card G) ((Nat.card G).minFac - 1)
    have h2 := Nat.gcd_le_right (n := (Nat.card G).minFac - 1) (Nat.card G)
      (tsub_pos_iff_lt.mpr (Nat.minFac_prime hn).one_lt)
    contrapose! h2
    refine Nat.sub_one_lt_of_le (Nat.card G).minFac_pos (Nat.minFac_le_of_dvd ?_ h1)
    exact (Nat.two_le_iff _).mpr ⟨ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h1, h2⟩

include hp in
/--
theorem `isComplement'` / 定理 `isComplement'`

English:
theorem isComplement'
  given: (hP : IsCyclic P)
  proof: by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)).ker ⊥]; rw [Subsingleton.elim P.1 ⊤]
    exact isComplement'_bot_top
  have := Fact.mk (Nat.minFac_prime hn)
  exact MonoidHom.ker_transferSylow_isComplement' P (hP.normalizer_le_centralizer rfl)

中文:
定理 isComplement'
  条件: (hP : 是循环 P)
  证明: by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)).ker ⊥]; rw [Subsingleton.elim P.1 ⊤]
    exact isComplement'_bot_top
  have := Fact.mk (Nat.minFac_prime hn)
  exact MonoidHom.ker_transferSylow_isComplement' P (hP.normalizer_le_centralizer rfl)

Depends on / 依赖: Fact.mk, MonoidHom, MonoidHom.ker_transferSylow_isComplement, MonoidHom.transferSylow, Nat.card, Nat.card_eq_one_iff_unique.mp, Nat.minFac_prime, Subsingleton, Subsingleton.elim, _bot_top, card_eq_one_iff_unique, hP.normalizer_le_centralizer, isComplement, ker_transferSylow_isComplement, minFac_prime, normalizer_le_centralizer, transferSylow
-/
theorem isComplement' (hP : IsCyclic P) :
    (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp)).ker.IsComplement' P := by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)).ker ⊥]; rw [Subsingleton.elim P.1 ⊤]
    exact isComplement'_bot_top
  have := Fact.mk (Nat.minFac_prime hn)
  exact MonoidHom.ker_transferSylow_isComplement' P (hP.normalizer_le_centralizer rfl)

end IsCyclic
