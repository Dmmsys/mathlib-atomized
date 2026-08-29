/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Transfer

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `Subgroup.exists_right_complement'_of_coprime`: The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `Subgroup.exists_left_complement'_of_coprime`: The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/

@[expose] public section


namespace Subgroup

section SchurZassenhausAbelian

open MulOpposite MulAction Subgroup.leftTransversals
open scoped IsMulCommutative

variable {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H] [FiniteIndex H]
  (α β : H.LeftTransversal)

/--
Definition of `QuotientDiff` / `QuotientDiff` 的定义

English:
definition QuotientDiff
  body: Quotient
    (Setoid.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun h => by rw [← diff_inv, h, inv_one],
        fun h h' => by rw [← diff_mul_diff, h, h', one_mul]⟩)

中文:
定义 QuotientDiff
  定义体: Quotient
    (Setoid.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun h => by rw [← diff_inv, h, inv_one],
        fun h h' => by rw [← diff_mul_diff, h, h', one_mul]⟩)

Depends on / 依赖: MonoidHom, MonoidHom.id, Quotient, Setoid, Setoid.mk, diff_inv, diff_mul_diff, diff_self, inv_one, one_mul
-/
def QuotientDiff :=
  Quotient
    (Setoid.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun h => by rw [← diff_inv, h, inv_one],
        fun h h' => by rw [← diff_mul_diff, h, h', one_mul]⟩)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited H.QuotientDiff
  body: inferInstanceAs (Inhabited <| Quotient _)

中文:
实例 :
  签名: Inhabited H.QuotientDiff
  定义体: inferInstanceAs (Inhabited <| Quotient _)

Depends on / 依赖: Inhabited, Quotient
-/
noncomputable instance : Inhabited H.QuotientDiff :=
  inferInstanceAs (Inhabited <| Quotient _)

/--
theorem `smul_diff_smul'` / 定理 `smul_diff_smul'`

English:
theorem smul_diff_smul'
  given: [hH : Normal H] (g : Gᵐᵒᵖ)
  proof: by
  let := H.fintypeQuotientOfFiniteIndex
  let ϕ : H ->* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop,
          hH.mem_comm ((congr_arg (· in H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
      map_one' := by rw [Subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_cancel]


中文:
定理 smul_diff_smul'
  条件: [hH : Normal H] (g : Gᵐᵒᵖ)
  证明: by
  let := H.fintypeQuotientOfFiniteIndex
  let ϕ : H ->* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop,
          hH.mem_comm ((congr_arg (· in H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
      map_one' := by rw [Subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_cancel]


Depends on / 依赖: Fintype, Fintype.prod_equiv, H.fintypeQuotientOfFiniteIndex, MulAction, MulAction.toPerm, SetLike, SetLike.coe_mem, Subtype, Subtype.ext_iff, coe_mem, coe_mk, coe_mul, coe_one, congr_arg, ext_iff, fintypeQuotientOfFiniteIndex, g.unop, hH.mem_comm, inv_mul_cancel, map_mul
-/
theorem smul_diff_smul' [hH : Normal H] (g : Gᵐᵒᵖ) :
    diff (MonoidHom.id H) (g • α) (g • β) =
      ⟨g.unop⁻¹ * (diff (MonoidHom.id H) α β : H) * g.unop,
        hH.mem_comm ((congr_arg (· in H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩ := by
  let := H.fintypeQuotientOfFiniteIndex
  let ϕ : H ->* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop,
          hH.mem_comm ((congr_arg (· in H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
      map_one' := by rw [Subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_cancel]
      map_mul' := fun h₁ h₂ => by
        simp only [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left] }
  refine (Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun x => ?_).trans (map_prod ϕ _ _).symm
  simp only [ϕ, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, mul_inv_rev, mul_assoc,
    MonoidHom.id_apply, toPerm_symm_apply, MonoidHom.coe_mk, OneHom.coe_mk]

variable {H}
variable [Normal H]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G H.QuotientDiff
  body: Quotient.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_eq_left, ←
            coe_one, ← Subtype.ext_iff])
  mul_smul g₁ g₂ q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by 

中文:
实例 :
  签名: MulAction G H.QuotientDiff
  定义体: Quotient.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_eq_left, ←
            coe_one, ← Subtype.ext_iff])
  mul_smul g₁ g₂ q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by 

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.map, Quotient.mk, Subtype, Subtype.ext, Subtype.ext_iff, coe_mk, coe_one, congr_arg, ext_iff, inductionOn, inv_one, mul_eq_left, mul_eq_one_iff_eq_inv, mul_inv_rev, mul_smul, one_smul, smul_diff_smul
-/
noncomputable instance : MulAction G H.QuotientDiff where
  smul g :=
    Quotient.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_eq_left, ←
            coe_one, ← Subtype.ext_iff])
  mul_smul g₁ g₂ q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [mul_inv_rev]; exact mul_smul (op g₁⁻¹) (op g₂⁻¹) T)
  one_smul q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [inv_one]; apply one_smul Gᵐᵒᵖ T)

/--
theorem `smul_diff'` / 定理 `smul_diff'`

English:
theorem smul_diff'
  given: (h : H)
  proof: by
  let := H.fintypeQuotientOfFiniteIndex
  rw [diff]; rw [diff]; rw [index_eq_card]; rw [Nat.card_eq_fintype_card]; rw [← Finset.card_univ]; rw [← Finset.prod_const]; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul

中文:
定理 smul_diff'
  条件: (h : H)
  证明: by
  let := H.fintypeQuotientOfFiniteIndex
  rw [diff]; rw [diff]; rw [index_eq_card]; rw [Nat.card_eq_fintype_card]; rw [← Finset.card_univ]; rw [← Finset.prod_const]; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul

Depends on / 依赖: Equiv.apply_eq_iff_eq, Finset, Finset.card_univ, Finset.prod_congr, Finset.prod_const, Finset.prod_mul_distrib, H.fintypeQuotientOfFiniteIndex, MonoidHom, MonoidHom.id_apply, MulOpposite, MulOpposite.unop_op, Nat.card_eq_fintype_card, Subtype, Subtype.ext_iff, apply_eq_iff_eq, card_eq_fintype_card, card_univ, coe_mul, ext_iff, fintypeQuotientOfFiniteIndex
-/
theorem smul_diff' (h : H) :
    diff (MonoidHom.id H) α (op (h : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index := by
  let := H.fintypeQuotientOfFiniteIndex
  rw [diff]; rw [diff]; rw [index_eq_card]; rw [Nat.card_eq_fintype_card]; rw [← Finset.card_univ]; rw [← Finset.prod_const]; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul, mul_assoc, mul_right_inj]
  rw [smul_apply_eq_smul_apply_inv_smul]; rw [smul_eq_mul_unop]; rw [MulOpposite.unop_op]; rw [mul_left_inj]; rw [← Subtype.ext_iff]; rw [Equiv.apply_eq_iff_eq]; rw [inv_smul_eq_iff]
  exact left_eq_mul.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)

/--
theorem `eq_one_of_smul_eq_one` / 定理 `eq_one_of_smul_eq_one`

English:
theorem eq_one_of_smul_eq_one
  statement: (hH : Nat.Coprime (Nat.card H) H.index) (α : H.QuotientDiff)
  proof: Quotient.inductionOn' α fun α hα =>
(powCoprime hH).injective
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv]; rw [smul_diff']; rw [diff_self]; rw [one_mul]; rw [inv_pow]; rw [inv_inv]
        _ = 1 ^ H.index := (Quotient.exact' hα).t

中文:
定理 eq_one_of_smul_eq_one
  结论: (hH : 自然数.Coprime (自然数.card H) H.index) (α : H.QuotientDiff)
  证明: Quotient.inductionOn' α fun α hα =>
(powCoprime hH).injective
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv]; rw [smul_diff']; rw [diff_self]; rw [one_mul]; rw [inv_pow]; rw [inv_inv]
        _ = 1 ^ H.index := (Quotient.exact' hα).t

Depends on / 依赖: H.index, MonoidHom, MonoidHom.id, Quotient, Quotient.exact, Quotient.inductionOn, diff_inv, diff_self, inductionOn, injective, inv_inv, inv_pow, one_mul, one_pow, powCoprime, smul_diff
-/
theorem eq_one_of_smul_eq_one (hH : Nat.Coprime (Nat.card H) H.index) (α : H.QuotientDiff)
    (h : H) : h • α = α -> h = 1 :=
  Quotient.inductionOn' α fun α hα =>
(powCoprime hH).injective
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv]; rw [smul_diff']; rw [diff_self]; rw [one_mul]; rw [inv_pow]; rw [inv_inv]
        _ = 1 ^ H.index := (Quotient.exact' hα).trans (one_pow H.index).symm

/--
theorem `exists_smul_eq` / 定理 `exists_smul_eq`

English:
theorem exists_smul_eq
  given: (hH : Nat.Coprime (Nat.card H) H.index) (α β : H.QuotientDiff)
  proof: Quotient.inductionOn' α
    (Quotient.inductionOn' β fun β α =>
      Exists.imp (fun _ => Quotient.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidH

中文:
定理 exists_smul_eq
  条件: (hH : 自然数.Coprime (自然数.card H) H.index) (α β : H.QuotientDiff)
  证明: Quotient.inductionOn' α
    (Quotient.inductionOn' β fun β α =>
      Exists.imp (fun _ => Quotient.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidH

Depends on / 依赖: Equiv.apply_symm_apply, Exists, Exists.imp, MonoidHom, MonoidHom.id, Quotient, Quotient.inductionOn, Quotient.sound, apply_symm_apply, diff_inv, inductionOn, inv_eq_one, inv_eq_one.mpr, inv_pow, mul_inv_cancel, powCoprime, powCoprime_apply, smul_diff, symm.trans
-/
theorem exists_smul_eq (hH : Nat.Coprime (Nat.card H) H.index) (α β : H.QuotientDiff) :
    exists h : H, h • α = β :=
  Quotient.inductionOn' α
    (Quotient.inductionOn' β fun β α =>
      Exists.imp (fun _ => Quotient.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidHom.id H) β α))⁻¹).trans
                (by rw [inv_pow, ← powCoprime_apply hH, Equiv.apply_symm_apply, mul_inv_cancel])))⟩)

/--
theorem `isComplement'_stabilizer_of_coprime` / 定理 `isComplement'_stabilizer_of_coprime`

English:
theorem isComplement'_stabilizer_of_coprime
  statement: {α : H.QuotientDiff}
  proof: isComplement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α

中文:
定理 isComplement'_stabilizer_of_coprime
  结论: {α : H.QuotientDiff}
  证明: isComplement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α
-/
theorem isComplement'_stabilizer_of_coprime {α : H.QuotientDiff}
    (hH : Nat.Coprime (Nat.card H) H.index) : IsComplement' H (stabilizer G α) :=
  isComplement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α

/--
theorem `exists_right_complement'_of_coprime_aux` / 定理 `exists_right_complement'_of_coprime_aux`

English:
theorem exists_right_complement'_of_coprime_aux
  given: (hH : Nat.Coprime (Nat.card H) H.index)
  proof: have ne : Nonempty (QuotientDiff H) := inferInstance
  ne.elim fun α => ⟨stabilizer G α, isComplement'_stabilizer_of_coprime hH⟩

中文:
定理 exists_right_complement'_of_coprime_aux
  条件: (hH : 自然数.Coprime (自然数.card H) H.index)
  证明: have ne : Nonempty (QuotientDiff H) := inferInstance
  ne.elim fun α => ⟨stabilizer G α, isComplement'_stabilizer_of_coprime hH⟩
-/
private theorem exists_right_complement'_of_coprime_aux (hH : Nat.Coprime (Nat.card H) H.index) :
    exists K : Subgroup G, IsComplement' H K :=
  have ne : Nonempty (QuotientDiff H) := inferInstance
  ne.elim fun α => ⟨stabilizer G α, isComplement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Group G] {N : Subgroup G} [Normal N]
  (h1 : Nat.Coprime (Nat.card N) N.index)
  (h2 : forall (G' : Type u) [Group G'] [Finite G'],
    Nat.card G' < Nat.card G -> forall {N' : Subgroup G'} [N'.Normal],
      Nat.Coprime (Nat.card N') N'.index -> exists H' : Subgroup G', IsComplement' N' H')
  (h3 : forall H : Subgroup G, ¬IsComplement' N H)
include h1 h3

/-! We will arrive at a contradiction via the following steps:
* step 0: `N` (the normal Hall subgroup) is nontrivial.
* step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
* step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
* step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
* step 4: `p` (`min_fact (Fintype.card N)`) is prime (follows from step0).
* step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
* step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
* step 7: `N` is abelian (applies step 3 to the center of `N`).
-/


/--
theorem `step0` / 定理 `step0`

English:
theorem step0
  statement: N != ⊥
  proof: by
  rintro rfl
  exact h3 ⊤ isComplement'_bot_top

中文:
定理 step0
  结论: N != ⊥
  证明: by
  rintro rfl
  exact h3 ⊤ isComplement'_bot_top
-/
private theorem step0 : N != ⊥ := by
  rintro rfl
  exact h3 ⊤ isComplement'_bot_top

variable [Finite G]

include h2 in
/--
theorem `step1` / 定理 `step1`

English:
theorem step1
  given: (K : Subgroup G) (hK : K ⊔ N = ⊤)
  statement: K = ⊤
  proof: by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relIndex_top_right]; rw [← hK]
    exact (relIndex_sup_right K N).symm
  have h5 : Nat.card K < Nat.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Nat.card_pos (one_lt_index_of_ne_top h3)


中文:
定理 step1
  条件: (K : Subgroup G) (hK : K ⊔ N = ⊤)
  结论: K = ⊤
  证明: by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relIndex_top_right]; rw [← hK]
    exact (relIndex_sup_right K N).symm
  have h5 : Nat.card K < Nat.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Nat.card_pos (one_lt_index_of_ne_top h3)

-/
private theorem step1 (K : Subgroup G) (hK : K ⊔ N = ⊤) : K = ⊤ := by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relIndex_top_right]; rw [← hK]
    exact (relIndex_sup_right K N).symm
  have h5 : Nat.card K < Nat.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Nat.card_pos (one_lt_index_of_ne_top h3)
  have h6 : Nat.Coprime (Nat.card (N.comap K.subtype)) (N.comap K.subtype).index := by
    rw [h4]
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype Subtype.coe_injective)
  obtain ⟨H, hH⟩ := h2 K h5 h6
  replace hH : Nat.card (H.map K.subtype) = N.index := by
    rw [← relIndex_bot_left]; rw [← relIndex_comap]; rw [MonoidHom.comap_bot]; rw [Subgroup.ker_subtype]; rw [relIndex_bot_left]; rw [← IsComplement'.index_eq_card (IsComplement'.symm hH)]; rw [index_comap]; rw [range_subtype]; rw [← relIndex_sup_right]; rw [hK]; rw [relIndex_top_right]
  have h7 : Nat.card N * Nat.card (H.map K.subtype) = Nat.card G := by
    rw [hH]; rw [← N.index_mul_card]; rw [mul_comm]
  have h8 : (Nat.card N).Coprime (Nat.card (H.map K.subtype)) := by
    rwa [hH]
  exact ⟨H.map K.subtype, isComplement'_of_coprime h7 h8⟩

include h2 in
/--
theorem `step2` / 定理 `step2`

English:
theorem step2
  given: (K : Subgroup G) [K.Normal] (hK : K <= N)
  statement: K = ⊥ ∨ K = N
  proof: by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotient.mk''_surjective
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Nat.card (G ⧸ K) < Nat.card G := by
    rw [← index_eq_card]; rw [← K.index_mul_card]
    refine
      lt_mul_of_one_lt_right (Nat.pos_of_ne_zero index_ne_zero_o

中文:
定理 step2
  条件: (K : Subgroup G) [K.Normal] (hK : K <= N)
  结论: K = ⊥ ∨ K = N
  证明: by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotient.mk''_surjective
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Nat.card (G ⧸ K) < Nat.card G := by
    rw [← index_eq_card]; rw [← K.index_mul_card]
    refine
      lt_mul_of_one_lt_right (Nat.pos_of_ne_zero index_ne_zero_o
-/
private theorem step2 (K : Subgroup G) [K.Normal] (hK : K <= N) : K = ⊥ ∨ K = N := by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotient.mk''_surjective
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Nat.card (G ⧸ K) < Nat.card G := by
    rw [← index_eq_card]; rw [← K.index_mul_card]
    refine
      lt_mul_of_one_lt_right (Nat.pos_of_ne_zero index_ne_zero_of_finite)
        (K.one_lt_card_iff_ne_bot.mpr h4.1)
  have h6 :
    (Nat.card (N.map (QuotientGroup.mk' K))).Coprime (N.map (QuotientGroup.mk' K)).index := by
    have index_map := N.index_map_eq this (by rwa [QuotientGroup.ker_mk'])
    have index_pos : 0 < N.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    rw [index_map]
    refine h1.coprime_dvd_left ?_
    rw [← Nat.mul_dvd_mul_iff_left index_pos]; rw [index_mul_card]; rw [← index_map]; rw [index_mul_card]
    exact K.card_quotient_dvd_card
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6
  refine ⟨H.comap (QuotientGroup.mk' K), ?_, ?_⟩
  · have key : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
      refine comap_map_eq_self ?_
      rwa [QuotientGroup.ker_mk']
    rwa [← key, comap_sup_eq, hH.symm.sup_eq_top, comap_top]
  · rw [← comap_top (QuotientGroup.mk' K)]
    intro hH'
    rw [comap_injective this hH']; rw [isComplement'_top_right]; rw [map_eq_bot_iff]; rw [QuotientGroup.ker_mk'] at hH
    exact h4.2 (le_antisymm hK hH)

include h2 in
/--
theorem `step3` / 定理 `step3`

English:
theorem step3
  given: (K : Subgroup N) [(K.map N.subtype).Normal]
  statement: K = ⊥ ∨ K = ⊤
  proof: by
  have key := step2 h1 h2 h3 (K.map N.subtype) (map_subtype_le K)
  rw [← map_bot N.subtype] at key
  conv at key =>
    rhs
    rhs
    rw [← N.range_subtype]; rw [N.subtype.range_eq_map]
  rwa [map_subtype_inj, map_subtype_inj] at key

中文:
定理 step3
  条件: (K : Subgroup N) [(K.map N.subtype).Normal]
  结论: K = ⊥ ∨ K = ⊤
  证明: by
  have key := step2 h1 h2 h3 (K.map N.subtype) (map_subtype_le K)
  rw [← map_bot N.subtype] at key
  conv at key =>
    rhs
    rhs
    rw [← N.range_subtype]; rw [N.subtype.range_eq_map]
  rwa [map_subtype_inj, map_subtype_inj] at key
-/
private theorem step3 (K : Subgroup N) [(K.map N.subtype).Normal] : K = ⊥ ∨ K = ⊤ := by
  have key := step2 h1 h2 h3 (K.map N.subtype) (map_subtype_le K)
  rw [← map_bot N.subtype] at key
  conv at key =>
    rhs
    rhs
    rw [← N.range_subtype]; rw [N.subtype.range_eq_map]
  rwa [map_subtype_inj, map_subtype_inj] at key

/--
theorem `step4` / 定理 `step4`

English:
theorem step4
  statement: (Nat.card N).minFac.Prime
  proof: Nat.minFac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h3)).ne'

中文:
定理 step4
  结论: (自然数.card N).minFac.Prime
  证明: Nat.minFac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h3)).ne'
-/
private theorem step4 : (Nat.card N).minFac.Prime :=
  Nat.minFac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h3)).ne'

/--
theorem `step5` / 定理 `step5`

English:
theorem step5
  given: {P : Sylow (Nat.card N).minFac N}
  statement: P.1 != ⊥
  proof: by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  apply P.ne_bot_of_dvd_card
  exact (Nat.card N).minFac_dvd

include h2 in

中文:
定理 step5
  条件: {P : Sylow (自然数.card N).minFac N}
  结论: P.1 != ⊥
  证明: by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  apply P.ne_bot_of_dvd_card
  exact (Nat.card N).minFac_dvd

include h2 in
-/
private theorem step5 {P : Sylow (Nat.card N).minFac N} : P.1 != ⊥ := by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  apply P.ne_bot_of_dvd_card
  exact (Nat.card N).minFac_dvd

include h2 in
/--
theorem `step6` / 定理 `step6`

English:
theorem step6
  statement: IsPGroup (Nat.card N).minFac N
  proof: by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  refine Sylow.nonempty.elim fun P => P.2.of_surjective P.1.subtype ?_
  rw [← MonoidHom.range_eq_top]; rw [range_subtype]
  have : (P.1.map N.subtype).Normal :=
    normalizer_eq_top_iff.mp (step1 h1 h2 h3 _ P.normalizer_sup_eq_top)
  exac

中文:
定理 step6
  结论: IsPGroup (自然数.card N).minFac N
  证明: by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  refine Sylow.nonempty.elim fun P => P.2.of_surjective P.1.subtype ?_
  rw [← MonoidHom.range_eq_top]; rw [range_subtype]
  have : (P.1.map N.subtype).Normal :=
    normalizer_eq_top_iff.mp (step1 h1 h2 h3 _ P.normalizer_sup_eq_top)
  exac
-/
private theorem step6 : IsPGroup (Nat.card N).minFac N := by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  refine Sylow.nonempty.elim fun P => P.2.of_surjective P.1.subtype ?_
  rw [← MonoidHom.range_eq_top]; rw [range_subtype]
  have : (P.1.map N.subtype).Normal :=
    normalizer_eq_top_iff.mp (step1 h1 h2 h3 _ P.normalizer_sup_eq_top)
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h3)

include h2 in
/--
theorem `step7` / 定理 `step7`

English:
theorem step7
  statement: IsMulCommutative N
  proof: by
  have := N.bot_or_nontrivial.resolve_left (step0 h1 h3)
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  exact
    ⟨⟨fun g h => ((eq_top_iff.mp ((step3 h1 h2 h3 (center N)).resolve_left
      (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h)).comm g).symm⟩⟩

中文:
定理 step7
  结论: IsMulCommutative N
  证明: by
  have := N.bot_or_nontrivial.resolve_left (step0 h1 h3)
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  exact
    ⟨⟨fun g h => ((eq_top_iff.mp ((step3 h1 h2 h3 (center N)).resolve_left
      (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h)).comm g).symm⟩⟩

Depends on / 依赖: N.bot_or_nontrivial.resolve_left, Nat.card, bot_lt_center, bot_lt_center.ne, bot_or_nontrivial, center, eq_top_iff, eq_top_iff.mp, mem_top, minFac, minFac.Prime, resolve_left
-/
theorem step7 : IsMulCommutative N := by
  have := N.bot_or_nontrivial.resolve_left (step0 h1 h3)
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  exact
    ⟨⟨fun g h => ((eq_top_iff.mp ((step3 h1 h2 h3 (center N)).resolve_left
      (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h)).comm g).symm⟩⟩

end SchurZassenhausInduction

variable {n : Nat} {G : Type u} [Group G]

/--
theorem `exists_right_complement'_of_coprime_aux'` / 定理 `exists_right_complement'_of_coprime_aux'`

English:
theorem exists_right_complement'_of_coprime_aux'
  statement: [Finite G] (hG : Nat.card G = n)
  proof: by
  revert G
  induction n using Nat.strongRecOn with | ind n ih => ?_
  rintro G _ _ rfl N _ hN
  refine not_forall_not.mp fun h3 => ?_
  have := SchurZassenhausInduction.step7 hN (fun G' _ _ hG' => by apply ih _ hG'; rfl) h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime

中文:
定理 exists_right_complement'_of_coprime_aux'
  结论: [Finite G] (hG : 自然数.card G = n)
  证明: by
  revert G
  induction n using Nat.strongRecOn with | ind n ih => ?_
  rintro G _ _ rfl N _ hN
  refine not_forall_not.mp fun h3 => ?_
  have := SchurZassenhausInduction.step7 hN (fun G' _ _ hG' => by apply ih _ hG'; rfl) h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime
-/
private theorem exists_right_complement'_of_coprime_aux' [Finite G] (hG : Nat.card G = n)
    {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    exists H : Subgroup G, IsComplement' N H := by
  revert G
  induction n using Nat.strongRecOn with | ind n ih => ?_
  rintro G _ _ rfl N _ hN
  refine not_forall_not.mp fun h3 => ?_
  have := SchurZassenhausInduction.step7 hN (fun G' _ _ hG' => by apply ih _ hG'; rfl) h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)

/--
theorem `exists_right_complement'_of_coprime` / 定理 `exists_right_complement'_of_coprime`

English:
theorem exists_right_complement'_of_coprime
  statement: {N : Subgroup G} [N.Normal]
  proof: by
  by_cases hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_left, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, isComplement'_top_bot⟩
  by_cases hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_right, Nat.card_eq_one_iff_unique] at hN
    have := hN.1
    rw [N.eq_bot_of_subsingleton]
    exact

中文:
定理 exists_right_complement'_of_coprime
  结论: {N : Subgroup G} [N.Normal]
  证明: by
  by_cases hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_left, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, isComplement'_top_bot⟩
  by_cases hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_right, Nat.card_eq_one_iff_unique] at hN
    have := hN.1
    rw [N.eq_bot_of_subsingleton]
    exact

Depends on / 依赖: Finite, N.card_mul_index, N.eq_bot_of_subsingleton, N.index, Nat.card, Nat.card_eq_one_iff_unique, Nat.coprime_zero_left, Nat.coprime_zero_right, Nat.finite_of_card_ne_zero, _bot_top, _of_coprime_aux, _top_bot, card_eq_one_iff_unique, card_mul_index, coprime_zero_left, coprime_zero_right, eq_bot_of_subsingleton, exists_right_complement, finite_of_card_ne_zero, index_eq_one
-/
theorem exists_right_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) : exists H : Subgroup G, IsComplement' N H := by
  by_cases hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_left, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, isComplement'_top_bot⟩
  by_cases hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_right, Nat.card_eq_one_iff_unique] at hN
    have := hN.1
    rw [N.eq_bot_of_subsingleton]
    exact ⟨⊤, isComplement'_bot_top⟩
  have hN3 : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← N.card_mul_index]
    exact mul_ne_zero hN1 hN2
  exact exists_right_complement'_of_coprime_aux' rfl hN

/--
theorem `exists_left_complement'_of_coprime` / 定理 `exists_left_complement'_of_coprime`

English:
theorem exists_left_complement'_of_coprime
  statement: {N : Subgroup G} [N.Normal]
  proof: Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

中文:
定理 exists_left_complement'_of_coprime
  结论: {N : Subgroup G} [N.Normal]
  证明: Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

Depends on / 依赖: Exists, Exists.imp, IsComplement, _of_coprime, exists_right_complement
-/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) : exists H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

end Subgroup
