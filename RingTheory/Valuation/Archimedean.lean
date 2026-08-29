/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Ring of integers under a given valuation in a multiplicatively archimedean codomain

-/

public section

section Field

variable {F Γ₀ O : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  [CommRing O] [Algebra O F] {v : Valuation F Γ₀}

/--
Instance `MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange` / 实例 `MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange`

English:
instance MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange
  signature: (v : F ->*₀ Γ₀)
  body: ⟨⊥, by simp [bot_eq_zero]⟩
  bot_le a := by simp [bot_eq_zero, ← Subtype.coe_le_coe]
  isBot_zero a := by simp [← Subtype.coe_le_coe]
  mul_lt_mul_of_pos_left := by
    simp only [← Subtype.coe_lt_coe, val_mrange_zero, Submonoid.coe_mul, Subtype.forall,
      MonoidHom.mem_mrange, forall_exists_inde

中文:
实例 带零幺半群态射.instLinearOrderedCommGroupWithZeroMrange
  签名: (v : F ->*₀ Γ₀)
  定义体: ⟨⊥, by simp [bot_eq_zero]⟩
  bot_le a := by simp [bot_eq_zero, ← Subtype.coe_le_coe]
  isBot_zero a := by simp [← Subtype.coe_le_coe]
  mul_lt_mul_of_pos_left := by
    simp only [← Subtype.coe_lt_coe, val_mrange_zero, Submonoid.coe_mul, Subtype.forall,
      MonoidHom.mem_mrange, forall_exists_inde

Depends on / 依赖: bot_eq_zero
-/
instance MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange (v : F ->*₀ Γ₀) :
    LinearOrderedCommGroupWithZero (MonoidHom.mrange v) where
  bot := ⟨⊥, by simp [bot_eq_zero]⟩
  bot_le a := by simp [bot_eq_zero, ← Subtype.coe_le_coe]
  isBot_zero a := by simp [← Subtype.coe_le_coe]
  mul_lt_mul_of_pos_left := by
    simp only [← Subtype.coe_lt_coe, val_mrange_zero, Submonoid.coe_mul, Subtype.forall,
      MonoidHom.mem_mrange, forall_exists_index, forall_apply_eq_imp_iff]
    rintro a ha b c hbc
    gcongr

/--
Instance `Valuation.instLinearOrderedCommGroupWithZeroMrange` / 实例 `Valuation.instLinearOrderedCommGroupWithZeroMrange`

English:
instance Valuation.instLinearOrderedCommGroupWithZeroMrange
  signature: :
  body: inferInstanceAs (LinearOrderedCommGroupWithZero (MonoidHom.mrange (.ofClass v : F ->*₀ Γ₀)))

中文:
实例 赋值.instLinearOrderedCommGroupWithZeroMrange
  签名: :
  定义体: inferInstanceAs (LinearOrderedCommGroupWithZero (MonoidHom.mrange (.ofClass v : F ->*₀ Γ₀)))

Depends on / 依赖: LinearOrderedCommGroupWithZero, MonoidHom, MonoidHom.mrange, mrange, ofClass
-/
instance Valuation.instLinearOrderedCommGroupWithZeroMrange :
    LinearOrderedCommGroupWithZero (MonoidHom.mrange v) :=
  inferInstanceAs (LinearOrderedCommGroupWithZero (MonoidHom.mrange (.ofClass v : F ->*₀ Γ₀)))

namespace Valuation.Integers

open scoped Function in
/--
lemma `wfDvdMonoid_iff_wellFounded_gt_on_v` / 引理 `wfDvdMonoid_iff_wellFounded_gt_on_v`

English:
lemma wfDvdMonoid_iff_wellFounded_gt_on_v
  given: (hv : Integers v O)
  proof: by
  refine ⟨fun _ => wellFounded_dvdNotUnit.mono ?_, fun h => ⟨h.mono ?_⟩⟩ <;>
  simp [Function.onFun, hv.dvdNotUnit_iff_lt]

中文:
引理 wfDvdMonoid_iff_wellFounded_gt_on_v
  条件: (hv : 整数egers v O)
  证明: by
  refine ⟨fun _ => wellFounded_dvdNotUnit.mono ?_, fun h => ⟨h.mono ?_⟩⟩ <;>
  simp [Function.onFun, hv.dvdNotUnit_iff_lt]

Depends on / 依赖: Function, Function.onFun, dvdNotUnit_iff_lt, h.mono, hv.dvdNotUnit_iff_lt, wellFounded_dvdNotUnit, wellFounded_dvdNotUnit.mono
-/
lemma wfDvdMonoid_iff_wellFounded_gt_on_v (hv : Integers v O) :
    WfDvdMonoid O ↔ WellFounded ((· > ·) on (v ∘ algebraMap O F)) := by
  refine ⟨fun _ => wellFounded_dvdNotUnit.mono ?_, fun h => ⟨h.mono ?_⟩⟩ <;>
  simp [Function.onFun, hv.dvdNotUnit_iff_lt]

open scoped Function WithZero in
/--
lemma `wellFounded_gt_on_v_iff_discrete_mrange` / 引理 `wellFounded_gt_on_v_iff_discrete_mrange`

English:
lemma wellFounded_gt_on_v_iff_discrete_mrange
  statement: [Nontrivial (MonoidHom.mrange v)ˣ]
  proof: by
  rw [←
    LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge_gt_iff_nonempty_discrete_of_ne_zero
    one_ne_zero]; rw [← Set.wellFoundedOn_range]
  classical
  refine ⟨fun h => (h.mapsTo Subtype.val ?_).mono' (by simp), fun h => (h.mapsTo ?_ ?_).mono' ?_⟩
  · rintro ⟨_, x, rfl⟩
    simp 

中文:
引理 wellFounded_gt_on_v_iff_discrete_mrange
  结论: [非平凡 (幺半群态射.mrange v)ˣ]
  证明: by
  rw [←
    LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge_gt_iff_nonempty_discrete_of_ne_zero
    one_ne_zero]; rw [← Set.wellFoundedOn_range]
  classical
  refine ⟨fun h => (h.mapsTo Subtype.val ?_).mono' (by simp), fun h => (h.mapsTo ?_ ?_).mono' ?_⟩
  · rintro ⟨_, x, rfl⟩
    simp 

Depends on / 依赖: Function, Function.comp_apply, LinearOrderedCommGroupWithZero, LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge_gt_iff_nonempty_discrete_of_ne_zero, MonoidHom, MonoidHom.mrange, OneMemClass, OneMemClass.coe_one, Set.mem_ofPred_eq, Set.mem_range, Set.wellFoundedOn_range, Subtype, Subtype.coe_le_coe, Subtype.val, classical, coe_le_coe, coe_one, comp_apply, exists_of_le_one, h.mapsTo
-/
lemma wellFounded_gt_on_v_iff_discrete_mrange [Nontrivial (MonoidHom.mrange v)ˣ]
    (hv : Integers v O) :
    WellFounded ((· > ·) on (v ∘ algebraMap O F)) ↔
      Nonempty (MonoidHom.mrange v ≃*o Intᵐ⁰) := by
  rw [←
    LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge_gt_iff_nonempty_discrete_of_ne_zero
    one_ne_zero]; rw [← Set.wellFoundedOn_range]
  classical
  refine ⟨fun h => (h.mapsTo Subtype.val ?_).mono' (by simp), fun h => (h.mapsTo ?_ ?_).mono' ?_⟩
  · rintro ⟨_, x, rfl⟩
    simp only [← Subtype.coe_le_coe, OneMemClass.coe_one, Set.mem_ofPred_eq, Set.mem_range,
      Function.comp_apply]
    intro hx
    obtain ⟨y, rfl⟩ := hv.exists_of_le_one hx
    exact ⟨y, by simp⟩
  · exact fun x => if hx : x in MonoidHom.mrange v then ⟨x, hx⟩ else 1
  · intro
    simp only [Set.mem_range, Function.comp_apply, MonoidHom.mem_mrange, Set.mem_ofPred_eq,
      forall_exists_index]
    rintro x rfl
    simp [← Subtype.coe_le_coe, hv.map_le_one]
  · simp [Function.onFun]

/--
lemma `isPrincipalIdealRing_iff_not_denselyOrdered` / 引理 `isPrincipalIdealRing_iff_not_denselyOrdered`

English:
lemma isPrincipalIdealRing_iff_not_denselyOrdered
  statement: [MulArchimedean (MonoidHom.mrange v)]
  proof: by
  refine ⟨fun _ => not_denselyOrdered_of_isPrincipalIdealRing hv, fun H => ?_⟩
  rcases subsingleton_or_nontrivial (MonoidHom.mrange v)ˣ with hs | _
  · have := bijective_algebraMap_of_subsingleton_units_mrange hv
    exact .of_surjective _ (RingEquiv.ofBijective _ this).symm.surjective
  have : 

中文:
引理 isPrincipalIdealRing_iff_not_denselyOrdered
  结论: [MulArchimedean (幺半群态射.mrange v)]
  证明: by
  refine ⟨fun _ => not_denselyOrdered_of_isPrincipalIdealRing hv, fun H => ?_⟩
  rcases subsingleton_or_nontrivial (MonoidHom.mrange v)ˣ with hs | _
  · have := bijective_algebraMap_of_subsingleton_units_mrange hv
    exact .of_surjective _ (RingEquiv.ofBijective _ this).symm.surjective
  have : 

Depends on / 依赖: IsBezout, IsBezout.TFAE, IsDomain, MonoidHom, MonoidHom.mrange, RingEquiv, RingEquiv.ofBijective, ValuationRing, ValuationRing.of_integers, bijective_algebraMap_of_subsingleton_units_mrange, hom_inj, hv.hom_inj.isDomain, hv.wellFounded_gt_, hv.wfDvdMonoid_iff_wellFounded_gt_on_v, isDomain, mrange, not_denselyOrdered_of_isPrincipalIdealRing, ofBijective, of_integers, of_surjective
-/
lemma isPrincipalIdealRing_iff_not_denselyOrdered [MulArchimedean (MonoidHom.mrange v)]
    (hv : Integers v O) :
    IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (Set.range v) := by
  refine ⟨fun _ => not_denselyOrdered_of_isPrincipalIdealRing hv, fun H => ?_⟩
  rcases subsingleton_or_nontrivial (MonoidHom.mrange v)ˣ with hs | _
  · have := bijective_algebraMap_of_subsingleton_units_mrange hv
    exact .of_surjective _ (RingEquiv.ofBijective _ this).symm.surjective
  have : IsDomain O := hv.hom_inj.isDomain
  have : ValuationRing O := ValuationRing.of_integers v hv
  have := ((IsBezout.TFAE (R := O)).out 1 3)
  rw [this]; rw [hv.wfDvdMonoid_iff_wellFounded_gt_on_v]; rw [hv.wellFounded_gt_on_v_iff_discrete_mrange]; rw [LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
  exact H

/--
lemma `isPrincipalIdealRing_iff_not_denselyOrdered_mrange` / 引理 `isPrincipalIdealRing_iff_not_denselyOrdered_mrange`

English:
lemma isPrincipalIdealRing_iff_not_denselyOrdered_mrange
  statement: [MulArchimedean (MonoidHom.mrange v)]
  proof: isPrincipalIdealRing_iff_not_denselyOrdered hv

中文:
引理 isPrincipalIdealRing_iff_not_denselyOrdered_mrange
  结论: [MulArchimedean (幺半群态射.mrange v)]
  证明: isPrincipalIdealRing_iff_not_denselyOrdered hv

Depends on / 依赖: isPrincipalIdealRing_iff_not_denselyOrdered
-/
lemma isPrincipalIdealRing_iff_not_denselyOrdered_mrange [MulArchimedean (MonoidHom.mrange v)]
    (hv : Integers v O) :
    IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (MonoidHom.mrange v) :=
  isPrincipalIdealRing_iff_not_denselyOrdered hv

end Valuation.Integers

end Field
