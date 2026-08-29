/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Principal

/-!
# Ordinal arithmetic with cardinals

This file collects results about the cardinality of different ordinal operations.
-/

public section

universe u v
open Cardinal Ordinal Set

/-! ### Cardinal operations with ordinal indices -/

namespace Cardinal

/--
lemma `mk_biUnion_le_of_le_lift` / 引理 `mk_biUnion_le_of_le_lift`

English:
lemma mk_biUnion_le_of_le_lift
  statement: {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
  proof: by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← ToType.mk.symm.surjective.range_comp]
  rw [← lift_le.{u}]
  apply ((mk_iUnion_le_lift _).trans _).trans_eq (mul_eq_self (aleph0_le_lift.2 hc))
  rw [mk_toType]
  refine mul_le_mul' ho (ciSup_le' ?_)
  intro i
  simpa using hA _ i.toOrd.pro

中文:
引理 mk_biUnion_le_of_le_lift
  结论: {β : 类型v} {o : Ordinal.{u}} {c : Cardinal.{v}}
  证明: by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← ToType.mk.symm.surjective.range_comp]
  rw [← lift_le.{u}]
  apply ((mk_iUnion_le_lift _).trans _).trans_eq (mul_eq_self (aleph0_le_lift.2 hc))
  rw [mk_toType]
  refine mul_le_mul' ho (ciSup_le' ?_)
  intro i
  simpa using hA _ i.toOrd.pro

Depends on / 依赖: ToType, ToType.mk.symm.surjective.range_comp, aleph0_le_lift, biUnion_eq_iUnion, ciSup_le, i.toOrd.prop, iUnion, lift_le, mem_Iio, mk_iUnion_le_lift, mk_toType, mul_eq_self, mul_le_mul, range_comp, simp_rw, surjective, trans_eq
-/
lemma mk_biUnion_le_of_le_lift {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : lift.{v} o.card <= lift.{u} c) (hc : ℵ₀ <= c) (A : Ordinal -> Set β)
    (hA : forall j < o, #(A j) <= c) : #(⋃ j < o, A j) <= c := by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← ToType.mk.symm.surjective.range_comp]
  rw [← lift_le.{u}]
  apply ((mk_iUnion_le_lift _).trans _).trans_eq (mul_eq_self (aleph0_le_lift.2 hc))
  rw [mk_toType]
  refine mul_le_mul' ho (ciSup_le' ?_)
  intro i
  simpa using hA _ i.toOrd.prop

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_lift_le_of_le := mk_biUnion_le_of_le_lift

/--
lemma `mk_biUnion_le_of_le` / 引理 `mk_biUnion_le_of_le`

English:
lemma mk_biUnion_le_of_le
  statement: {β : Type*} {o : Ordinal} {c : Cardinal}
  proof: by
  apply mk_biUnion_le_of_le_lift _ hc A hA
  rwa [Cardinal.lift_le]

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_le_of_le := mk_biUnion_le_of_le

中文:
引理 mk_biUnion_le_of_le
  结论: {β : 类型} {o : Ordinal} {c : Cardinal}
  证明: by
  apply mk_biUnion_le_of_le_lift _ hc A hA
  rwa [Cardinal.lift_le]

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_le_of_le := mk_biUnion_le_of_le

Depends on / 依赖: Cardinal, Cardinal.lift_le, lift_le, mk_biUnion_le_of_le_lift
-/
lemma mk_biUnion_le_of_le {β : Type*} {o : Ordinal} {c : Cardinal}
    (ho : o.card <= c) (hc : ℵ₀ <= c) (A : Ordinal -> Set β)
    (hA : forall j < o, #(A j) <= c) : #(⋃ j < o, A j) <= c := by
  apply mk_biUnion_le_of_le_lift _ hc A hA
  rwa [Cardinal.lift_le]

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_le_of_le := mk_biUnion_le_of_le

end Cardinal

/-! ### Cardinality of ordinals -/

namespace Ordinal

/--
theorem `lift_card_iSup_le_sum_card` / 定理 `lift_card_iSup_le_sum_card`

English:
theorem lift_card_iSup_le_sum_card
  given: {ι : Type u} (f : ι -> Ordinal.{v})
  proof: by
  by_cases! hf : ¬ BddAbove (range f)
  · simp [ciSup_of_not_bddAbove hf]
  simp_rw [← mk_toType]
  rw [← mk_sigma]; rw [← Cardinal.lift_id'.{v} #(Σ _]; rw [_)]; rw [← Cardinal.lift_umax.{v]; rw [u}]
  apply lift_mk_le_lift_mk_of_surjective (f := .mk ∘ (⟨·.2.toOrd,
    (mem_Iio.mp (ToType.toOrd _

中文:
定理 lift_card_iSup_le_sum_card
  条件: {ι : 类型u} (f : ι -> Ordinal.{v})
  证明: by
  by_cases! hf : ¬ BddAbove (range f)
  · simp [ciSup_of_not_bddAbove hf]
  simp_rw [← mk_toType]
  rw [← mk_sigma]; rw [← Cardinal.lift_id'.{v} #(Σ _]; rw [_)]; rw [← Cardinal.lift_umax.{v]; rw [u}]
  apply lift_mk_le_lift_mk_of_surjective (f := .mk ∘ (⟨·.2.toOrd,
    (mem_Iio.mp (ToType.toOrd _

Depends on / 依赖: BddAbove, Cardinal, Cardinal.lift_id, Cardinal.lift_umax, EquivLike, EquivLike.comp_surjective, ToType, ToType.toOrd, ciSup_of_not_bddAbove, comp_surjective, le_ciSup, lift_id, lift_mk_le_lift_mk_of_surjective, lift_umax, lt_ciSup_iff, mem_Iio, mem_Iio.mp, mk_sigma, mk_toType, simp_rw
-/
theorem lift_card_iSup_le_sum_card {ι : Type u} (f : ι -> Ordinal.{v}) :
    Cardinal.lift.{u} (⨆ i, f i).card <= Cardinal.sum fun i => (f i).card := by
  by_cases! hf : ¬ BddAbove (range f)
  · simp [ciSup_of_not_bddAbove hf]
  simp_rw [← mk_toType]
  rw [← mk_sigma]; rw [← Cardinal.lift_id'.{v} #(Σ _]; rw [_)]; rw [← Cardinal.lift_umax.{v]; rw [u}]
  apply lift_mk_le_lift_mk_of_surjective (f := .mk ∘ (⟨·.2.toOrd,
    (mem_Iio.mp (ToType.toOrd _).2).trans_le (le_ciSup hf _)⟩))
  rw [EquivLike.comp_surjective]
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ := (lt_ciSup_iff' hf).mp hx
  exact ⟨⟨i, .mk ⟨x, hi⟩⟩, by simp⟩

/--
theorem `card_iSup_le_sum_card` / 定理 `card_iSup_le_sum_card`

English:
theorem card_iSup_le_sum_card
  given: {ι : Type u} (f : ι -> Ordinal.{max u v})
  proof: by
  have := lift_card_iSup_le_sum_card f
  rwa [Cardinal.lift_id'] at this

中文:
定理 card_iSup_le_sum_card
  条件: {ι : 类型u} (f : ι -> Ordinal.{max u v})
  证明: by
  have := lift_card_iSup_le_sum_card f
  rwa [Cardinal.lift_id'] at this

Depends on / 依赖: Cardinal, Cardinal.lift_id, lift_card_iSup_le_sum_card, lift_id
-/
theorem card_iSup_le_sum_card {ι : Type u} (f : ι -> Ordinal.{max u v}) :
    (⨆ i, f i).card <= Cardinal.sum fun i => (f i).card := by
  have := lift_card_iSup_le_sum_card f
  rwa [Cardinal.lift_id'] at this

/--
theorem `card_iSup_Iio_le_sum_card` / 定理 `card_iSup_Iio_le_sum_card`

English:
theorem card_iSup_Iio_le_sum_card
  given: {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v})
  proof: by
  apply le_of_eq_of_le (congr_arg _ _).symm (card_iSup_le_sum_card _)
  simpa using ToType.mk.symm.iSup_comp (g := fun x => f x)

中文:
定理 card_iSup_Iio_le_sum_card
  条件: {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v})
  证明: by
  apply le_of_eq_of_le (congr_arg _ _).symm (card_iSup_le_sum_card _)
  simpa using ToType.mk.symm.iSup_comp (g := fun x => f x)

Depends on / 依赖: ToType, ToType.mk.symm.iSup_comp, card_iSup_le_sum_card, congr_arg, iSup_comp, le_of_eq_of_le
-/
theorem card_iSup_Iio_le_sum_card {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card <= Cardinal.sum fun i : o.ToType => (f i.toOrd).card := by
  apply le_of_eq_of_le (congr_arg _ _).symm (card_iSup_le_sum_card _)
  simpa using ToType.mk.symm.iSup_comp (g := fun x => f x)

/--
theorem `card_iSup_Iio_le_card_mul_iSup` / 定理 `card_iSup_Iio_le_card_mul_iSup`

English:
theorem card_iSup_Iio_le_card_mul_iSup
  given: {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v})
  proof: by
  apply (card_iSup_Iio_le_sum_card f).trans
  convert! ← sum_le_lift_mk_mul_iSup _
  · exact mk_toType o
  · exact ToType.mk.symm.iSup_comp (g := fun x => (f x).card)

中文:
定理 card_iSup_Iio_le_card_mul_iSup
  条件: {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v})
  证明: by
  apply (card_iSup_Iio_le_sum_card f).trans
  convert! ← sum_le_lift_mk_mul_iSup _
  · exact mk_toType o
  · exact ToType.mk.symm.iSup_comp (g := fun x => (f x).card)

Depends on / 依赖: ToType, ToType.mk.symm.iSup_comp, card_iSup_Iio_le_sum_card, convert, iSup_comp, mk_toType, sum_le_lift_mk_mul_iSup
-/
theorem card_iSup_Iio_le_card_mul_iSup {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card <= Cardinal.lift.{v} o.card * ⨆ a : Iio o, (f a).card := by
  apply (card_iSup_Iio_le_sum_card f).trans
  convert! ← sum_le_lift_mk_mul_iSup _
  · exact mk_toType o
  · exact ToType.mk.symm.iSup_comp (g := fun x => (f x).card)

/--
theorem `card_iSup_le_lift` / 定理 `card_iSup_le_lift`

English:
theorem card_iSup_le_lift
  statement: {ι : Type u} {c : Cardinal} {f : ι -> Ordinal.{v}}
  proof: by
  by_cases! hc : c < ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    rw [card_le_nat]
    refine ciSup_le' fun i => ?_
    simpa using hf i
  · rw [← Cardinal.lift_le.{u}]
    apply (lift_card_iSup_le_sum_card ..).trans ((sum_le_lift_mk_mul_iSup_lift _).trans _)
    rw [← mul_eq_self hc]; rw [Cardin

中文:
定理 card_iSup_le_lift
  结论: {ι : 类型u} {c : Cardinal} {f : ι -> Ordinal.{v}}
  证明: by
  by_cases! hc : c < ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    rw [card_le_nat]
    refine ciSup_le' fun i => ?_
    simpa using hf i
  · rw [← Cardinal.lift_le.{u}]
    apply (lift_card_iSup_le_sum_card ..).trans ((sum_le_lift_mk_mul_iSup_lift _).trans _)
    rw [← mul_eq_self hc]; rw [Cardin

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.lift_mul, card_le_nat, ciSup_le, lift_card, lift_card_iSup_le_sum_card, lift_le, lift_mul, lt_aleph0, mul_eq_self, mul_le_mul, sum_le_lift_mk_mul_iSup_lift
-/
theorem card_iSup_le_lift {ι : Type u} {c : Cardinal} {f : ι -> Ordinal.{v}}
    (hι : Cardinal.lift.{v} #ι <= Cardinal.lift.{u} c) (hf : forall i, (f i).card <= c) :
    (⨆ i, f i).card <= c := by
  by_cases! hc : c < ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    rw [card_le_nat]
    refine ciSup_le' fun i => ?_
    simpa using hf i
  · rw [← Cardinal.lift_le.{u}]
    apply (lift_card_iSup_le_sum_card ..).trans ((sum_le_lift_mk_mul_iSup_lift _).trans _)
    rw [← mul_eq_self hc]; rw [Cardinal.lift_mul]
    apply mul_le_mul' hι (ciSup_le' _)
    simpa [← lift_card]

/--
theorem `card_iSup_le` / 定理 `card_iSup_le`

English:
theorem card_iSup_le
  statement: {ι : Type*} {c : Cardinal} {f : ι -> Ordinal}
  proof: by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_le_lift hι hf

中文:
定理 card_iSup_le
  结论: {ι : 类型} {c : Cardinal} {f : ι -> Ordinal}
  证明: by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_le_lift hι hf

Depends on / 依赖: Cardinal, Cardinal.lift_le, card_iSup_le_lift, lift_le
-/
theorem card_iSup_le {ι : Type*} {c : Cardinal} {f : ι -> Ordinal}
    (hι : #ι <= c) (hf : forall i, (f i).card <= c) : (⨆ i, f i).card <= c := by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_le_lift hι hf

/--
theorem `card_iSup_Iio_le_of_lift` / 定理 `card_iSup_Iio_le_of_lift`

English:
theorem card_iSup_Iio_le_of_lift
  statement: {o : Ordinal.{u}} {c : Cardinal} {f : Iio o -> Ordinal.{v}}
  proof: by
  apply card_iSup_le_lift _ hf
  conv_rhs => rw [← Cardinal.lift_lift.{u, u + 1}]
  rwa [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, ← Cardinal.lift_lift.{v, u + 1},
    Cardinal.lift_le]

中文:
定理 card_iSup_Iio_le_of_lift
  结论: {o : Ordinal.{u}} {c : Cardinal} {f : Iio o -> Ordinal.{v}}
  证明: by
  apply card_iSup_le_lift _ hf
  conv_rhs => rw [← Cardinal.lift_lift.{u, u + 1}]
  rwa [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, ← Cardinal.lift_lift.{v, u + 1},
    Cardinal.lift_le]

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.lift_lift, Cardinal.mk_Iio_ordinal, card_iSup_le_lift, conv_rhs, lift_le, lift_lift, mk_Iio_ordinal
-/
theorem card_iSup_Iio_le_of_lift {o : Ordinal.{u}} {c : Cardinal} {f : Iio o -> Ordinal.{v}}
    (hι : Cardinal.lift.{v} o.card <= Cardinal.lift.{u} c) (hf : forall i, (f i).card <= c) :
    (⨆ i, f i).card <= c := by
  apply card_iSup_le_lift _ hf
  conv_rhs => rw [← Cardinal.lift_lift.{u, u + 1}]
  rwa [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, ← Cardinal.lift_lift.{v, u + 1},
    Cardinal.lift_le]

/--
theorem `card_iSup_Iio_le` / 定理 `card_iSup_Iio_le`

English:
theorem card_iSup_Iio_le
  statement: {o : Ordinal} {c : Cardinal} {f : Iio o -> Ordinal}
  proof: by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_Iio_le_of_lift hι hf

中文:
定理 card_iSup_Iio_le
  结论: {o : Ordinal} {c : Cardinal} {f : Iio o -> Ordinal}
  证明: by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_Iio_le_of_lift hι hf

Depends on / 依赖: Cardinal, Cardinal.lift_le, card_iSup_Iio_le_of_lift, lift_le
-/
theorem card_iSup_Iio_le {o : Ordinal} {c : Cardinal} {f : Iio o -> Ordinal}
    (hι : o.card <= c) (hf : forall i, (f i).card <= c) : (⨆ i, f i).card <= c := by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_Iio_le_of_lift hι hf

/--
theorem `card_sSup_le` / 定理 `card_sSup_le`

English:
theorem card_sSup_le
  statement: {c : Cardinal} {s : Set Ordinal.{u}}
  proof: by
  rw [sSup_eq_iSup']
  apply card_iSup_le_lift
  · rwa [Cardinal.lift_id'.{u, u + 1}]
  · simpa

中文:
定理 card_sSup_le
  结论: {c : Cardinal} {s : Set Ordinal.{u}}
  证明: by
  rw [sSup_eq_iSup']
  apply card_iSup_le_lift
  · rwa [Cardinal.lift_id'.{u, u + 1}]
  · simpa

Depends on / 依赖: Cardinal, Cardinal.lift_id, card_iSup_le_lift, lift_id, sSup_eq_iSup
-/
theorem card_sSup_le {c : Cardinal} {s : Set Ordinal.{u}}
    (hs : #s <= Cardinal.lift.{u + 1} c) (hs' : forall x in s, x.card <= c) : (sSup s).card <= c := by
  rw [sSup_eq_iSup']
  apply card_iSup_le_lift
  · rwa [Cardinal.lift_id'.{u, u + 1}]
  · simpa

/--
theorem `card_opow_le_of_omega0_le_left` / 定理 `card_opow_le_of_omega0_le_left`

English:
theorem card_opow_le_of_omega0_le_left
  given: {a : Ordinal} (ha : ω <= a) (b : Ordinal)
  proof: by
  induction b using limitRecOn with
  | zero => simpa using one_lt_omega0.le.trans ha
  | add_one b IH =>
    rw [opow_add_one]; rw [card_mul]; rw [card_add_one]; rw [Cardinal.mul_eq_max_of_aleph0_le_right]; rw [max_comm]
    · grw [IH]
      rw [← max_assoc]; rw [max_self]
      grw [← le_self_a

中文:
定理 card_opow_le_of_omega0_le_left
  条件: {a : Ordinal} (ha : ω <= a) (b : Ordinal)
  证明: by
  induction b using limitRecOn with
  | zero => simpa using one_lt_omega0.le.trans ha
  | add_one b IH =>
    rw [opow_add_one]; rw [card_mul]; rw [card_add_one]; rw [Cardinal.mul_eq_max_of_aleph0_le_right]; rw [max_comm]
    · grw [IH]
      rw [← max_assoc]; rw [max_self]
      grw [← le_self_a

Depends on / 依赖: Cardinal, Cardinal.mul_eq_max_of_aleph0_le_right, add_one, aleph0_le_card, apply_of_isSuccLimit, card_add_one, card_eq_zero, card_iSup_Iio_le, card_mul, isNormal_opow, le_self_add, limitRecOn, max_assoc, max_comm, max_self, mul_eq_max_of_aleph0_le_right, ne_eq, not_ge, omega0_pos, omega0_pos.not_ge
-/
theorem card_opow_le_of_omega0_le_left {a : Ordinal} (ha : ω <= a) (b : Ordinal) :
    (a ^ b).card <= max a.card b.card := by
  induction b using limitRecOn with
  | zero => simpa using one_lt_omega0.le.trans ha
  | add_one b IH =>
    rw [opow_add_one]; rw [card_mul]; rw [card_add_one]; rw [Cardinal.mul_eq_max_of_aleph0_le_right]; rw [max_comm]
    · grw [IH]
      rw [← max_assoc]; rw [max_self]
      grw [← le_self_add]
    · rw [ne_eq, card_eq_zero, opow_eq_zero]
      rintro ⟨rfl, -⟩
      cases omega0_pos.not_ge ha
    · rwa [aleph0_le_card]
  | limit b hb IH =>
    rw [(isNormal_opow (one_lt_omega0.trans_le ha)).apply_of_isSuccLimit hb]
    exact card_iSup_Iio_le (le_max_right ..) fun i =>
      (IH i i.2).trans (max_le_max_left _ (card_le_card i.2.le))

/--
theorem `card_opow_le_of_omega0_le_right` / 定理 `card_opow_le_of_omega0_le_right`

English:
theorem card_opow_le_of_omega0_le_right
  given: (a : Ordinal) {b : Ordinal} (hb : ω <= b)
  proof: by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · apply (card_le_card <| opow_le_opow_left b (natCast_lt_omega0 n).le).trans
    apply (card_opow_le_of_omega0_le_left le_rfl _).trans
    simp [hb]
  · exact card_opow_le_of_omega0_le_left ha b

中文:
定理 card_opow_le_of_omega0_le_right
  条件: (a : Ordinal) {b : Ordinal} (hb : ω <= b)
  证明: by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · apply (card_le_card <| opow_le_opow_left b (natCast_lt_omega0 n).le).trans
    apply (card_opow_le_of_omega0_le_left le_rfl _).trans
    simp [hb]
  · exact card_opow_le_of_omega0_le_left ha b

Depends on / 依赖: card_le_card, card_opow_le_of_omega0_le_left, eq_natCast_or_omega0_le, le_rfl, natCast_lt_omega0, opow_le_opow_left
-/
theorem card_opow_le_of_omega0_le_right (a : Ordinal) {b : Ordinal} (hb : ω <= b) :
    (a ^ b).card <= max a.card b.card := by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · apply (card_le_card <| opow_le_opow_left b (natCast_lt_omega0 n).le).trans
    apply (card_opow_le_of_omega0_le_left le_rfl _).trans
    simp [hb]
  · exact card_opow_le_of_omega0_le_left ha b

/--
theorem `card_opow_le` / 定理 `card_opow_le`

English:
theorem card_opow_le
  given: (a b : Ordinal)
  statement: (a ^ b).card <= max ℵ₀ (max a.card b.card)
  proof: by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · obtain ⟨m, rfl⟩ | hb := eq_natCast_or_omega0_le b
    · rw [opow_natCast, ← natCast_pow, card_nat]
      exact le_max_of_le_left natCast_le_aleph0
    · exact (card_opow_le_of_omega0_le_right _ hb).trans (le_max_right _ _)
  · exact (card_op

中文:
定理 card_opow_le
  条件: (a b : Ordinal)
  结论: (a ^ b).card <= max ℵ₀ (max a.card b.card)
  证明: by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · obtain ⟨m, rfl⟩ | hb := eq_natCast_or_omega0_le b
    · rw [opow_natCast, ← natCast_pow, card_nat]
      exact le_max_of_le_left natCast_le_aleph0
    · exact (card_opow_le_of_omega0_le_right _ hb).trans (le_max_right _ _)
  · exact (card_op

Depends on / 依赖: card_nat, card_opow_le_of_omega0_le_left, card_opow_le_of_omega0_le_right, eq_natCast_or_omega0_le, le_max_of_le_left, le_max_right, natCast_le_aleph0, natCast_pow, opow_natCast
-/
theorem card_opow_le (a b : Ordinal) : (a ^ b).card <= max ℵ₀ (max a.card b.card) := by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · obtain ⟨m, rfl⟩ | hb := eq_natCast_or_omega0_le b
    · rw [opow_natCast, ← natCast_pow, card_nat]
      exact le_max_of_le_left natCast_le_aleph0
    · exact (card_opow_le_of_omega0_le_right _ hb).trans (le_max_right _ _)
  · exact (card_opow_le_of_omega0_le_left ha _).trans (le_max_right _ _)

/--
theorem `card_opow_eq_of_omega0_le_left` / 定理 `card_opow_eq_of_omega0_le_left`

English:
theorem card_opow_eq_of_omega0_le_left
  given: {a b : Ordinal} (ha : ω <= a) (hb : 0 < b)
  proof: by
  apply (card_opow_le_of_omega0_le_left ha b).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a hb
  · exact right_le_opow b (one_lt_omega0.trans_le ha)

中文:
定理 card_opow_eq_of_omega0_le_left
  条件: {a b : Ordinal} (ha : ω <= a) (hb : 0 < b)
  证明: by
  apply (card_opow_le_of_omega0_le_left ha b).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a hb
  · exact right_le_opow b (one_lt_omega0.trans_le ha)

Depends on / 依赖: antisymm, card_le_card, card_opow_le_of_omega0_le_left, left_le_opow, max_le, one_lt_omega0, one_lt_omega0.trans_le, right_le_opow, trans_le
-/
theorem card_opow_eq_of_omega0_le_left {a b : Ordinal} (ha : ω <= a) (hb : 0 < b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_left ha b).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a hb
  · exact right_le_opow b (one_lt_omega0.trans_le ha)

/--
theorem `card_opow_eq_of_omega0_le_right` / 定理 `card_opow_eq_of_omega0_le_right`

English:
theorem card_opow_eq_of_omega0_le_right
  given: {a b : Ordinal} (ha : 1 < a) (hb : ω <= b)
  proof: by
  apply (card_opow_le_of_omega0_le_right a hb).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a (omega0_pos.trans_le hb)
  · exact right_le_opow b ha

中文:
定理 card_opow_eq_of_omega0_le_right
  条件: {a b : Ordinal} (ha : 1 < a) (hb : ω <= b)
  证明: by
  apply (card_opow_le_of_omega0_le_right a hb).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a (omega0_pos.trans_le hb)
  · exact right_le_opow b ha

Depends on / 依赖: antisymm, card_le_card, card_opow_le_of_omega0_le_right, left_le_opow, max_le, omega0_pos, omega0_pos.trans_le, right_le_opow, trans_le
-/
theorem card_opow_eq_of_omega0_le_right {a b : Ordinal} (ha : 1 < a) (hb : ω <= b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_right a hb).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a (omega0_pos.trans_le hb)
  · exact right_le_opow b ha

/--
theorem `card_omega0_opow` / 定理 `card_omega0_opow`

English:
theorem card_omega0_opow
  given: {a : Ordinal} (h : a != 0)
  statement: card (ω ^ a) = max ℵ₀ a.card
  proof: by
  rw [card_opow_eq_of_omega0_le_left le_rfl h.bot_lt]; rw [card_omega0]

中文:
定理 card_omega0_opow
  条件: {a : Ordinal} (h : a != 0)
  结论: card (ω ^ a) = max ℵ₀ a.card
  证明: by
  rw [card_opow_eq_of_omega0_le_left le_rfl h.bot_lt]; rw [card_omega0]

Depends on / 依赖: bot_lt, card_omega0, card_opow_eq_of_omega0_le_left, h.bot_lt, le_rfl
-/
theorem card_omega0_opow {a : Ordinal} (h : a != 0) : card (ω ^ a) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_left le_rfl h.bot_lt]; rw [card_omega0]

/--
theorem `card_opow_omega0` / 定理 `card_opow_omega0`

English:
theorem card_opow_omega0
  given: {a : Ordinal} (h : 1 < a)
  statement: card (a ^ ω) = max ℵ₀ a.card
  proof: by
  rw [card_opow_eq_of_omega0_le_right h le_rfl]; rw [card_omega0]; rw [max_comm]

中文:
定理 card_opow_omega0
  条件: {a : Ordinal} (h : 1 < a)
  结论: card (a ^ ω) = max ℵ₀ a.card
  证明: by
  rw [card_opow_eq_of_omega0_le_right h le_rfl]; rw [card_omega0]; rw [max_comm]

Depends on / 依赖: ContinuousMul, LipschitzMul, LipschitzMul.continuousMul, card_omega0, card_opow_eq_of_omega0_le_right, continuousMul, le_rfl, max_comm
-/
theorem card_opow_omega0 {a : Ordinal} (h : 1 < a) : card (a ^ ω) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_right h le_rfl]; rw [card_omega0]; rw [max_comm]

/--
theorem `isPrincipal_opow_omega` / 定理 `isPrincipal_opow_omega`

English:
theorem isPrincipal_opow_omega
  given: (o : Ordinal)
  statement: IsPrincipal (· ^ ·) (ω_ o)
  proof: by
  obtain rfl | ho := eq_zero_or_pos o
  · rw [omega_zero]
    exact isPrincipal_opow_omega0
  · intro a b ha hb
    rw [lt_omega_iff_card_lt] at ha hb ⊢
    apply (card_opow_le a b).trans_lt (max_lt _ (max_lt ha hb))
    rwa [← aleph_zero, aleph_lt_aleph]

@[deprecated (since := "2026-03-18")] al

中文:
定理 isPrincipal_opow_omega
  条件: (o : Ordinal)
  结论: IsPrincipal (· ^ ·) (ω_ o)
  证明: by
  obtain rfl | ho := eq_zero_or_pos o
  · rw [omega_zero]
    exact isPrincipal_opow_omega0
  · intro a b ha hb
    rw [lt_omega_iff_card_lt] at ha hb ⊢
    apply (card_opow_le a b).trans_lt (max_lt _ (max_lt ha hb))
    rwa [← aleph_zero, aleph_lt_aleph]

@[deprecated (since := "2026-03-18")] al

Depends on / 依赖: aleph_lt_aleph, aleph_zero, card_opow_le, eq_zero_or_pos, isPrincipal_opow_omega0, lt_omega_iff_card_lt, max_lt, omega_zero, trans_lt
-/
theorem isPrincipal_opow_omega (o : Ordinal) : IsPrincipal (· ^ ·) (ω_ o) := by
  obtain rfl | ho := eq_zero_or_pos o
  · rw [omega_zero]
    exact isPrincipal_opow_omega0
  · intro a b ha hb
    rw [lt_omega_iff_card_lt] at ha hb ⊢
    apply (card_opow_le a b).trans_lt (max_lt _ (max_lt ha hb))
    rwa [← aleph_zero, aleph_lt_aleph]

@[deprecated (since := "2026-03-18")] alias principal_opow_omega := isPrincipal_opow_omega

/--
theorem `IsInitial.isPrincipal_opow` / 定理 `IsInitial.isPrincipal_opow`

English:
theorem IsInitial.isPrincipal_opow
  given: {o : Ordinal} (h : IsInitial o) (ho : ω <= o)
  proof: by
  obtain ⟨a, rfl⟩ := mem_range_omega_iff.2 ⟨ho, h⟩
  exact isPrincipal_opow_omega a

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_opow := IsInitial.isPrincipal_opow

中文:
定理 IsInitial.isPrincipal_opow
  条件: {o : Ordinal} (h : IsInitial o) (ho : ω <= o)
  证明: by
  obtain ⟨a, rfl⟩ := mem_range_omega_iff.2 ⟨ho, h⟩
  exact isPrincipal_opow_omega a

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_opow := IsInitial.isPrincipal_opow

Depends on / 依赖: isPrincipal_opow_omega, mem_range_omega_iff
-/
theorem IsInitial.isPrincipal_opow {o : Ordinal} (h : IsInitial o) (ho : ω <= o) :
    IsPrincipal (· ^ ·) o := by
  obtain ⟨a, rfl⟩ := mem_range_omega_iff.2 ⟨ho, h⟩
  exact isPrincipal_opow_omega a

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_opow := IsInitial.isPrincipal_opow

/--
theorem `isPrincipal_opow_ord` / 定理 `isPrincipal_opow_ord`

English:
theorem isPrincipal_opow_ord
  given: {c : Cardinal} (hc : ℵ₀ <= c)
  statement: IsPrincipal (· ^ ·) c.ord
  proof: by
  apply (isInitial_ord c).isPrincipal_opow
  rwa [omega0_le_ord]

@[deprecated (since := "2026-03-18")] alias principal_opow_ord := isPrincipal_opow_ord

中文:
定理 isPrincipal_opow_ord
  条件: {c : Cardinal} (hc : ℵ₀ <= c)
  结论: IsPrincipal (· ^ ·) c.ord
  证明: by
  apply (isInitial_ord c).isPrincipal_opow
  rwa [omega0_le_ord]

@[deprecated (since := "2026-03-18")] alias principal_opow_ord := isPrincipal_opow_ord

Depends on / 依赖: isInitial_ord, isPrincipal_opow, omega0_le_ord
-/
theorem isPrincipal_opow_ord {c : Cardinal} (hc : ℵ₀ <= c) : IsPrincipal (· ^ ·) c.ord := by
  apply (isInitial_ord c).isPrincipal_opow
  rwa [omega0_le_ord]

@[deprecated (since := "2026-03-18")] alias principal_opow_ord := isPrincipal_opow_ord


/--
theorem `isPrincipal_add_ord` / 定理 `isPrincipal_add_ord`

English:
theorem isPrincipal_add_ord
  given: {c : Cardinal} (hc : ℵ₀ <= c)
  statement: IsPrincipal (· + ·) c.ord
  proof: by
  intro a b ha hb
  rw [lt_ord]; rw [card_add] at *
  exact add_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_add_ord := isPrincipal_add_ord

中文:
定理 isPrincipal_add_ord
  条件: {c : Cardinal} (hc : ℵ₀ <= c)
  结论: IsPrincipal (· + ·) c.ord
  证明: by
  intro a b ha hb
  rw [lt_ord]; rw [card_add] at *
  exact add_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_add_ord := isPrincipal_add_ord

Depends on / 依赖: add_lt_of_lt, card_add, lt_ord
-/
theorem isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀ <= c) : IsPrincipal (· + ·) c.ord := by
  intro a b ha hb
  rw [lt_ord]; rw [card_add] at *
  exact add_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_add_ord := isPrincipal_add_ord

/--
theorem `IsInitial.isPrincipal_add` / 定理 `IsInitial.isPrincipal_add`

English:
theorem IsInitial.isPrincipal_add
  given: {o : Ordinal} (h : IsInitial o) (ho : ω <= o)
  proof: by
  rw [← h.ord_card]
  apply isPrincipal_add_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_add := IsInitial.isPrincipal_add

中文:
定理 IsInitial.isPrincipal_add
  条件: {o : Ordinal} (h : IsInitial o) (ho : ω <= o)
  证明: by
  rw [← h.ord_card]
  apply isPrincipal_add_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_add := IsInitial.isPrincipal_add

Depends on / 依赖: aleph0_le_card, h.ord_card, isPrincipal_add_ord, ord_card
-/
theorem IsInitial.isPrincipal_add {o : Ordinal} (h : IsInitial o) (ho : ω <= o) :
    IsPrincipal (· + ·) o := by
  rw [← h.ord_card]
  apply isPrincipal_add_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_add := IsInitial.isPrincipal_add

/--
theorem `isPrincipal_add_omega` / 定理 `isPrincipal_add_omega`

English:
theorem isPrincipal_add_omega
  given: (o : Ordinal)
  statement: IsPrincipal (· + ·) (ω_ o)
  proof: (isInitial_omega o).isPrincipal_add (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_add_omega := isPrincipal_add_omega

中文:
定理 isPrincipal_add_omega
  条件: (o : Ordinal)
  结论: IsPrincipal (· + ·) (ω_ o)
  证明: (isInitial_omega o).isPrincipal_add (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_add_omega := isPrincipal_add_omega

Depends on / 依赖: isInitial_omega, isPrincipal_add, omega0_le_omega
-/
theorem isPrincipal_add_omega (o : Ordinal) : IsPrincipal (· + ·) (ω_ o) :=
  (isInitial_omega o).isPrincipal_add (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_add_omega := isPrincipal_add_omega

/--
theorem `isPrincipal_mul_ord` / 定理 `isPrincipal_mul_ord`

English:
theorem isPrincipal_mul_ord
  given: {c : Cardinal} (hc : ℵ₀ <= c)
  statement: IsPrincipal (· * ·) c.ord
  proof: by
  intro a b ha hb
  rw [lt_ord]; rw [card_mul] at *
  exact mul_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_mul_ord := isPrincipal_mul_ord

中文:
定理 isPrincipal_mul_ord
  条件: {c : Cardinal} (hc : ℵ₀ <= c)
  结论: IsPrincipal (· * ·) c.ord
  证明: by
  intro a b ha hb
  rw [lt_ord]; rw [card_mul] at *
  exact mul_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_mul_ord := isPrincipal_mul_ord

Depends on / 依赖: card_mul, lt_ord, mul_lt_of_lt
-/
theorem isPrincipal_mul_ord {c : Cardinal} (hc : ℵ₀ <= c) : IsPrincipal (· * ·) c.ord := by
  intro a b ha hb
  rw [lt_ord]; rw [card_mul] at *
  exact mul_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_mul_ord := isPrincipal_mul_ord

/--
theorem `IsInitial.isPrincipal_mul` / 定理 `IsInitial.isPrincipal_mul`

English:
theorem IsInitial.isPrincipal_mul
  given: {o : Ordinal} (h : IsInitial o) (ho : ω <= o)
  proof: by
  rw [← h.ord_card]
  apply isPrincipal_mul_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_mul := IsInitial.isPrincipal_mul

中文:
定理 IsInitial.isPrincipal_mul
  条件: {o : Ordinal} (h : IsInitial o) (ho : ω <= o)
  证明: by
  rw [← h.ord_card]
  apply isPrincipal_mul_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_mul := IsInitial.isPrincipal_mul

Depends on / 依赖: ContinuousSMul, IsBoundedSMul, IsBoundedSMul.continuousSMul, aleph0_le_card, continuousSMul, h.ord_card, isPrincipal_mul_ord, ord_card
-/
theorem IsInitial.isPrincipal_mul {o : Ordinal} (h : IsInitial o) (ho : ω <= o) :
    IsPrincipal (· * ·) o := by
  rw [← h.ord_card]
  apply isPrincipal_mul_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_mul := IsInitial.isPrincipal_mul

/--
theorem `isPrincipal_mul_omega` / 定理 `isPrincipal_mul_omega`

English:
theorem isPrincipal_mul_omega
  given: (o : Ordinal)
  statement: IsPrincipal (· * ·) (ω_ o)
  proof: (isInitial_omega o).isPrincipal_mul (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_mul_omega := isPrincipal_mul_omega

中文:
定理 isPrincipal_mul_omega
  条件: (o : Ordinal)
  结论: IsPrincipal (· * ·) (ω_ o)
  证明: (isInitial_omega o).isPrincipal_mul (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_mul_omega := isPrincipal_mul_omega

Depends on / 依赖: IsBoundedSMul, IsBoundedSMul.toUniformContinuousConstSMul, isInitial_omega, isPrincipal_mul, omega0_le_omega, toUniformContinuousConstSMul
-/
theorem isPrincipal_mul_omega (o : Ordinal) : IsPrincipal (· * ·) (ω_ o) :=
  (isInitial_omega o).isPrincipal_mul (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_mul_omega := isPrincipal_mul_omega

end Ordinal
