/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Metrizable.Real

/-!
# Limsup and liminf of reals

This file compiles filter-related results about `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

public section


open Filter ENNReal
open scoped NNReal

namespace Real
variable {ι : Type*} {f : Filter ι} {u : ι -> Real}

@[simp]
/--
lemma `limsSup_of_not_isCobounded` / 引理 `limsSup_of_not_isCobounded`

English:
lemma limsSup_of_not_isCobounded
  given: {f : Filter Real} (hf : ¬ f.IsCobounded (· <= ·))
  proof: by rwa [limsSup, sInf_of_not_bddBelow]

@[simp]

中文:
引理 limsSup_of_not_isCobounded
  条件: {f : Filter 实数} (hf : ¬ f.IsCobounded (· <= ·))
  证明: by rwa [limsSup, sInf_of_not_bddBelow]

@[simp]

Depends on / 依赖: limsSup, sInf_of_not_bddBelow
-/
lemma limsSup_of_not_isCobounded {f : Filter Real} (hf : ¬ f.IsCobounded (· <= ·)) :
    limsSup f = 0 := by rwa [limsSup, sInf_of_not_bddBelow]

@[simp]
/--
lemma `limsSup_of_not_isBounded` / 引理 `limsSup_of_not_isBounded`

English:
lemma limsSup_of_not_isBounded
  given: {f : Filter Real} (hf : ¬ f.IsBounded (· <= ·))
  statement: limsSup f = 0
  proof: by
  rw [limsSup]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]

中文:
引理 limsSup_of_not_isBounded
  条件: {f : Filter 实数} (hf : ¬ f.IsBounded (· <= ·))
  结论: limsSup f = 0
  证明: by
  rw [limsSup]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]

Depends on / 依赖: IsBounded, Set.eq_empty_iff_forall_notMem, convert, eq_empty_iff_forall_notMem, limsSup, sInf_empty
-/
lemma limsSup_of_not_isBounded {f : Filter Real} (hf : ¬ f.IsBounded (· <= ·)) : limsSup f = 0 := by
  rw [limsSup]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
/--
lemma `limsInf_of_not_isCobounded` / 引理 `limsInf_of_not_isCobounded`

English:
lemma limsInf_of_not_isCobounded
  given: {f : Filter Real} (hf : ¬ f.IsCobounded (· >= ·))
  proof: by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]

中文:
引理 limsInf_of_not_isCobounded
  条件: {f : Filter 实数} (hf : ¬ f.IsCobounded (· >= ·))
  证明: by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]

Depends on / 依赖: limsInf, sSup_of_not_bddAbove
-/
lemma limsInf_of_not_isCobounded {f : Filter Real} (hf : ¬ f.IsCobounded (· >= ·)) :
    limsInf f = 0 := by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]
/--
lemma `limsInf_of_not_isBounded` / 引理 `limsInf_of_not_isBounded`

English:
lemma limsInf_of_not_isBounded
  given: {f : Filter Real} (hf : ¬ f.IsBounded (· >= ·))
  statement: limsInf f = 0
  proof: by
  rw [limsInf]
  convert! sSup_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]

中文:
引理 limsInf_of_not_isBounded
  条件: {f : Filter 实数} (hf : ¬ f.IsBounded (· >= ·))
  结论: limsInf f = 0
  证明: by
  rw [limsInf]
  convert! sSup_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]

Depends on / 依赖: IsBounded, Set.eq_empty_iff_forall_notMem, convert, eq_empty_iff_forall_notMem, limsInf, sSup_empty
-/
lemma limsInf_of_not_isBounded {f : Filter Real} (hf : ¬ f.IsBounded (· >= ·)) : limsInf f = 0 := by
  rw [limsInf]
  convert! sSup_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
/--
lemma `limsup_of_not_isCoboundedUnder` / 引理 `limsup_of_not_isCoboundedUnder`

English:
lemma limsup_of_not_isCoboundedUnder
  given: (hf : ¬ f.IsCoboundedUnder (· <= ·) u)
  statement: limsup u f = 0
  proof: limsSup_of_not_isCobounded hf

@[simp]

中文:
引理 limsup_of_not_isCoboundedUnder
  条件: (hf : ¬ f.IsCoboundedUnder (· <= ·) u)
  结论: limsup u f = 0
  证明: limsSup_of_not_isCobounded hf

@[simp]

Depends on / 依赖: limsSup_of_not_isCobounded
-/
lemma limsup_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· <= ·) u) : limsup u f = 0 :=
  limsSup_of_not_isCobounded hf

@[simp]
/--
lemma `limsup_of_not_isBoundedUnder` / 引理 `limsup_of_not_isBoundedUnder`

English:
lemma limsup_of_not_isBoundedUnder
  given: (hf : ¬ f.IsBoundedUnder (· <= ·) u)
  statement: limsup u f = 0
  proof: limsSup_of_not_isBounded hf

@[simp]

中文:
引理 limsup_of_not_isBoundedUnder
  条件: (hf : ¬ f.IsBoundedUnder (· <= ·) u)
  结论: limsup u f = 0
  证明: limsSup_of_not_isBounded hf

@[simp]

Depends on / 依赖: limsSup_of_not_isBounded
-/
lemma limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· <= ·) u) : limsup u f = 0 :=
  limsSup_of_not_isBounded hf

@[simp]
/--
lemma `liminf_of_not_isCoboundedUnder` / 引理 `liminf_of_not_isCoboundedUnder`

English:
lemma liminf_of_not_isCoboundedUnder
  given: (hf : ¬ f.IsCoboundedUnder (· >= ·) u)
  statement: liminf u f = 0
  proof: limsInf_of_not_isCobounded hf

@[simp]

中文:
引理 liminf_of_not_isCoboundedUnder
  条件: (hf : ¬ f.IsCoboundedUnder (· >= ·) u)
  结论: liminf u f = 0
  证明: limsInf_of_not_isCobounded hf

@[simp]

Depends on / 依赖: limsInf_of_not_isCobounded
-/
lemma liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· >= ·) u) : liminf u f = 0 :=
  limsInf_of_not_isCobounded hf

@[simp]
/--
lemma `liminf_of_not_isBoundedUnder` / 引理 `liminf_of_not_isBoundedUnder`

English:
lemma liminf_of_not_isBoundedUnder
  given: (hf : ¬ f.IsBoundedUnder (· >= ·) u)
  statement: liminf u f = 0
  proof: limsInf_of_not_isBounded hf

中文:
引理 liminf_of_not_isBoundedUnder
  条件: (hf : ¬ f.IsBoundedUnder (· >= ·) u)
  结论: liminf u f = 0
  证明: limsInf_of_not_isBounded hf

Depends on / 依赖: limsInf_of_not_isBounded
-/
lemma liminf_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· >= ·) u) : liminf u f = 0 :=
  limsInf_of_not_isBounded hf

end Real

namespace NNReal
variable {ι : Type*} {f : Filter ι} {u : ι -> Real>=0}

/--
lemma `isBoundedUnder_le_toReal` / 引理 `isBoundedUnder_le_toReal`

English:
lemma isBoundedUnder_le_toReal
  proof: by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by filter_upwards [hb]; simp +contextual⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩

中文:
引理 isBoundedUnder_le_toReal
  证明: by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by filter_upwards [hb]; simp +contextual⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩
-/
@[simp, norm_cast] lemma isBoundedUnder_le_toReal :
    IsBoundedUnder (· <= ·) f (fun i => (u i : Real)) ↔ IsBoundedUnder (· <= ·) f u := by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by filter_upwards [hb]; simp +contextual⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩

/--
lemma `isBoundedUnder_ge_toReal` / 引理 `isBoundedUnder_ge_toReal`

English:
lemma isBoundedUnder_ge_toReal
  proof: by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by simpa⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩

中文:
引理 isBoundedUnder_ge_toReal
  证明: by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by simpa⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩
-/
@[simp, norm_cast] lemma isBoundedUnder_ge_toReal :
    IsBoundedUnder (· >= ·) f (fun i => (u i : Real)) ↔ IsBoundedUnder (· >= ·) f u := by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by simpa⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩

/--
lemma `isCoboundedUnder_le_toReal` / 引理 `isCoboundedUnder_le_toReal`

English:
lemma isCoboundedUnder_le_toReal
  given: [f.NeBot]
  proof: by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, fun x _ => by simpa [*] using hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    exact ⟨b, fun x hx => hb _ (hx.exists.choose_spec.trans' (by

中文:
引理 isCoboundedUnder_le_toReal
  条件: [f.NeBot]
  证明: by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, fun x _ => by simpa [*] using hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    exact ⟨b, fun x hx => hb _ (hx.exists.choose_spec.trans' (by
-/
@[simp, norm_cast] lemma isCoboundedUnder_le_toReal [f.NeBot] :
    IsCoboundedUnder (· <= ·) f (fun i => (u i : Real)) ↔ IsCoboundedUnder (· <= ·) f u := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, fun x _ => by simpa [*] using hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    exact ⟨b, fun x hx => hb _ (hx.exists.choose_spec.trans' (by simp)) hx⟩

/--
lemma `isCoboundedUnder_ge_toReal` / 引理 `isCoboundedUnder_ge_toReal`

English:
lemma isCoboundedUnder_ge_toReal
  proof: by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb _ (by simp), fun x _ => hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    refine ⟨b, fun x hx => ?_⟩
    obtain hx₀ | hx₀ := le_total x 0
    · exact hx₀.t

中文:
引理 isCoboundedUnder_ge_toReal
  证明: by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb _ (by simp), fun x _ => hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    refine ⟨b, fun x hx => ?_⟩
    obtain hx₀ | hx₀ := le_total x 0
    · exact hx₀.t
-/
@[simp, norm_cast] lemma isCoboundedUnder_ge_toReal :
    IsCoboundedUnder (· >= ·) f (fun i => (u i : Real)) ↔ IsCoboundedUnder (· >= ·) f u := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb _ (by simp), fun x _ => hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    refine ⟨b, fun x hx => ?_⟩
    obtain hx₀ | hx₀ := le_total x 0
    · exact hx₀.trans hb₀
    · exact hb _ hx₀ hx

@[simp]
/--
lemma `limsSup_of_not_isBounded` / 引理 `limsSup_of_not_isBounded`

English:
lemma limsSup_of_not_isBounded
  given: {f : Filter Real>=0} (hf : ¬ f.IsBounded (· <= ·))
  statement: limsSup f = 0
  proof: by
  rw [limsSup]; rw [← bot_eq_zero]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]

中文:
引理 limsSup_of_not_isBounded
  条件: {f : Filter 实数>=0} (hf : ¬ f.IsBounded (· <= ·))
  结论: limsSup f = 0
  证明: by
  rw [limsSup]; rw [← bot_eq_zero]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]

Depends on / 依赖: IsBounded, Set.eq_empty_iff_forall_notMem, bot_eq_zero, convert, eq_empty_iff_forall_notMem, limsSup, sInf_empty
-/
lemma limsSup_of_not_isBounded {f : Filter Real>=0} (hf : ¬ f.IsBounded (· <= ·)) : limsSup f = 0 := by
  rw [limsSup]; rw [← bot_eq_zero]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
/--
lemma `limsInf_of_not_isCobounded` / 引理 `limsInf_of_not_isCobounded`

English:
lemma limsInf_of_not_isCobounded
  given: {f : Filter Real>=0} (hf : ¬ f.IsCobounded (· >= ·))
  proof: by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]

中文:
引理 limsInf_of_not_isCobounded
  条件: {f : Filter 实数>=0} (hf : ¬ f.IsCobounded (· >= ·))
  证明: by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]

Depends on / 依赖: limsInf, sSup_of_not_bddAbove
-/
lemma limsInf_of_not_isCobounded {f : Filter Real>=0} (hf : ¬ f.IsCobounded (· >= ·)) :
    limsInf f = 0 := by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]
/--
lemma `limsup_of_not_isBoundedUnder` / 引理 `limsup_of_not_isBoundedUnder`

English:
lemma limsup_of_not_isBoundedUnder
  given: (hf : ¬ f.IsBoundedUnder (· <= ·) u)
  statement: limsup u f = 0
  proof: limsSup_of_not_isBounded hf

@[simp]

中文:
引理 limsup_of_not_isBoundedUnder
  条件: (hf : ¬ f.IsBoundedUnder (· <= ·) u)
  结论: limsup u f = 0
  证明: limsSup_of_not_isBounded hf

@[simp]

Depends on / 依赖: limsSup_of_not_isBounded
-/
lemma limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· <= ·) u) : limsup u f = 0 :=
  limsSup_of_not_isBounded hf

@[simp]
/--
lemma `liminf_of_not_isCoboundedUnder` / 引理 `liminf_of_not_isCoboundedUnder`

English:
lemma liminf_of_not_isCoboundedUnder
  given: (hf : ¬ f.IsCoboundedUnder (· >= ·) u)
  statement: liminf u f = 0
  proof: limsInf_of_not_isCobounded hf

@[simp, norm_cast]

中文:
引理 liminf_of_not_isCoboundedUnder
  条件: (hf : ¬ f.IsCoboundedUnder (· >= ·) u)
  结论: liminf u f = 0
  证明: limsInf_of_not_isCobounded hf

@[simp, norm_cast]

Depends on / 依赖: limsInf_of_not_isCobounded
-/
lemma liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· >= ·) u) : liminf u f = 0 :=
  limsInf_of_not_isCobounded hf

@[simp, norm_cast]
/--
lemma `toReal_liminf` / 引理 `toReal_liminf`

English:
lemma toReal_liminf
  statement: liminf (fun i => (u i : Real)) f = liminf u f
  proof: by
  by_cases hf : f.IsCoboundedUnder (· >= ·) u; swap
  · simp [*]
  refine eq_of_forall_le_iff fun c => ?_
  rw [← Real.toNNReal_le_iff_le_coe]; rw [le_liminf_iff (by simpa) ⟨0]; rw [by simp⟩]; rw [le_liminf_iff]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_

中文:
引理 toReal_liminf
  结论: liminf (fun i => (u i : 实数)) f = liminf u f
  证明: by
  by_cases hf : f.IsCoboundedUnder (· >= ·) u; swap
  · simp [*]
  refine eq_of_forall_le_iff fun c => ?_
  rw [← Real.toNNReal_le_iff_le_coe]; rw [le_liminf_iff (by simpa) ⟨0]; rw [by simp⟩]; rw [le_liminf_iff]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_

Depends on / 依赖: IsCoboundedUnder, IsEmpty, IsEmpty.forall_iff, NNReal, NNReal.forall, Real.coe_toNNReal, Real.toNNReal_le_iff_le_coe, and_true, coe_lt_coe, coe_mk, coe_toNNReal, eq_of_forall_le_iff, f.IsCoboundedUnder, forall_comm, forall_iff, hr.trans_l, imp_right, isEmpty_Prop, le_liminf_iff, le_or_gt
-/
lemma toReal_liminf : liminf (fun i => (u i : Real)) f = liminf u f := by
  by_cases hf : f.IsCoboundedUnder (· >= ·) u; swap
  · simp [*]
  refine eq_of_forall_le_iff fun c => ?_
  rw [← Real.toNNReal_le_iff_le_coe]; rw [le_liminf_iff (by simpa) ⟨0]; rw [by simp⟩]; rw [le_liminf_iff]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_lt,
    zero_le_coe, IsEmpty.forall_iff, and_true, NNReal.forall, coe_mk, forall_comm (α := _ <= _)]
  refine forall₂_congr fun r hr => ?_
  simpa using (le_or_gt 0 r).imp_right fun hr => .of_forall fun i => hr.trans_le (by simp)

@[simp, norm_cast]
/--
lemma `toReal_limsup` / 引理 `toReal_limsup`

English:
lemma toReal_limsup
  statement: limsup (fun i => (u i : Real)) f = limsup u f
  proof: by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  by_cases hf : f.IsBoundedUnder (· <= ·) u; swap
  · simp [*]
  have : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault
  refine eq_of_forall_le_iff fun c => ?_
  rw [← Real.toNNReal_le_iff_le_coe]; rw [le_limsup_iff (by simpa) (b

中文:
引理 toReal_limsup
  结论: limsup (fun i => (u i : 实数)) f = limsup u f
  证明: by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  by_cases hf : f.IsBoundedUnder (· <= ·) u; swap
  · simp [*]
  have : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault
  refine eq_of_forall_le_iff fun c => ?_
  rw [← Real.toNNReal_le_iff_le_coe]; rw [le_limsup_iff (by simpa) (b

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, IsEmpty, IsEmpty.forall_iff, NNReal, NNReal.forall, Real.coe_toNNReal, Real.toNNReal_le_iff_le_coe, and_true, coe_lt_coe, coe_mk, coe_toNNReal, eq_of_forall_le_iff, eq_or_neBot, f.IsBoundedUnder, f.IsCoboundedUnder, f.eq_or_neBot, forall_comm, forall_iff, isBoundedDefault
-/
lemma toReal_limsup : limsup (fun i => (u i : Real)) f = limsup u f := by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  by_cases hf : f.IsBoundedUnder (· <= ·) u; swap
  · simp [*]
  have : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault
  refine eq_of_forall_le_iff fun c => ?_
  rw [← Real.toNNReal_le_iff_le_coe]; rw [le_limsup_iff (by simpa) (by simpa)]; rw [le_limsup_iff ‹_›]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_lt,
    zero_le_coe, IsEmpty.forall_iff, and_true, NNReal.forall, coe_mk, forall_comm (α := _ <= _)]
  refine forall₂_congr fun r hr => ?_
  simpa using (le_or_gt 0 r).imp_right fun hr => .of_forall fun i => hr.trans_le (by simp)

end NNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

/--
theorem `eventually_le_limsup` / 定理 `eventually_le_limsup`

English:
theorem eventually_le_limsup
  given: [CountableInterFilter f] (u : α -> Real>=0∞)
  proof: _root_.eventually_le_limsup

中文:
定理 eventually_le_limsup
  条件: [Countable整数erFilter f] (u : α -> 实数>=0∞)
  证明: _root_.eventually_le_limsup

Depends on / 依赖: _root_, _root_.eventually_le_limsup, eventually_le_limsup
-/
theorem eventually_le_limsup [CountableInterFilter f] (u : α -> Real>=0∞) :
    forallᶠ y in f, u y <= f.limsup u :=
  _root_.eventually_le_limsup

/--
theorem `limsup_eq_zero_iff` / 定理 `limsup_eq_zero_iff`

English:
theorem limsup_eq_zero_iff
  given: [CountableInterFilter f] {u : α -> Real>=0∞}
  proof: limsup_eq_bot

中文:
定理 limsup_eq_zero_iff
  条件: [Countable整数erFilter f] {u : α -> 实数>=0∞}
  证明: limsup_eq_bot

Depends on / 依赖: limsup_eq_bot
-/
theorem limsup_eq_zero_iff [CountableInterFilter f] {u : α -> Real>=0∞} :
    f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
  limsup_eq_bot

/--
theorem `limsup_const_mul_of_ne_top` / 定理 `limsup_const_mul_of_ne_top`

English:
theorem limsup_const_mul_of_ne_top
  given: {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤)
  proof: by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    exact limsup_const_bot
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x =>
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.limsup_apply.symm

中文:
定理 limsup_const_mul_of_ne_top
  条件: {u : α -> 实数>=0∞} {a : 实数>=0∞} (ha_top : a != ⊤)
  证明: by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    exact limsup_const_bot
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x =>
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.limsup_apply.symm

Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, ENNReal.mul_inv_cancel_left, ENNReal.mul_right_strictMono, bot_eq_zero, g_iso, g_iso.limsup_apply.symm, ha_top, limsup_apply, limsup_const_bot, mul_inv_cancel_left, mul_right_strictMono, orderIsoOfSurjective, simp_rw, zero_mul
-/
theorem limsup_const_mul_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) :
    (f.limsup fun x : α => a * u x) = a * f.limsup u := by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    exact limsup_const_bot
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x =>
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.limsup_apply.symm

/--
theorem `limsup_mul_const_of_ne_top` / 定理 `limsup_mul_const_of_ne_top`

English:
theorem limsup_mul_const_of_ne_top
  given: {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤)
  proof: by
  simpa [mul_comm] using limsup_const_mul_of_ne_top ha_top

中文:
定理 limsup_mul_const_of_ne_top
  条件: {u : α -> 实数>=0∞} {a : 实数>=0∞} (ha_top : a != ⊤)
  证明: by
  simpa [mul_comm] using limsup_const_mul_of_ne_top ha_top

Depends on / 依赖: ha_top, limsup_const_mul_of_ne_top, mul_comm
-/
theorem limsup_mul_const_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) :
    f.limsup (fun x : α => u x * a) = a * f.limsup u := by
  simpa [mul_comm] using limsup_const_mul_of_ne_top ha_top

/--
theorem `liminf_const_mul_of_ne_zero_of_ne_top` / 定理 `liminf_const_mul_of_ne_zero_of_ne_top`

English:
theorem liminf_const_mul_of_ne_zero_of_ne_top
  statement: {u : α -> Real>=0∞} {a : Real>=0∞}
  proof: by
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x =>
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.liminf_apply.symm

中文:
定理 liminf_const_mul_of_ne_zero_of_ne_top
  结论: {u : α -> 实数>=0∞} {a : 实数>=0∞}
  证明: by
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x =>
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.liminf_apply.symm

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel_left, ENNReal.mul_right_strictMono, g_iso, g_iso.liminf_apply.symm, ha_top, liminf_apply, mul_inv_cancel_left, mul_right_strictMono, orderIsoOfSurjective
-/
theorem liminf_const_mul_of_ne_zero_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞}
    (ha₀ : a != 0) (ha_top : a != ⊤) :
    f.liminf (fun x : α => a * u x) = a * f.liminf u := by
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x =>
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.liminf_apply.symm

/--
theorem `liminf_mul_const_of_ne_zero_of_ne_top` / 定理 `liminf_mul_const_of_ne_zero_of_ne_top`

English:
theorem liminf_mul_const_of_ne_zero_of_ne_top
  statement: {u : α -> Real>=0∞} {a : Real>=0∞}
  proof: by
  simpa [mul_comm] using liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top

中文:
定理 liminf_mul_const_of_ne_zero_of_ne_top
  结论: {u : α -> 实数>=0∞} {a : 实数>=0∞}
  证明: by
  simpa [mul_comm] using liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top

Depends on / 依赖: ha_top, liminf_const_mul_of_ne_zero_of_ne_top, mul_comm
-/
theorem liminf_mul_const_of_ne_zero_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞}
    (ha₀ : a != 0) (ha_top : a != ⊤) :
    f.liminf (fun x : α => u x * a) = a * f.liminf u := by
  simpa [mul_comm] using liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top

/--
theorem `liminf_const_mul_of_ne_top` / 定理 `liminf_const_mul_of_ne_top`

English:
theorem liminf_const_mul_of_ne_top
  given: [f.NeBot] {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤)
  proof: by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    apply liminf_const
  exact liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top

中文:
定理 liminf_const_mul_of_ne_top
  条件: [f.NeBot] {u : α -> 实数>=0∞} {a : 实数>=0∞} (ha_top : a != ⊤)
  证明: by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    apply liminf_const
  exact liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top

Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, bot_eq_zero, ha_top, liminf_const, liminf_const_mul_of_ne_zero_of_ne_top, simp_rw, zero_mul
-/
theorem liminf_const_mul_of_ne_top [f.NeBot] {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) :
    f.liminf (fun x : α => a * u x) = a * f.liminf u := by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    apply liminf_const
  exact liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top

/--
theorem `liminf_mul_const_of_ne_top` / 定理 `liminf_mul_const_of_ne_top`

English:
theorem liminf_mul_const_of_ne_top
  given: [f.NeBot] {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤)
  proof: by
  simpa [mul_comm] using liminf_const_mul_of_ne_top ha_top

中文:
定理 liminf_mul_const_of_ne_top
  条件: [f.NeBot] {u : α -> 实数>=0∞} {a : 实数>=0∞} (ha_top : a != ⊤)
  证明: by
  simpa [mul_comm] using liminf_const_mul_of_ne_top ha_top

Depends on / 依赖: ha_top, liminf_const_mul_of_ne_top, mul_comm
-/
theorem liminf_mul_const_of_ne_top [f.NeBot] {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) :
    f.liminf (fun x : α => u x * a) = a * f.liminf u := by
  simpa [mul_comm] using liminf_const_mul_of_ne_top ha_top

/--
theorem `limsup_const_mul` / 定理 `limsup_const_mul`

English:
theorem limsup_const_mul
  given: [CountableInterFilter f] {u : α -> Real>=0∞} {a : Real>=0∞}
  proof: by
  by_cases! ha_top : a != ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (a * u ·) =ᶠ[f] 0 := hu.mono fun x hx => by simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_def, ← ENNReal.bot_eq_zero,
      limsup_const_bot]
    simp
  · have hu

中文:
定理 limsup_const_mul
  条件: [Countable整数erFilter f] {u : α -> 实数>=0∞} {a : 实数>=0∞}
  证明: by
  by_cases! ha_top : a != ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (a * u ·) =ᶠ[f] 0 := hu.mono fun x hx => by simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_def, ← ENNReal.bot_eq_zero,
      limsup_const_bot]
    simp
  · have hu

Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, EventuallyEq, Pi.zero_def, bot_eq_zero, f.limsup, h_top_le, ha_top, hu.mono, hu_mul, limsup, limsup_congr, limsup_const_bot, limsup_const_mul_of_ne_top, not_eventually, zero_def
-/
theorem limsup_const_mul [CountableInterFilter f] {u : α -> Real>=0∞} {a : Real>=0∞} :
    f.limsup (a * u ·) = a * f.limsup u := by
  by_cases! ha_top : a != ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (a * u ·) =ᶠ[f] 0 := hu.mono fun x hx => by simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_def, ← ENNReal.bot_eq_zero,
      limsup_const_bot]
    simp
  · have hu_mul : existsᶠ x : α in f, ⊤ <= ite (u x = 0) (0 : Real>=0∞) ⊤ := by
      rw [EventuallyEq]; rw [not_eventually] at hu
      exact hu.mono fun x hx => by simpa
    have h_top_le : (f.limsup fun x : α => ite (u x = 0) (0 : Real>=0∞) ⊤) = ⊤ :=
      eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul)
    have hfu : f.limsup u != 0 := mt limsup_eq_bot.1 hu
    simp [ha_top, top_mul', h_top_le, hfu]

/--
theorem `limsup_mul_const` / 定理 `limsup_mul_const`

English:
theorem limsup_mul_const
  given: [CountableInterFilter f] {u : α -> Real>=0∞} {a : Real>=0∞}
  proof: by
  simpa [mul_comm] using limsup_const_mul

中文:
定理 limsup_mul_const
  条件: [Countable整数erFilter f] {u : α -> 实数>=0∞} {a : 实数>=0∞}
  证明: by
  simpa [mul_comm] using limsup_const_mul

Depends on / 依赖: limsup_const_mul, mul_comm
-/
theorem limsup_mul_const [CountableInterFilter f] {u : α -> Real>=0∞} {a : Real>=0∞} :
    f.limsup (u · * a) = a * f.limsup u := by
  simpa [mul_comm] using limsup_const_mul

/--
theorem `limsup_mul_le` / 定理 `limsup_mul_le`

English:
theorem limsup_mul_le
  given: [CountableInterFilter f] (u v : α -> Real>=0∞)
  proof: calc
    f.limsup (u * v) <= f.limsup fun x => f.limsup u * v x := by
      refine limsup_le_limsup ?_
      filter_upwards [@eventually_le_limsup _ f _ u] with x hx using mul_le_mul' hx le_rfl
    _ = f.limsup u * f.limsup v := limsup_const_mul

中文:
定理 limsup_mul_le
  条件: [Countable整数erFilter f] (u v : α -> 实数>=0∞)
  证明: calc
    f.limsup (u * v) <= f.limsup fun x => f.limsup u * v x := by
      refine limsup_le_limsup ?_
      filter_upwards [@eventually_le_limsup _ f _ u] with x hx using mul_le_mul' hx le_rfl
    _ = f.limsup u * f.limsup v := limsup_const_mul

Depends on / 依赖: eventually_le_limsup, f.limsup, filter_upwards, le_rfl, limsup, limsup_const_mul, limsup_le_limsup, mul_le_mul
-/
theorem limsup_mul_le [CountableInterFilter f] (u v : α -> Real>=0∞) :
    f.limsup (u * v) <= f.limsup u * f.limsup v :=
  calc
    f.limsup (u * v) <= f.limsup fun x => f.limsup u * v x := by
      refine limsup_le_limsup ?_
      filter_upwards [@eventually_le_limsup _ f _ u] with x hx using mul_le_mul' hx le_rfl
    _ = f.limsup u * f.limsup v := limsup_const_mul

/--
theorem `limsup_add_le` / 定理 `limsup_add_le`

English:
theorem limsup_add_le
  given: [CountableInterFilter f] (u v : α -> Real>=0∞)
  proof: sInf_le ((eventually_le_limsup u).mp
    ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))

中文:
定理 limsup_add_le
  条件: [Countable整数erFilter f] (u v : α -> 实数>=0∞)
  证明: sInf_le ((eventually_le_limsup u).mp
    ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))

Depends on / 依赖: add_le_add, eventually_le_limsup, sInf_le
-/
theorem limsup_add_le [CountableInterFilter f] (u v : α -> Real>=0∞) :
    f.limsup (u + v) <= f.limsup u + f.limsup v :=
  sInf_le ((eventually_le_limsup u).mp
    ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))

/--
theorem `limsup_liminf_le_liminf_limsup` / 定理 `limsup_liminf_le_liminf_limsup`

English:
theorem limsup_liminf_le_liminf_limsup
  statement: {β} [Countable β] {f : Filter α} [CountableInterFilter f]
  proof: have h1 : forallᶠ a in f, forall b, u a b <= f.limsup fun a' => u a' b := by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
sInf_le h1.mono fun x hx => Filter.liminf_le_liminf (Filter.Eventually.of_forall hx)

中文:
定理 limsup_liminf_le_liminf_limsup
  结论: {β} [Countable β] {f : Filter α} [Countable整数erFilter f]
  证明: have h1 : forallᶠ a in f, forall b, u a b <= f.limsup fun a' => u a' b := by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
sInf_le h1.mono fun x hx => Filter.liminf_le_liminf (Filter.Eventually.of_forall hx)

Depends on / 依赖: ENNReal, ENNReal.eventually_le_limsup, Eventually, Filter, Filter.Eventually.of_forall, Filter.liminf_le_liminf, eventually_countable_forall, eventually_le_limsup, f.limsup, h1.mono, liminf_le_liminf, limsup, of_forall, sInf_le
-/
theorem limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [CountableInterFilter f]
    {g : Filter β} (u : α -> β -> Real>=0∞) :
    (f.limsup fun a : α => g.liminf fun b : β => u a b) <=
      g.liminf fun b => f.limsup fun a => u a b :=
  have h1 : forallᶠ a in f, forall b, u a b <= f.limsup fun a' => u a' b := by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
sInf_le h1.mono fun x hx => Filter.liminf_le_liminf (Filter.Eventually.of_forall hx)

/--
lemma `ofReal_limsup` / 引理 `ofReal_limsup`

English:
lemma ofReal_limsup
  statement: {u : α -> Real}
  proof: by
  refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
  simp only [ofReal_le_coe]
  rw [limsup_le_iff]; rw [limsup_le_iff]
  constructor
  · rintro h (_ | x) hx
    · simp
    filter_upwards [h x (by simpa using hx)] with a ha
    obtain ha₀ | ha₀ := le_total (u a) 0
    · simpa [ofReal_of_nonp

中文:
引理 ofReal_limsup
  结论: {u : α -> 实数}
  证明: by
  refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
  simp only [ofReal_le_coe]
  rw [limsup_le_iff]; rw [limsup_le_iff]
  constructor
  · rintro h (_ | x) hx
    · simp
    filter_upwards [h x (by simpa using hx)] with a ha
    obtain ha₀ | ha₀ := le_total (u a) 0
    · simpa [ofReal_of_nonp

Depends on / 依赖: ENNReal, ENNReal.eq_of_forall_le_nnreal_iff, ENNReal.ofReal, IsBoundedUnder, bot_lt, eq_of_forall_le_nnreal_iff, filter_upwards, hx.bot_lt, isBoundedDefault, le_total, limsup, limsup_le_iff, ofReal, ofReal_le_coe, ofReal_lt_coe_iff, ofReal_of_nonpos
-/
lemma ofReal_limsup {u : α -> Real}
    (h₁ : IsCoboundedUnder (· <= ·) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    ENNReal.ofReal (limsup u f) = limsup (fun a => .ofReal (u a)) f := by
  refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
  simp only [ofReal_le_coe]
  rw [limsup_le_iff]; rw [limsup_le_iff]
  constructor
  · rintro h (_ | x) hx
    · simp
    filter_upwards [h x (by simpa using hx)] with a ha
    obtain ha₀ | ha₀ := le_total (u a) 0
    · simpa [ofReal_of_nonpos, *] using hx.bot_lt
    · simp [ofReal_lt_coe_iff, *]
  · rintro h x hx
    have : 0 < x := hx.trans_le' (by simp)
    filter_upwards [h (.ofReal x) (by simpa [this] using hx)] with a ha
    exact (toReal_lt_of_lt_ofReal ha).trans_le' (by simp [toReal_ofReal'])

/--
lemma `ofReal_limsup_toReal` / 引理 `ofReal_limsup_toReal`

English:
lemma ofReal_limsup_toReal
  given: [f.NeBot] {u : α -> Real>=0∞} {C : Real>=0} (hf : forallᶠ a in f, u a <= C)
  proof: by
  have h₁ : IsCoboundedUnder (· <= ·) f (fun a => (u a).toReal) :=
IsCoboundedUnder.of_frequently_ge .of_forall fun _ => by positivity
  have h₂ : IsBoundedUnder (· <= ·) f (fun a => (u a).toReal) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hf] with a ha
    e

中文:
引理 ofReal_limsup_toReal
  条件: [f.NeBot] {u : α -> 实数>=0∞} {C : 实数>=0} (hf : 对任意ᶠ a in f, u a <= C)
  证明: by
  have h₁ : IsCoboundedUnder (· <= ·) f (fun a => (u a).toReal) :=
IsCoboundedUnder.of_frequently_ge .of_forall fun _ => by positivity
  have h₂ : IsBoundedUnder (· <= ·) f (fun a => (u a).toReal) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hf] with a ha
    e

Depends on / 依赖: ENNReal, ENNReal.ofReal_limsup, ENNReal.ofReal_toReal, ENNReal.toReal_le_coe_of_le_coe, IsBoundedUnder, IsCoboundedUnder, IsCoboundedUnder.of_frequently_ge, filter_upwards, isBoundedUnder_of_eventually_le, limsup_congr, ne_top_of_le_ne_top, ofReal_limsup, ofReal_toReal, of_forall, of_frequently_ge, toReal, toReal_le_coe_of_le_coe
-/
lemma ofReal_limsup_toReal [f.NeBot] {u : α -> Real>=0∞} {C : Real>=0} (hf : forallᶠ a in f, u a <= C) :
    ENNReal.ofReal (limsup (fun a => (u a).toReal) f) = limsup u f := by
  have h₁ : IsCoboundedUnder (· <= ·) f (fun a => (u a).toReal) :=
IsCoboundedUnder.of_frequently_ge .of_forall fun _ => by positivity
  have h₂ : IsBoundedUnder (· <= ·) f (fun a => (u a).toReal) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hf] with a ha
    exact ENNReal.toReal_le_coe_of_le_coe ha
  refine (ENNReal.ofReal_limsup h₁ h₂).trans (limsup_congr ?_)
  filter_upwards [hf] with x hx
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp : C != ∞) hx)

/--
lemma `toReal_limsup` / 引理 `toReal_limsup`

English:
lemma toReal_limsup
  statement: {u : α -> Real>=0∞} (h₁ : forallᶠ a in f, u a != ∞)
  proof: by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  have : IsCoboundedUnder (· <= ·) f fun a => (u a).toReal := .of_frequently_ge (a := 0) (by simpa)
  refine eq_of_forall_ge_iff fun r => ?_
  obtain hr | hr := lt_or_ge r 0
  · exact iff_of_false (hr.trans_le toReal_nonneg).not_ge
   

中文:
引理 toReal_limsup
  结论: {u : α -> 实数>=0∞} (h₁ : 对任意ᶠ a in f, u a != ∞)
  证明: by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  have : IsCoboundedUnder (· <= ·) f fun a => (u a).toReal := .of_frequently_ge (a := 0) (by simpa)
  refine eq_of_forall_ge_iff fun r => ?_
  obtain hr | hr := lt_or_ge r 0
  · exact iff_of_false (hr.trans_le toReal_nonneg).not_ge
   

Depends on / 依赖: IsCoboundedUnder, eq_of_forall_ge_iff, eq_or_neBot, f.eq_or_neBot, hr.trans_le, iff_of_false, isBoundedDefault, le_limsup_of_frequently_le, le_ofReal_iff_toReal_le, limsSup, limsup, limsup_le_i, limsup_le_iff, lt_or_ge, not_ge, of_frequently_ge, toReal, toReal_nonneg, trans_le
-/
lemma toReal_limsup {u : α -> Real>=0∞} (h₁ : forallᶠ a in f, u a != ∞)
    (h₂ : IsBoundedUnder (· <= ·) f fun a => (u a).toReal := by isBoundedDefault) :
    (limsup u f).toReal = limsup (fun a => (u a).toReal) f := by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  have : IsCoboundedUnder (· <= ·) f fun a => (u a).toReal := .of_frequently_ge (a := 0) (by simpa)
  refine eq_of_forall_ge_iff fun r => ?_
  obtain hr | hr := lt_or_ge r 0
  · exact iff_of_false (hr.trans_le toReal_nonneg).not_ge
      (hr.trans_le <| le_limsup_of_frequently_le (by simpa)).not_ge
  rw [← le_ofReal_iff_toReal_le _ hr]; rw [limsup_le_iff]; rw [limsup_le_iff]
  constructor
  · rintro h x hx
    have : 0 < x := hx.trans_le' hr
    filter_upwards [h (.ofReal x) (by simpa [this] using hx)] with i hi
    exact toReal_lt_of_lt_ofReal hi
  · rintro h (_ | x) hx
    · simpa [lt_top_iff_ne_top]
    filter_upwards [h₁, h x (by simpa [ofReal_lt_coe_iff hr] using hx)] with i hi
    simp [← lt_ofReal_iff_toReal_lt hi]
  obtain ⟨x, hx⟩ := h₂
  rw [eventually_map] at hx
  have hx₀ : 0 <= x := by obtain ⟨i, hi⟩ := hx.exists; exact toReal_nonneg.trans hi
  simp only [limsup, limsSup, eventually_map, ne_eq, sInf_eq_top, Set.mem_ofPred_eq, not_forall]
  refine ⟨.ofReal x, ?_, by simp⟩
  filter_upwards [h₁, hx] with i hi
  simp [le_ofReal_iff_toReal_le, *]

end ENNReal
