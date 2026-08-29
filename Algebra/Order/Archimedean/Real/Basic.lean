/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Disjoint

import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Data.Int.LeastGreatest

/-!
# The real numbers are an Archimedean floor ring, and a conditionally complete linear order.

-/

@[expose] public section

assert_not_exists Finset

open scoped Pointwise
open CauSeq

namespace Real
variable {ι : Sort*} {f : ι -> Real} {s : Set Real} {a : Real}

/--
Instance `instArchimedean` / 实例 `instArchimedean`

English:
instance instArchimedean
  signature: : Archimedean Real
  body: archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 le_of_lt (abs_lt.1 (H i)).2⟩⟩

中文:
实例 instArchimedean
  签名: : Archimedean 实数
  定义体: archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 le_of_lt (abs_lt.1 (H i)).2⟩⟩

Depends on / 依赖: Rat.cast_le, Real.ind_mk, abs_lt, archimedean_iff_rat_le, bounded, cast_le, f.bounded, ind_mk, le_of_lt, mk_le_of_forall_le
-/
instance instArchimedean : Archimedean Real :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 le_of_lt (abs_lt.1 (H i)).2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorRing Real
  body: Archimedean.floorRing _

中文:
实例 :
  签名: FloorRing 实数
  定义体: Archimedean.floorRing _

Depends on / 依赖: Archimedean, Archimedean.floorRing, floorRing
-/
noncomputable instance : FloorRing Real :=
  Archimedean.floorRing _

/--
theorem `isCauSeq_iff_lift` / 定理 `isCauSeq_iff_lift`

English:
theorem isCauSeq_iff_lift
  given: {f : Nat -> Rat}
  statement: IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : Real) where
  proof: let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij

中文:
定理 isCauSeq_iff_lift
  条件: {f : 自然数 -> Rat}
  结论: IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : 实数) where
  证明: let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij

Depends on / 依赖: Rat.cast_pos, cast_pos, exists_pos_rat_lt, lt_trans, mod_cast
-/
theorem isCauSeq_iff_lift {f : Nat -> Rat} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : Real) where
  mp H ε ε0 :=
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij

/--
theorem `of_near` / 定理 `of_near`

English:
theorem of_near
  given: (f : Nat -> Rat) (x : Real) (h : forall ε > 0, exists i, forall j >= i, |(f j : Real) - x| < ε)
  proof: ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
sub_eq_zero.1
abs_eq_zero.1
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
mk_near_of_forall_near (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩

@[deprecated _root_.exists_floor (since := "2026-01-29")]

中文:
定理 of_near
  条件: (f : 自然数 -> Rat) (x : 实数) (h : 对任意 ε > 0, 存在 i, 对任意 j >= i, |(f j : 实数) - x| < ε)
  证明: ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
sub_eq_zero.1
abs_eq_zero.1
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
mk_near_of_forall_near (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩

@[deprecated _root_.exists_floor (since := "2026-01-29")]

Depends on / 依赖: CauSeq, CauSeq.of_near, abs_eq_zero, abs_nonneg, eq_of_le_of_forall_lt_imp_le_of_dense, isCauSeq_iff_lift, le_of_lt, mk_near_of_forall_near, of_near, sub_eq_zero
-/
theorem of_near (f : Nat -> Rat) (x : Real) (h : forall ε > 0, exists i, forall j >= i, |(f j : Real) - x| < ε) :
    exists h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
sub_eq_zero.1
abs_eq_zero.1
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
mk_near_of_forall_near (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩

@[deprecated _root_.exists_floor (since := "2026-01-29")]
/--
theorem `exists_floor` / 定理 `exists_floor`

English:
theorem exists_floor
  given: (x : Real)
  statement: exists ub : Int, (ub : Real) <= x ∧ forall z : Int, (z : Real) <= x -> z <= ub
  proof: ⟨⌊x⌋, Int.floor_le x, fun _ => Int.le_floor.mpr⟩

中文:
定理 exists_floor
  条件: (x : 实数)
  结论: 存在 ub : 整数, (ub : 实数) <= x ∧ 对任意 z : 整数, (z : 实数) <= x -> z <= ub
  证明: ⟨⌊x⌋, Int.floor_le x, fun _ => Int.le_floor.mpr⟩

Depends on / 依赖: Int.floor_le, Int.le_floor.mpr, floor_le, le_floor
-/
theorem exists_floor (x : Real) : exists ub : Int, (ub : Real) <= x ∧ forall z : Int, (z : Real) <= x -> z <= ub :=
  ⟨⌊x⌋, Int.floor_le x, fun _ => Int.le_floor.mpr⟩

/--
theorem `exists_isLUB` / 定理 `exists_isLUB`

English:
theorem exists_isLUB
  given: (hne : s.Nonempty) (hbdd : BddAbove s)
  statement: exists x, IsLUB s x
  proof: by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : forall d : Nat, BddAbove { m : Int | exists y in s, (m : Real) <= y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
 

中文:
定理 exists_isLUB
  条件: (hne : s.Nonempty) (hbdd : BddAbove s)
  结论: 存在 x, IsLUB s x
  证明: by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : forall d : Nat, BddAbove { m : Int | exists y in s, (m : Real) <= y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
 

Depends on / 依赖: BddAbove, Int.cast_le, Int.exists_greatest_of_bdd, Int.floor_le, cast_le, exists_greatest_of_bdd, exists_int_gt, floor_le, hk.le, hy.trans
-/
theorem exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) : exists x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : forall d : Nat, BddAbove { m : Int | exists y in s, (m : Real) <= y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    gcongr
    exact (hU yS).trans hk.le
  choose f hf using fun d : Nat =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : forall n > 0, exists y in s, ((f n / n : Rat) : Real) <= y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff₀ (Nat.cast_pos.2 n0 : (_ : Real) < _)).2 hy⟩
  have hf₂ : forall n > 0, forall y in s, (y - ((n : Nat) : Real)⁻¹) < (f n / n : Rat) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, gt_iff_lt]
    rwa [lt_div_iff₀ (Nat.cast_pos.2 n0 : (_ : Real) < _), sub_mul, inv_mul_cancel₀]
    exact (Nat.cast_pos.2 n0).ne'
  have hg : IsCauSeq abs (fun n => f n / n : Nat -> Rat) := by
    intro ε ε0
    suffices forall j >= ⌈ε⁻¹⌉₊, forall k >= ⌈ε⁻¹⌉₊, (f j / j - f k / k : Rat) < ε by
      refine ⟨_, fun j ij => abs_lt.2 ⟨?_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt]; rw [neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine lt_of_lt_of_le ((Rat.cast_lt (K := Real)).1 ?_) ((inv_le_comm₀ ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq Rat abs := ⟨fun n => f n / n, hg⟩
  refine ⟨mk g, ⟨fun x xS => ?_, fun y h => ?_⟩⟩
  · refine le_of_forall_lt_imp_le_of_dense fun z xz => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (x - z)⁻¹
    refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine le_trans ?_ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le_comm₀ (Nat.cast_pos.2 n0 : (_ : Real) < _) xz]
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩

/--
theorem `exists_isGLB` / 定理 `exists_isGLB`

English:
theorem exists_isGLB
  given: (hne : s.Nonempty) (hbdd : BddBelow s)
  statement: exists x, IsGLB s x
  proof: by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

中文:
定理 exists_isGLB
  条件: (hne : s.Nonempty) (hbdd : BddBelow s)
  结论: 存在 x, IsGLB s x
  证明: by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

Depends on / 依赖: BddAbove, Classical, Classical.choose, Classical.choose_spec, Nonempty, Real.exists_isLUB, Set.nonempty_neg.mpr, bddAbove_neg, bddAbove_neg.mpr, choose_spec, exists_isLUB, isLUB_neg, nonempty_neg
-/
theorem exists_isGLB (hne : s.Nonempty) (hbdd : BddBelow s) : exists x, IsGLB s x := by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet Real
  body: ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

中文:
实例 :
  签名: SupSet 实数
  定义体: ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

Depends on / 依赖: BddAbove, Classical, Classical.choose, Nonempty, exists_isLUB, s.Nonempty
-/
noncomputable instance : SupSet Real :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

open scoped Classical in
/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: (s : Set Real)
  proof: rfl

中文:
定理 sSup_def
  条件: (s : Set 实数)
  证明: rfl
-/
theorem sSup_def (s : Set Real) :
    sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl

/--
theorem `isLUB_sSup` / 定理 `isLUB_sSup`

English:
theorem isLUB_sSup
  given: (h₁ : s.Nonempty) (h₂ : BddAbove s)
  statement: IsLUB s (sSup s)
  proof: by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec

中文:
定理 isLUB_sSup
  条件: (h₁ : s.Nonempty) (h₂ : BddAbove s)
  结论: IsLUB s (sSup s)
  证明: by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec
-/
protected theorem isLUB_sSup (h₁ : s.Nonempty) (h₂ : BddAbove s) : IsLUB s (sSup s) := by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet Real
  body: ⟨fun s => -sSup (-s)⟩

中文:
实例 :
  签名: InfSet 实数
  定义体: ⟨fun s => -sSup (-s)⟩
-/
noncomputable instance : InfSet Real :=
  ⟨fun s => -sSup (-s)⟩

/--
theorem `sInf_def` / 定理 `sInf_def`

English:
theorem sInf_def
  given: (s : Set Real)
  statement: sInf s = -sSup (-s)
  proof: rfl

中文:
定理 sInf_def
  条件: (s : Set 实数)
  结论: sInf s = -sSup (-s)
  证明: rfl
-/
theorem sInf_def (s : Set Real) : sInf s = -sSup (-s) := rfl

/--
theorem `isGLB_sInf` / 定理 `isGLB_sInf`

English:
theorem isGLB_sInf
  given: (h₁ : s.Nonempty) (h₂ : BddBelow s)
  statement: IsGLB s (sInf s)
  proof: by
  rw [sInf_def]; rw [← isLUB_neg']; rw [neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg

中文:
定理 isGLB_sInf
  条件: (h₁ : s.Nonempty) (h₂ : BddBelow s)
  结论: IsGLB s (sInf s)
  证明: by
  rw [sInf_def]; rw [← isLUB_neg']; rw [neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg
-/
protected theorem isGLB_sInf (h₁ : s.Nonempty) (h₂ : BddBelow s) : IsGLB s (sInf s) := by
  rw [sInf_def]; rw [← isLUB_neg']; rw [neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConditionallyCompleteLinearOrder Real
  body: Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]

中文:
实例 :
  签名: ConditionallyCompleteLinearOrder 实数
  定义体: Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]

Depends on / 依赖: Real.linearOrder, linearOrder
-/
noncomputable instance : ConditionallyCompleteLinearOrder Real where
  __ := Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]

/--
theorem `lt_sInf_add_pos` / 定理 `lt_sInf_add_pos`

English:
theorem lt_sInf_add_pos
  given: (h : s.Nonempty) {ε : Real} (hε : 0 < ε)
  statement: exists a in s, a < sInf s + ε
  proof: exists_lt_of_csInf_lt h lt_add_of_pos_right _ hε

中文:
定理 lt_sInf_add_pos
  条件: (h : s.Nonempty) {ε : 实数} (hε : 0 < ε)
  结论: 存在 a in s, a < sInf s + ε
  证明: exists_lt_of_csInf_lt h lt_add_of_pos_right _ hε

Depends on / 依赖: exists_lt_of_csInf_lt, lt_add_of_pos_right
-/
theorem lt_sInf_add_pos (h : s.Nonempty) {ε : Real} (hε : 0 < ε) : exists a in s, a < sInf s + ε :=
exists_lt_of_csInf_lt h lt_add_of_pos_right _ hε

/--
theorem `add_neg_lt_sSup` / 定理 `add_neg_lt_sSup`

English:
theorem add_neg_lt_sSup
  given: (h : s.Nonempty) {ε : Real} (hε : ε < 0)
  statement: exists a in s, sSup s + ε < a
  proof: exists_lt_of_lt_csSup h add_lt_iff_neg_left.2 hε

中文:
定理 add_neg_lt_sSup
  条件: (h : s.Nonempty) {ε : 实数} (hε : ε < 0)
  结论: 存在 a in s, sSup s + ε < a
  证明: exists_lt_of_lt_csSup h add_lt_iff_neg_left.2 hε

Depends on / 依赖: add_lt_iff_neg_left, exists_lt_of_lt_csSup
-/
theorem add_neg_lt_sSup (h : s.Nonempty) {ε : Real} (hε : ε < 0) : exists a in s, sSup s + ε < a :=
exists_lt_of_lt_csSup h add_lt_iff_neg_left.2 hε

/--
theorem `sInf_le_iff` / 定理 `sInf_le_iff`

English:
theorem sInf_le_iff
  given: (h : BddBelow s) (h' : s.Nonempty)
  proof: by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx

中文:
定理 sInf_le_iff
  条件: (h : BddBelow s) (h' : s.Nonempty)
  证明: by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx

Depends on / 依赖: csInf_lt_of_lt, exists_lt_of_csInf_lt, le_iff_forall_pos_lt_add, x_in
-/
theorem sInf_le_iff (h : BddBelow s) (h' : s.Nonempty) :
    sInf s <= a ↔ forall ε, 0 < ε -> exists x in s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx

/--
theorem `le_sSup_iff` / 定理 `le_sSup_iff`

English:
theorem le_sSup_iff
  given: (h : BddAbove s) (h' : s.Nonempty)
  proof: by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in hx)

@[simp]

中文:
定理 le_sSup_iff
  条件: (h : BddAbove s) (h' : s.Nonempty)
  证明: by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in hx)

@[simp]

Depends on / 依赖: exists_lt_of_lt_csSup, le_iff_forall_pos_lt_add, lt_csSup_of_lt, lt_sub_iff_add_lt, lt_sub_iff_add_lt.mp, neg_lt_zero, neg_lt_zero.mpr, neg_pos, neg_pos.mpr, sub_lt_iff_lt_add, sub_lt_iff_lt_add.mp, x_in
-/
theorem le_sSup_iff (h : BddAbove s) (h' : s.Nonempty) :
    a <= sSup s ↔ forall ε, ε < 0 -> exists x in s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in hx)

@[simp]
/--
theorem `sSup_empty` / 定理 `sSup_empty`

English:
theorem sSup_empty
  statement: sSup (∅ : Set Real) = 0
  proof: dif_neg by simp

中文:
定理 sSup_empty
  结论: sSup (∅ : Set 实数) = 0
  证明: dif_neg by simp

Depends on / 依赖: dif_neg
-/
theorem sSup_empty : sSup (∅ : Set Real) = 0 :=
dif_neg by simp

/--
theorem `sInf_univ` / 定理 `sInf_univ`

English:
theorem sInf_univ
  statement: sInf (@Set.univ Real) = 0
  proof: by
  simp [sInf_def]

中文:
定理 sInf_univ
  结论: sInf (@Set.univ 实数) = 0
  证明: by
  simp [sInf_def]

Depends on / 依赖: sInf_def
-/
theorem sInf_univ : sInf (@Set.univ Real) = 0 := by
  simp [sInf_def]

/--
lemma `iSup_of_isEmpty` / 引理 `iSup_of_isEmpty`

English:
lemma iSup_of_isEmpty
  given: [IsEmpty ι] (f : ι -> Real)
  statement: ⨆ i, f i = 0
  proof: by
  dsimp [iSup]
  convert! Real.sSup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance

@[simp]

中文:
引理 iSup_of_isEmpty
  条件: [IsEmpty ι] (f : ι -> 实数)
  结论: ⨆ i, f i = 0
  证明: by
  dsimp [iSup]
  convert! Real.sSup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance

@[simp]
-/
@[simp] lemma iSup_of_isEmpty [IsEmpty ι] (f : ι -> Real) : ⨆ i, f i = 0 := by
  dsimp [iSup]
  convert! Real.sSup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance

@[simp]
/--
theorem `iSup_const_zero` / 定理 `iSup_const_zero`

English:
theorem iSup_const_zero
  statement: ⨆ _ : ι, (0 : Real) = 0
  proof: by
  cases isEmpty_or_nonempty ι
  · exact Real.iSup_of_isEmpty _
  · exact ciSup_const

中文:
定理 iSup_const_zero
  结论: ⨆ _ : ι, (0 : 实数) = 0
  证明: by
  cases isEmpty_or_nonempty ι
  · exact Real.iSup_of_isEmpty _
  · exact ciSup_const

Depends on / 依赖: Real.iSup_of_isEmpty, ciSup_const, iSup_of_isEmpty, isEmpty_or_nonempty
-/
theorem iSup_const_zero : ⨆ _ : ι, (0 : Real) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact Real.iSup_of_isEmpty _
  · exact ciSup_const

/--
lemma `sSup_of_not_bddAbove` / 引理 `sSup_of_not_bddAbove`

English:
lemma sSup_of_not_bddAbove
  given: (hs : ¬BddAbove s)
  statement: sSup s = 0
  proof: dif_neg fun h => hs h.2

中文:
引理 sSup_of_not_bddAbove
  条件: (hs : ¬BddAbove s)
  结论: sSup s = 0
  证明: dif_neg fun h => hs h.2

Depends on / 依赖: dif_neg
-/
lemma sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = 0 := dif_neg fun h => hs h.2
/--
lemma `iSup_of_not_bddAbove` / 引理 `iSup_of_not_bddAbove`

English:
lemma iSup_of_not_bddAbove
  given: (hf : ¬BddAbove (Set.range f))
  statement: ⨆ i, f i = 0
  proof: sSup_of_not_bddAbove hf

中文:
引理 iSup_of_not_bddAbove
  条件: (hf : ¬BddAbove (Set.range f))
  结论: ⨆ i, f i = 0
  证明: sSup_of_not_bddAbove hf

Depends on / 依赖: sSup_of_not_bddAbove
-/
lemma iSup_of_not_bddAbove (hf : ¬BddAbove (Set.range f)) : ⨆ i, f i = 0 := sSup_of_not_bddAbove hf

/--
theorem `sSup_univ` / 定理 `sSup_univ`

English:
theorem sSup_univ
  statement: sSup (@Set.univ Real) = 0
  proof: Real.sSup_of_not_bddAbove not_bddAbove_univ

@[simp]

中文:
定理 sSup_univ
  结论: sSup (@Set.univ 实数) = 0
  证明: Real.sSup_of_not_bddAbove not_bddAbove_univ

@[simp]

Depends on / 依赖: Real.sSup_of_not_bddAbove, not_bddAbove_univ, sSup_of_not_bddAbove
-/
theorem sSup_univ : sSup (@Set.univ Real) = 0 := Real.sSup_of_not_bddAbove not_bddAbove_univ

@[simp]
/--
theorem `sInf_empty` / 定理 `sInf_empty`

English:
theorem sInf_empty
  statement: sInf (∅ : Set Real) = 0
  proof: by simp [sInf_def, sSup_empty]

@[simp] nonrec lemma iInf_of_isEmpty [IsEmpty ι] (f : ι -> Real) : ⨅ i, f i = 0 := by
  rw [iInf_of_isEmpty]; rw [sInf_empty]

@[simp]

中文:
定理 sInf_empty
  结论: sInf (∅ : Set 实数) = 0
  证明: by simp [sInf_def, sSup_empty]

@[simp] nonrec lemma iInf_of_isEmpty [IsEmpty ι] (f : ι -> Real) : ⨅ i, f i = 0 := by
  rw [iInf_of_isEmpty]; rw [sInf_empty]

@[simp]

Depends on / 依赖: sInf_def, sSup_empty
-/
theorem sInf_empty : sInf (∅ : Set Real) = 0 := by simp [sInf_def, sSup_empty]

@[simp] nonrec lemma iInf_of_isEmpty [IsEmpty ι] (f : ι -> Real) : ⨅ i, f i = 0 := by
  rw [iInf_of_isEmpty]; rw [sInf_empty]

@[simp]
/--
theorem `iInf_const_zero` / 定理 `iInf_const_zero`

English:
theorem iInf_const_zero
  statement: ⨅ _ : ι, (0 : Real) = 0
  proof: by
  cases isEmpty_or_nonempty ι
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const

中文:
定理 iInf_const_zero
  结论: ⨅ _ : ι, (0 : 实数) = 0
  证明: by
  cases isEmpty_or_nonempty ι
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const

Depends on / 依赖: Real.iInf_of_isEmpty, ciInf_const, iInf_of_isEmpty, isEmpty_or_nonempty
-/
theorem iInf_const_zero : ⨅ _ : ι, (0 : Real) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const

/--
theorem `sInf_of_not_bddBelow` / 定理 `sInf_of_not_bddBelow`

English:
theorem sInf_of_not_bddBelow
  given: (hs : ¬BddBelow s)
  statement: sInf s = 0
  proof: neg_eq_zero.2 sSup_of_not_bddAbove mt bddAbove_neg.1 hs

中文:
定理 sInf_of_not_bddBelow
  条件: (hs : ¬BddBelow s)
  结论: sInf s = 0
  证明: neg_eq_zero.2 sSup_of_not_bddAbove mt bddAbove_neg.1 hs

Depends on / 依赖: bddAbove_neg, neg_eq_zero, sSup_of_not_bddAbove
-/
theorem sInf_of_not_bddBelow (hs : ¬BddBelow s) : sInf s = 0 :=
neg_eq_zero.2 sSup_of_not_bddAbove mt bddAbove_neg.1 hs

/--
theorem `iInf_of_not_bddBelow` / 定理 `iInf_of_not_bddBelow`

English:
theorem iInf_of_not_bddBelow
  given: (hf : ¬BddBelow (Set.range f))
  statement: ⨅ i, f i = 0
  proof: sInf_of_not_bddBelow hf

@[simp]

中文:
定理 iInf_of_not_bddBelow
  条件: (hf : ¬BddBelow (Set.range f))
  结论: ⨅ i, f i = 0
  证明: sInf_of_not_bddBelow hf

@[simp]

Depends on / 依赖: sInf_of_not_bddBelow
-/
theorem iInf_of_not_bddBelow (hf : ¬BddBelow (Set.range f)) : ⨅ i, f i = 0 :=
  sInf_of_not_bddBelow hf

@[simp]
/--
theorem `sSup_neg` / 定理 `sSup_neg`

English:
theorem sSup_neg
  given: (s : Set Real)
  statement: sSup (-s) = -sInf s
  proof: by
  obtain rfl | hn := s.eq_empty_or_nonempty; · simp
  by_cases hb : BddBelow s
  · rw [csSup_neg hn hb]
  · rw [csInf_of_not_bddBelow hb, Real.sInf_empty, csSup_of_not_bddAbove (bddAbove_neg.not.2 hb),
      Real.sSup_empty, neg_zero]

@[simp]

中文:
定理 sSup_neg
  条件: (s : Set 实数)
  结论: sSup (-s) = -sInf s
  证明: by
  obtain rfl | hn := s.eq_empty_or_nonempty; · simp
  by_cases hb : BddBelow s
  · rw [csSup_neg hn hb]
  · rw [csInf_of_not_bddBelow hb, Real.sInf_empty, csSup_of_not_bddAbove (bddAbove_neg.not.2 hb),
      Real.sSup_empty, neg_zero]

@[simp]

Depends on / 依赖: BddBelow, Real.sInf_empty, Real.sSup_empty, bddAbove_neg, bddAbove_neg.not, csInf_of_not_bddBelow, csSup_neg, csSup_of_not_bddAbove, eq_empty_or_nonempty, neg_zero, s.eq_empty_or_nonempty, sInf_empty, sSup_empty
-/
theorem sSup_neg (s : Set Real) : sSup (-s) = -sInf s := by
  obtain rfl | hn := s.eq_empty_or_nonempty; · simp
  by_cases hb : BddBelow s
  · rw [csSup_neg hn hb]
  · rw [csInf_of_not_bddBelow hb, Real.sInf_empty, csSup_of_not_bddAbove (bddAbove_neg.not.2 hb),
      Real.sSup_empty, neg_zero]

@[simp]
/--
theorem `sInf_neg` / 定理 `sInf_neg`

English:
theorem sInf_neg
  given: (s : Set Real)
  statement: sInf (-s) = -sSup s
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← Real.sSup_neg]; rw [neg_neg]

中文:
定理 sInf_neg
  条件: (s : Set 实数)
  结论: sInf (-s) = -sSup s
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← Real.sSup_neg]; rw [neg_neg]

Depends on / 依赖: Real.sSup_neg, neg_eq_iff_eq_neg, neg_neg, sSup_neg
-/
theorem sInf_neg (s : Set Real) : sInf (-s) = -sSup s := by
  rw [← neg_eq_iff_eq_neg]; rw [← Real.sSup_neg]; rw [neg_neg]

/--
lemma `sSup_le` / 引理 `sSup_le`

English:
lemma sSup_le
  given: (hs : forall x in s, x <= a) (ha : 0 <= a)
  statement: sSup s <= a
  proof: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [sSup_empty.trans_le ha, csSup_le hs' hs]

中文:
引理 sSup_le
  条件: (hs : 对任意 x in s, x <= a) (ha : 0 <= a)
  结论: sSup s <= a
  证明: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [sSup_empty.trans_le ha, csSup_le hs' hs]
-/
protected lemma sSup_le (hs : forall x in s, x <= a) (ha : 0 <= a) : sSup s <= a := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [sSup_empty.trans_le ha, csSup_le hs' hs]

/--
lemma `iSup_le` / 引理 `iSup_le`

English:
lemma iSup_le
  given: (hf : forall i, f i <= a) (ha : 0 <= a)
  statement: ⨆ i, f i <= a
  proof: Real.sSup_le (Set.forall_mem_range.2 hf) ha

中文:
引理 iSup_le
  条件: (hf : 对任意 i, f i <= a) (ha : 0 <= a)
  结论: ⨆ i, f i <= a
  证明: Real.sSup_le (Set.forall_mem_range.2 hf) ha
-/
protected lemma iSup_le (hf : forall i, f i <= a) (ha : 0 <= a) : ⨆ i, f i <= a :=
  Real.sSup_le (Set.forall_mem_range.2 hf) ha

/--
lemma `le_sInf` / 引理 `le_sInf`

English:
lemma le_sInf
  given: (hs : forall x in s, a <= x) (ha : a <= 0)
  statement: a <= sInf s
  proof: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [ha.trans_eq sInf_empty.symm, le_csInf hs' hs]

中文:
引理 le_sInf
  条件: (hs : 对任意 x in s, a <= x) (ha : a <= 0)
  结论: a <= sInf s
  证明: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [ha.trans_eq sInf_empty.symm, le_csInf hs' hs]
-/
protected lemma le_sInf (hs : forall x in s, a <= x) (ha : a <= 0) : a <= sInf s := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [ha.trans_eq sInf_empty.symm, le_csInf hs' hs]

/--
lemma `le_iInf` / 引理 `le_iInf`

English:
lemma le_iInf
  given: (hf : forall i, a <= f i) (ha : a <= 0)
  statement: a <= ⨅ i, f i
  proof: Real.le_sInf (Set.forall_mem_range.2 hf) ha

中文:
引理 le_iInf
  条件: (hf : 对任意 i, a <= f i) (ha : a <= 0)
  结论: a <= ⨅ i, f i
  证明: Real.le_sInf (Set.forall_mem_range.2 hf) ha
-/
protected lemma le_iInf (hf : forall i, a <= f i) (ha : a <= 0) : a <= ⨅ i, f i :=
  Real.le_sInf (Set.forall_mem_range.2 hf) ha

/--
lemma `sSup_nonpos` / 引理 `sSup_nonpos`

English:
lemma sSup_nonpos
  given: (hs : forall x in s, x <= 0)
  statement: sSup s <= 0
  proof: Real.sSup_le hs le_rfl

中文:
引理 sSup_nonpos
  条件: (hs : 对任意 x in s, x <= 0)
  结论: sSup s <= 0
  证明: Real.sSup_le hs le_rfl

Depends on / 依赖: Real.sSup_le, le_rfl, sSup_le
-/
lemma sSup_nonpos (hs : forall x in s, x <= 0) : sSup s <= 0 := Real.sSup_le hs le_rfl

/--
lemma `iSup_nonpos` / 引理 `iSup_nonpos`

English:
lemma iSup_nonpos
  given: (hf : forall i, f i <= 0)
  statement: ⨆ i, f i <= 0
  proof: Real.iSup_le hf le_rfl

中文:
引理 iSup_nonpos
  条件: (hf : 对任意 i, f i <= 0)
  结论: ⨆ i, f i <= 0
  证明: Real.iSup_le hf le_rfl

Depends on / 依赖: Real.iSup_le, iSup_le, le_rfl
-/
lemma iSup_nonpos (hf : forall i, f i <= 0) : ⨆ i, f i <= 0 := Real.iSup_le hf le_rfl

/--
lemma `sInf_nonneg` / 引理 `sInf_nonneg`

English:
lemma sInf_nonneg
  given: (hs : forall x in s, 0 <= x)
  statement: 0 <= sInf s
  proof: Real.le_sInf hs le_rfl

中文:
引理 sInf_nonneg
  条件: (hs : 对任意 x in s, 0 <= x)
  结论: 0 <= sInf s
  证明: Real.le_sInf hs le_rfl

Depends on / 依赖: Real.le_sInf, le_rfl, le_sInf
-/
lemma sInf_nonneg (hs : forall x in s, 0 <= x) : 0 <= sInf s := Real.le_sInf hs le_rfl

/--
lemma `iInf_nonneg` / 引理 `iInf_nonneg`

English:
lemma iInf_nonneg
  given: (hf : forall i, 0 <= f i)
  statement: 0 <= iInf f
  proof: Real.le_iInf hf le_rfl

中文:
引理 iInf_nonneg
  条件: (hf : 对任意 i, 0 <= f i)
  结论: 0 <= iInf f
  证明: Real.le_iInf hf le_rfl

Depends on / 依赖: Real.le_iInf, le_iInf, le_rfl
-/
lemma iInf_nonneg (hf : forall i, 0 <= f i) : 0 <= iInf f := Real.le_iInf hf le_rfl

/--
lemma `sSup_nonneg'` / 引理 `sSup_nonneg'`

English:
lemma sSup_nonneg'
  given: (hs : exists x in s, 0 <= x)
  statement: 0 <= sSup s
  proof: by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h => le_csSup_of_le h hxs hx) fun h => (sSup_of_not_bddAbove h).ge

中文:
引理 sSup_nonneg'
  条件: (hs : 存在 x in s, 0 <= x)
  结论: 0 <= sSup s
  证明: by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h => le_csSup_of_le h hxs hx) fun h => (sSup_of_not_bddAbove h).ge

Depends on / 依赖: classical, le_csSup_of_le, sSup_of_not_bddAbove
-/
lemma sSup_nonneg' (hs : exists x in s, 0 <= x) : 0 <= sSup s := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h => le_csSup_of_le h hxs hx) fun h => (sSup_of_not_bddAbove h).ge

/--
lemma `iSup_nonneg'` / 引理 `iSup_nonneg'`

English:
lemma iSup_nonneg'
  given: (hf : exists i, 0 <= f i)
  statement: 0 <= ⨆ i, f i
  proof: sSup_nonneg' Set.exists_range_iff.2 hf

中文:
引理 iSup_nonneg'
  条件: (hf : 存在 i, 0 <= f i)
  结论: 0 <= ⨆ i, f i
  证明: sSup_nonneg' Set.exists_range_iff.2 hf

Depends on / 依赖: Set.exists_range_iff, exists_range_iff, sSup_nonneg
-/
lemma iSup_nonneg' (hf : exists i, 0 <= f i) : 0 <= ⨆ i, f i := sSup_nonneg' Set.exists_range_iff.2 hf

/--
lemma `sInf_nonpos'` / 引理 `sInf_nonpos'`

English:
lemma sInf_nonpos'
  given: (hs : exists x in s, x <= 0)
  statement: sInf s <= 0
  proof: by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h => csInf_le_of_le h hxs hx) fun h => (sInf_of_not_bddBelow h).le

中文:
引理 sInf_nonpos'
  条件: (hs : 存在 x in s, x <= 0)
  结论: sInf s <= 0
  证明: by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h => csInf_le_of_le h hxs hx) fun h => (sInf_of_not_bddBelow h).le

Depends on / 依赖: classical, csInf_le_of_le, sInf_of_not_bddBelow
-/
lemma sInf_nonpos' (hs : exists x in s, x <= 0) : sInf s <= 0 := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h => csInf_le_of_le h hxs hx) fun h => (sInf_of_not_bddBelow h).le

/--
lemma `iInf_nonpos'` / 引理 `iInf_nonpos'`

English:
lemma iInf_nonpos'
  given: (hf : exists i, f i <= 0)
  statement: ⨅ i, f i <= 0
  proof: sInf_nonpos' Set.exists_range_iff.2 hf

中文:
引理 iInf_nonpos'
  条件: (hf : 存在 i, f i <= 0)
  结论: ⨅ i, f i <= 0
  证明: sInf_nonpos' Set.exists_range_iff.2 hf

Depends on / 依赖: Set.exists_range_iff, exists_range_iff, sInf_nonpos
-/
lemma iInf_nonpos' (hf : exists i, f i <= 0) : ⨅ i, f i <= 0 := sInf_nonpos' Set.exists_range_iff.2 hf

/--
lemma `sSup_nonneg` / 引理 `sSup_nonneg`

English:
lemma sSup_nonneg
  given: (hs : forall x in s, 0 <= x)
  statement: 0 <= sSup s
  proof: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sSup_empty.ge
  · exact sSup_nonneg' ⟨x, hx, hs _ hx⟩

中文:
引理 sSup_nonneg
  条件: (hs : 对任意 x in s, 0 <= x)
  结论: 0 <= sSup s
  证明: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sSup_empty.ge
  · exact sSup_nonneg' ⟨x, hx, hs _ hx⟩

Depends on / 依赖: eq_empty_or_nonempty, s.eq_empty_or_nonempty, sSup_empty, sSup_empty.ge, sSup_nonneg
-/
lemma sSup_nonneg (hs : forall x in s, 0 <= x) : 0 <= sSup s := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sSup_empty.ge
  · exact sSup_nonneg' ⟨x, hx, hs _ hx⟩

/--
lemma `iSup_nonneg` / 引理 `iSup_nonneg`

English:
lemma iSup_nonneg
  given: (hf : forall i, 0 <= f i)
  statement: 0 <= ⨆ i, f i
  proof: sSup_nonneg Set.forall_mem_range.2 hf

中文:
引理 iSup_nonneg
  条件: (hf : 对任意 i, 0 <= f i)
  结论: 0 <= ⨆ i, f i
  证明: sSup_nonneg Set.forall_mem_range.2 hf

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, sSup_nonneg
-/
lemma iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i := sSup_nonneg Set.forall_mem_range.2 hf

/--
lemma `iSup_nonneg_of_nonnegHomClass` / 引理 `iSup_nonneg_of_nonnegHomClass`

English:
lemma iSup_nonneg_of_nonnegHomClass
  statement: {ι F α : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F)
  proof: iSup_nonneg (fun i => apply_nonneg f (g i))

中文:
引理 iSup_nonneg_of_nonnegHomClass
  结论: {ι F α : 类型} [FunLike F α 实数] [NonnegHomClass F α 实数] (f : F)
  证明: iSup_nonneg (fun i => apply_nonneg f (g i))

Depends on / 依赖: apply_nonneg, iSup_nonneg
-/
lemma iSup_nonneg_of_nonnegHomClass {ι F α : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F)
    (g : ι -> α) :
    0 <= ⨆ i, f (g i) :=
  iSup_nonneg (fun i => apply_nonneg f (g i))

/--
lemma `sInf_nonpos` / 引理 `sInf_nonpos`

English:
lemma sInf_nonpos
  given: (hs : forall x in s, x <= 0)
  statement: sInf s <= 0
  proof: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sInf_empty.le
  · exact sInf_nonpos' ⟨x, hx, hs _ hx⟩

中文:
引理 sInf_nonpos
  条件: (hs : 对任意 x in s, x <= 0)
  结论: sInf s <= 0
  证明: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sInf_empty.le
  · exact sInf_nonpos' ⟨x, hx, hs _ hx⟩

Depends on / 依赖: eq_empty_or_nonempty, s.eq_empty_or_nonempty, sInf_empty, sInf_empty.le, sInf_nonpos
-/
lemma sInf_nonpos (hs : forall x in s, x <= 0) : sInf s <= 0 := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sInf_empty.le
  · exact sInf_nonpos' ⟨x, hx, hs _ hx⟩

/--
lemma `iInf_nonpos` / 引理 `iInf_nonpos`

English:
lemma iInf_nonpos
  given: (hf : forall i, f i <= 0)
  statement: ⨅ i, f i <= 0
  proof: sInf_nonpos Set.forall_mem_range.2 hf

中文:
引理 iInf_nonpos
  条件: (hf : 对任意 i, f i <= 0)
  结论: ⨅ i, f i <= 0
  证明: sInf_nonpos Set.forall_mem_range.2 hf

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, sInf_nonpos
-/
lemma iInf_nonpos (hf : forall i, f i <= 0) : ⨅ i, f i <= 0 := sInf_nonpos Set.forall_mem_range.2 hf

/--
theorem `sInf_le_sSup` / 定理 `sInf_le_sSup`

English:
theorem sInf_le_sSup
  given: (s : Set Real) (h₁ : BddBelow s) (h₂ : BddAbove s)
  statement: sInf s <= sSup s
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [sInf_empty, sSup_empty]
  · exact csInf_le_csSup hne h₁ h₂

中文:
定理 sInf_le_sSup
  条件: (s : Set 实数) (h₁ : BddBelow s) (h₂ : BddAbove s)
  结论: sInf s <= sSup s
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [sInf_empty, sSup_empty]
  · exact csInf_le_csSup hne h₁ h₂

Depends on / 依赖: csInf_le_csSup, eq_empty_or_nonempty, s.eq_empty_or_nonempty, sInf_empty, sSup_empty
-/
theorem sInf_le_sSup (s : Set Real) (h₁ : BddBelow s) (h₂ : BddAbove s) : sInf s <= sSup s := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [sInf_empty, sSup_empty]
  · exact csInf_le_csSup hne h₁ h₂

/--
theorem `cauSeq_converges` / 定理 `cauSeq_converges`

English:
theorem cauSeq_converges
  given: (f : CauSeq Real abs)
  statement: exists x, f ≈ const abs x
  proof: by
  let s := {x : Real | const abs x < f}
  have lb : exists x, x in s := exists_lt f
  have ub' : forall x, f < const abs x -> forall y in s, y <= x := fun x h y yS =>
le_of_lt const_lt.1 CauSeq.lt_trans yS h
  have ub : exists x, forall y in s, y <= x := (exists_gt f).imp ub'
  refine ⟨sSup s, ((

中文:
定理 cauSeq_converges
  条件: (f : CauSeq 实数 abs)
  结论: 存在 x, f ≈ const abs x
  证明: by
  let s := {x : Real | const abs x < f}
  have lb : exists x, x in s := exists_lt f
  have ub' : forall x, f < const abs x -> forall y in s, y <= x := fun x h y yS =>
le_of_lt const_lt.1 CauSeq.lt_trans yS h
  have ub : exists x, forall y in s, y <= x := (exists_gt f).imp ub'
  refine ⟨sSup s, ((

Depends on / 依赖: CauSeq, CauSeq.lt_trans, const_lt, csSup_le, exists_gt, exists_lt, half_pos, le_of_lt, lt_total, lt_trans, not_gt, resolve_left, resolve_right, sub_lt_self
-/
theorem cauSeq_converges (f : CauSeq Real abs) : exists x, f ≈ const abs x := by
  let s := {x : Real | const abs x < f}
  have lb : exists x, x in s := exists_lt f
  have ub' : forall x, f < const abs x -> forall y in s, y <= x := fun x h y yS =>
le_of_lt const_lt.1 CauSeq.lt_trans yS h
  have ub : exists x, forall y in s, y <= x := (exists_gt f).imp ub'
  refine ⟨sSup s, ((lt_total _ _).resolve_left fun h => ?_).resolve_right fun h => ?_⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (csSup_le lb (ub' _ ?_)).not_gt (sub_lt_self _ (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply]; rw [const_apply]; rw [sub_right_comm]; rw [le_sub_iff_add_le]; rw [add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (le_csSup ub ?_).not_gt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply]; rw [const_apply]; rw [add_comm]; rw [← sub_sub]; rw [le_sub_iff_add_le]; rw [add_halves]
    exact ih _ ij

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CauSeq.IsComplete Real abs
  body: ⟨cauSeq_converges⟩

中文:
实例 :
  签名: CauSeq.IsComplete 实数 abs
  定义体: ⟨cauSeq_converges⟩

Depends on / 依赖: SMulCommClass, cauSeq_converges
-/
instance : CauSeq.IsComplete Real abs :=
  ⟨cauSeq_converges⟩

open Set

/--
theorem `iInf_Ioi_eq_iInf_rat_gt` / 定理 `iInf_Ioi_eq_iInf_rat_gt`

English:
theorem iInf_Ioi_eq_iInf_rat_gt
  statement: {f : Real -> Real} (x : Real) (hf : BddBelow (f '' Ioi x))
  proof: by
  refine le_antisymm ?_ ?_
  · have : Nonempty { r' : Rat // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine le_ciInf fun r => ?_
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine ciInf_set_le hf (hxy.trans ?_)
    exact_mod_cast hyr
  · refi

中文:
定理 iInf_Ioi_eq_iInf_rat_gt
  结论: {f : 实数 -> 实数} (x : 实数) (hf : BddBelow (f '' Ioi x))
  证明: by
  refine le_antisymm ?_ ?_
  · have : Nonempty { r' : Rat // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine le_ciInf fun r => ?_
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine ciInf_set_le hf (hxy.trans ?_)
    exact_mod_cast hyr
  · refi

Depends on / 依赖: IsScalarTower, Nonempty, choose_s, ciInf_le, ciInf_set_le, exists_rat_btwn, exists_rat_gt, hf.choose_s, hf.some, hxy.trans, le_antisymm, le_ciInf, mem_Ioi, q.prop, r.prop
-/
theorem iInf_Ioi_eq_iInf_rat_gt {f : Real -> Real} (x : Real) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : Rat // x < q' }, f q := by
  refine le_antisymm ?_ ?_
  · have : Nonempty { r' : Rat // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine le_ciInf fun r => ?_
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine ciInf_set_le hf (hxy.trans ?_)
    exact_mod_cast hyr
  · refine le_ciInf fun q => ?_
    have hq := q.prop
    rw [mem_Ioi] at hq
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    refine (ciInf_le ?_ ?_).trans ?_
    · refine ⟨hf.some, fun z => ?_⟩
      rintro ⟨u, rfl⟩
      suffices hfu : f u in f '' Ioi x from hf.choose_spec hfu
      exact ⟨u, u.prop, rfl⟩
    · exact ⟨y, hxy⟩
    · refine hf_mono (le_trans ?_ hyq.le)
      norm_cast

/--
theorem `not_bddAbove_coe` / 定理 `not_bddAbove_coe`

English:
theorem not_bddAbove_coe
  statement: ¬ (BddAbove <| range (fun (x : Rat) => (x : Real)))
  proof: by
  dsimp only [BddAbove, upperBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_gt _

中文:
定理 not_bddAbove_coe
  结论: ¬ (BddAbove <| range (fun (x : Rat) => (x : 实数)))
  证明: by
  dsimp only [BddAbove, upperBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_gt _

Depends on / 依赖: BddAbove, Set.not_nonempty_iff_eq_empty, exists_rat_gt, not_nonempty_iff_eq_empty, upperBounds
-/
theorem not_bddAbove_coe : ¬ (BddAbove <| range (fun (x : Rat) => (x : Real))) := by
  dsimp only [BddAbove, upperBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_gt _

/--
theorem `not_bddBelow_coe` / 定理 `not_bddBelow_coe`

English:
theorem not_bddBelow_coe
  statement: ¬ (BddBelow <| range (fun (x : Rat) => (x : Real)))
  proof: by
  dsimp only [BddBelow, lowerBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_lt _

中文:
定理 not_bddBelow_coe
  结论: ¬ (BddBelow <| range (fun (x : Rat) => (x : 实数)))
  证明: by
  dsimp only [BddBelow, lowerBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_lt _

Depends on / 依赖: BddBelow, Set.not_nonempty_iff_eq_empty, exists_rat_lt, lowerBounds, not_nonempty_iff_eq_empty
-/
theorem not_bddBelow_coe : ¬ (BddBelow <| range (fun (x : Rat) => (x : Real))) := by
  dsimp only [BddBelow, lowerBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_lt _

/--
theorem `iUnion_Iic_rat` / 定理 `iUnion_Iic_rat`

English:
theorem iUnion_Iic_rat
  statement: ⋃ r : Rat, Iic (r : Real) = univ
  proof: by
  exact iUnion_Iic_of_not_bddAbove_range not_bddAbove_coe

中文:
定理 iUnion_Iic_rat
  结论: ⋃ r : Rat, Iic (r : 实数) = univ
  证明: by
  exact iUnion_Iic_of_not_bddAbove_range not_bddAbove_coe

Depends on / 依赖: iUnion_Iic_of_not_bddAbove_range, not_bddAbove_coe
-/
theorem iUnion_Iic_rat : ⋃ r : Rat, Iic (r : Real) = univ := by
  exact iUnion_Iic_of_not_bddAbove_range not_bddAbove_coe

/--
theorem `iInter_Iic_rat` / 定理 `iInter_Iic_rat`

English:
theorem iInter_Iic_rat
  statement: ⋂ r : Rat, Iic (r : Real) = ∅
  proof: by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe

中文:
定理 iInter_Iic_rat
  结论: ⋂ r : Rat, Iic (r : 实数) = ∅
  证明: by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe

Depends on / 依赖: iInter_Iic_eq_empty_iff, iInter_Iic_eq_empty_iff.mpr, not_bddBelow_coe
-/
theorem iInter_Iic_rat : ⋂ r : Rat, Iic (r : Real) = ∅ := by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe

/--
lemma `exists_natCast_add_one_lt_pow_of_one_lt` / 引理 `exists_natCast_add_one_lt_pow_of_one_lt`

English:
lemma exists_natCast_add_one_lt_pow_of_one_lt
  given: (ha : 1 < a)
  statement: exists m : Nat, (m + 1 : Real) < a ^ m
  proof: by
  obtain ⟨k, posk, hk⟩ : exists k : Nat, 0 < k ∧ 1 / k + 1 < a := by
    contrapose! ha
    refine le_of_forall_lt_rat_imp_le ?_
    intro q hq
    refine (ha q.den (by positivity)).trans ?_
    rw [← le_sub_iff_add_le]; rw [div_le_iff₀ (by positivity)]; rw [sub_mul]; rw [one_mul]
    norm_cast a

中文:
引理 exists_natCast_add_one_lt_pow_of_one_lt
  条件: (ha : 1 < a)
  结论: 存在 m : 自然数, (m + 1 : 实数) < a ^ m
  证明: by
  obtain ⟨k, posk, hk⟩ : exists k : Nat, 0 < k ∧ 1 / k + 1 < a := by
    contrapose! ha
    refine le_of_forall_lt_rat_imp_le ?_
    intro q hq
    refine (ha q.den (by positivity)).trans ?_
    rw [← le_sub_iff_add_le]; rw [div_le_iff₀ (by positivity)]; rw [sub_mul]; rw [one_mul]
    norm_cast a

Depends on / 依赖: Nat.two_mul_sq_add_one_le_two_pow_two_, contrapose, le_of_forall_lt_rat_imp_le, le_sub_iff_add_le, mod_cast, mul_den_eq_num, num_div_den, one_lt_div, one_mul, q.den, q.mul_den_eq_num, q.num_div_den, sub_mul, two_mul_sq_add_one_le_two_pow_two_
-/
lemma exists_natCast_add_one_lt_pow_of_one_lt (ha : 1 < a) : exists m : Nat, (m + 1 : Real) < a ^ m := by
  obtain ⟨k, posk, hk⟩ : exists k : Nat, 0 < k ∧ 1 / k + 1 < a := by
    contrapose! ha
    refine le_of_forall_lt_rat_imp_le ?_
    intro q hq
    refine (ha q.den (by positivity)).trans ?_
    rw [← le_sub_iff_add_le]; rw [div_le_iff₀ (by positivity)]; rw [sub_mul]; rw [one_mul]
    norm_cast at hq ⊢
    rw [← q.num_div_den]; rw [one_lt_div (by positivity)] at hq
    rw [q.mul_den_eq_num]
    norm_cast at hq ⊢
    lia
  use 2 * k ^ 2
  calc
    ((2 * k ^ 2 : Nat) + 1 : Real) <= 2 ^ (2 * k) := mod_cast Nat.two_mul_sq_add_one_le_two_pow_two_mul _
    _ = (1 / k * k + 1 : Real) ^ (2 * k) := by simp [posk.ne']; norm_num
    _ <= ((1 / k + 1) ^ k : Real) ^ (2 * k) := by gcongr; exact mul_add_one_le_add_one_pow (by simp) _
    _ = (1 / k + 1 : Real) ^ (2 * k ^ 2) := by rw [← pow_mul, mul_left_comm, sq]
    _ < a ^ (2 * k ^ 2) := by gcongr

/--
lemma `exists_nat_pos_inv_lt` / 引理 `exists_nat_pos_inv_lt`

English:
lemma exists_nat_pos_inv_lt
  given: {b : Real} (hb : 0 < b)
  proof: by
  refine (exists_nat_gt b⁻¹).imp fun k hk => ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

中文:
引理 exists_nat_pos_inv_lt
  条件: {b : 实数} (hb : 0 < b)
  证明: by
  refine (exists_nat_gt b⁻¹).imp fun k hk => ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

Depends on / 依赖: Nat.cast_pos.mp, cast_pos, exists_nat_gt, inv_pos_of_pos
-/
lemma exists_nat_pos_inv_lt {b : Real} (hb : 0 < b) :
    exists (n : Nat), 0 < n ∧ (n : Real)⁻¹ < b := by
  refine (exists_nat_gt b⁻¹).imp fun k hk => ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

end Real
