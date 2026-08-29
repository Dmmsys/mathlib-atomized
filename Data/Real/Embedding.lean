/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Embedding of archimedean groups into reals

This file provides embedding of any archimedean groups into reals.

## Main declarations
* `Archimedean.embedReal` defines an injective `M →+o ℝ` for archimedean group `M` with a positive
  `1` element. `1` is preserved by the map.
* `Archimedean.exists_orderAddMonoidHom_real_injective` states there exists an injective `M →+o ℝ`
  for any archimedean group `M` without specifying the `1` element in `M`.
-/

@[expose] public section


variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]

/--
theorem `mul_smul_one_lt_iff` / 定理 `mul_smul_one_lt_iff`

English:
theorem mul_smul_one_lt_iff
  given: {num : Int} {n den : Nat} (hn : 0 < n) {x : M}
  proof: by
  rw [mul_comm num]; rw [mul_smul]; rw [mul_smul]; rw [natCast_zsmul x den]
  exact ⟨fun h => lt_of_smul_lt_smul_left h (Int.natCast_nonneg n),
    fun h => zsmul_lt_zsmul_right (Int.natCast_pos.mpr hn) h⟩

中文:
定理 mul_smul_one_lt_iff
  条件: {num : 整数} {n den : 自然数} (hn : 0 < n) {x : M}
  证明: by
  rw [mul_comm num]; rw [mul_smul]; rw [mul_smul]; rw [natCast_zsmul x den]
  exact ⟨fun h => lt_of_smul_lt_smul_left h (Int.natCast_nonneg n),
    fun h => zsmul_lt_zsmul_right (Int.natCast_pos.mpr hn) h⟩

Depends on / 依赖: Int.natCast_nonneg, Int.natCast_pos.mpr, lt_of_smul_lt_smul_left, mul_comm, mul_smul, natCast_nonneg, natCast_pos, natCast_zsmul, zsmul_lt_zsmul_right
-/
theorem mul_smul_one_lt_iff {num : Int} {n den : Nat} (hn : 0 < n) {x : M} :
    (num * n) • 1 < (n * den : Int) • x ↔ num • 1 < den • x := by
  rw [mul_comm num]; rw [mul_smul]; rw [mul_smul]; rw [natCast_zsmul x den]
  exact ⟨fun h => lt_of_smul_lt_smul_left h (Int.natCast_nonneg n),
    fun h => zsmul_lt_zsmul_right (Int.natCast_pos.mpr hn) h⟩

/--
theorem `num_smul_one_lt_den_smul_add` / 定理 `num_smul_one_lt_den_smul_add`

English:
theorem num_smul_one_lt_den_smul_add
  statement: {u v : Rat} {x y : M}
  proof: by
  have hu' : (u.num * v.den) • 1 < (u.den * v.den : Int) • x := by
    simpa [mul_comm] using (mul_smul_one_lt_iff v.den_pos).mpr hu
  suffices ((u + v).num * u.den * v.den) • 1 <
      ((u + v).den : Int) • (u.den * v.den : Int) • (x + y) by
    refine (mul_smul_one_lt_iff (mul_pos u.den_pos v.d

中文:
定理 num_smul_one_lt_den_smul_add
  结论: {u v : Rat} {x y : M}
  证明: by
  have hu' : (u.num * v.den) • 1 < (u.den * v.den : Int) • x := by
    simpa [mul_comm] using (mul_smul_one_lt_iff v.den_pos).mpr hu
  suffices ((u + v).num * u.den * v.den) • 1 <
      ((u + v).den : Int) • (u.den * v.den : Int) • (x + y) by
    refine (mul_smul_one_lt_iff (mul_pos u.den_pos v.d

Depends on / 依赖: Nat.cast_mul, Rat.add_num_den, add_num_den, cast_mul, den_pos, mul_assoc, mul_comm, mul_pos, mul_smul_one_lt_iff, smul_assoc, smul_eq_mul, smul_lt_smul_iff_of_pos_left, smul_smul, u.den, u.den_pos, u.num, v.den, v.den_pos
-/
theorem num_smul_one_lt_den_smul_add {u v : Rat} {x y : M}
    (hu : u.num • 1 < u.den • x) (hv : v.num • 1 < v.den • y) :
    (u + v).num • 1 < (u + v).den • (x + y) := by
  have hu' : (u.num * v.den) • 1 < (u.den * v.den : Int) • x := by
    simpa [mul_comm] using (mul_smul_one_lt_iff v.den_pos).mpr hu
  suffices ((u + v).num * u.den * v.den) • 1 <
      ((u + v).den : Int) • (u.den * v.den : Int) • (x + y) by
    refine (mul_smul_one_lt_iff (mul_pos u.den_pos v.den_pos)).mp ?_
    rwa [Nat.cast_mul, ← mul_assoc, mul_comm _ ((u + v).den : Int), ← smul_eq_mul ((u + v).den : Int),
      smul_assoc]
  rw [Rat.add_num_den']; rw [mul_comm]; rw [← smul_smul]
  rw [smul_lt_smul_iff_of_pos_left (by simpa using (u + v).den_pos)]
  rw [add_smul]; rw [smul_add]
  exact add_lt_add hu' ((mul_smul_one_lt_iff u.den_pos).mpr hv)

/--
theorem `num_le_nat_mul_den` / 定理 `num_le_nat_mul_den`

English:
theorem num_le_nat_mul_den
  statement: [ZeroLEOneClass M] [NeZero (1 : M)]
  proof: by
  refine le_of_smul_le_smul_right (h.trans ?_) (by simp)
  rw [mul_comm]; rw [← smul_smul]
  simpa using nsmul_le_nsmul_right hn den

中文:
定理 num_le_nat_mul_den
  结论: [ZeroLEOneClass M] [NeZero (1 : M)]
  证明: by
  refine le_of_smul_le_smul_right (h.trans ?_) (by simp)
  rw [mul_comm]; rw [← smul_smul]
  simpa using nsmul_le_nsmul_right hn den

Depends on / 依赖: h.trans, le_of_smul_le_smul_right, mul_comm, nsmul_le_nsmul_right, smul_smul
-/
theorem num_le_nat_mul_den [ZeroLEOneClass M] [NeZero (1 : M)]
    {num : Int} {den : Nat} {x : M} (h : num • 1 <= den • x)
    {n : Int} (hn : x <= n • 1) : num <= n * den := by
  refine le_of_smul_le_smul_right (h.trans ?_) (by simp)
  rw [mul_comm]; rw [← smul_smul]
  simpa using nsmul_le_nsmul_right hn den

namespace Archimedean

/--
Definition of `ratLt` / `ratLt` 的定义

English:
abbreviation ratLt
  signature: (x : M)
  body: {r | r.num • 1 < r.den • x}

中文:
缩写 ratLt
  签名: (x : M)
  定义体: {r | r.num • 1 < r.den • x}

Depends on / 依赖: r.den, r.num
-/
abbrev ratLt (x : M) : Set Rat := {r | r.num • 1 < r.den • x}

/--
theorem `mkRat_mem_ratLt` / 定理 `mkRat_mem_ratLt`

English:
theorem mkRat_mem_ratLt
  given: {num : Int} {den : Nat} (hden : den != 0) {x : M}
  proof: by
  rw [Set.mem_ofPred]
  obtain ⟨m, hm0, hnum, hden⟩ := Rat.mkRat_num_den hden (show mkRat num den = _ by rfl)
  conv in num • 1 => rw [hnum, mul_comm, ← smul_smul, natCast_zsmul]
  conv in den • x => rw [hden, mul_comm, ← smul_smul]
  exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm

中文:
定理 mkRat_mem_ratLt
  条件: {num : 整数} {den : 自然数} (hden : den != 0) {x : M}
  证明: by
  rw [Set.mem_ofPred]
  obtain ⟨m, hm0, hnum, hden⟩ := Rat.mkRat_num_den hden (show mkRat num den = _ by rfl)
  conv in num • 1 => rw [hnum, mul_comm, ← smul_smul, natCast_zsmul]
  conv in den • x => rw [hden, mul_comm, ← smul_smul]
  exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm

Depends on / 依赖: Nat.zero_lt_of_ne_zero, Rat.mkRat_num_den, Set.mem_ofPred, mem_ofPred, mkRat_num_den, mul_comm, natCast_zsmul, smul_lt_smul_iff_of_pos_left, smul_smul, zero_lt_of_ne_zero
-/
theorem mkRat_mem_ratLt {num : Int} {den : Nat} (hden : den != 0) {x : M} :
    mkRat num den in ratLt x ↔ num • 1 < den • x := by
  rw [Set.mem_ofPred]
  obtain ⟨m, hm0, hnum, hden⟩ := Rat.mkRat_num_den hden (show mkRat num den = _ by rfl)
  conv in num • 1 => rw [hnum, mul_comm, ← smul_smul, natCast_zsmul]
  conv in den • x => rw [hden, mul_comm, ← smul_smul]
  exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm0)).symm

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `ratLt'` / `ratLt'` 的定义

English:
abbreviation ratLt'
  signature: (x : M)
  body: (Rat.castHom Real) '' (ratLt x)

中文:
缩写 ratLt'
  签名: (x : M)
  定义体: (Rat.castHom Real) '' (ratLt x)

Depends on / 依赖: Rat.castHom, castHom
-/
noncomputable abbrev ratLt' (x : M) : Set Real := (Rat.castHom Real) '' (ratLt x)

/-- Mapping `M` to `ℝ`, defined as the supremum of `ratLt' x`. -/
noncomputable
/--
Definition of `embedRealFun` / `embedRealFun` 的定义

English:
abbreviation embedRealFun
  signature: (x : M)
  body: sSup (ratLt' x)

中文:
缩写 embedRealFun
  签名: (x : M)
  定义体: sSup (ratLt' x)
-/
abbrev embedRealFun (x : M) := sSup (ratLt' x)

variable [ZeroLEOneClass M] [NeZero (1 : M)] [Archimedean M]

/--
theorem `ratLt_bddAbove` / 定理 `ratLt_bddAbove`

English:
theorem ratLt_bddAbove
  given: (x : M)
  statement: BddAbove (ratLt x)
  proof: by
  obtain ⟨n, hn⟩ := Archimedean.arch x zero_lt_one
  use n
  rw [ratLt]; rw [mem_upperBounds]
  intro ⟨num, den, _, _⟩
  rw [Rat.le_iff]
  suffices num • 1 < den • x -> num <= n * den by simpa using this
  intro h
  exact num_le_nat_mul_den h.le (by simpa using hn)

中文:
定理 ratLt_bddAbove
  条件: (x : M)
  结论: BddAbove (ratLt x)
  证明: by
  obtain ⟨n, hn⟩ := Archimedean.arch x zero_lt_one
  use n
  rw [ratLt]; rw [mem_upperBounds]
  intro ⟨num, den, _, _⟩
  rw [Rat.le_iff]
  suffices num • 1 < den • x -> num <= n * den by simpa using this
  intro h
  exact num_le_nat_mul_den h.le (by simpa using hn)

Depends on / 依赖: Archimedean, Archimedean.arch, Rat.le_iff, h.le, le_iff, mem_upperBounds, num_le_nat_mul_den, zero_lt_one
-/
theorem ratLt_bddAbove (x : M) : BddAbove (ratLt x) := by
  obtain ⟨n, hn⟩ := Archimedean.arch x zero_lt_one
  use n
  rw [ratLt]; rw [mem_upperBounds]
  intro ⟨num, den, _, _⟩
  rw [Rat.le_iff]
  suffices num • 1 < den • x -> num <= n * den by simpa using this
  intro h
  exact num_le_nat_mul_den h.le (by simpa using hn)

/--
theorem `ratLt_nonempty` / 定理 `ratLt_nonempty`

English:
theorem ratLt_nonempty
  given: (x : M)
  statement: (ratLt x).Nonempty
  proof: by
  obtain hneg | rfl | hxpos := lt_trichotomy x 0
  · obtain ⟨n, hn⟩ := Archimedean.arch (-x - x) zero_lt_one
    use Rat.ofInt (-n)
    suffices -(n • 1) < x by simpa using this
    exact neg_lt.mpr (lt_of_lt_of_le (by simpa using hneg) hn)
  · exact ⟨Rat.ofInt (-1), by simp⟩
  · obtain ⟨n, hn⟩ :

中文:
定理 ratLt_nonempty
  条件: (x : M)
  结论: (ratLt x).Nonempty
  证明: by
  obtain hneg | rfl | hxpos := lt_trichotomy x 0
  · obtain ⟨n, hn⟩ := Archimedean.arch (-x - x) zero_lt_one
    use Rat.ofInt (-n)
    suffices -(n • 1) < x by simpa using this
    exact neg_lt.mpr (lt_of_lt_of_le (by simpa using hneg) hn)
  · exact ⟨Rat.ofInt (-1), by simp⟩
  · obtain ⟨n, hn⟩ :

Depends on / 依赖: Archimedean, Archimedean.arch, Rat.mk, Rat.ofInt, hn.trans_lt, lt_of_lt_of_le, lt_trichotomy, neg_lt, neg_lt.mpr, nsmul_lt_nsmul_iff_left, trans_lt, zero_lt_one
-/
theorem ratLt_nonempty (x : M) : (ratLt x).Nonempty := by
  obtain hneg | rfl | hxpos := lt_trichotomy x 0
  · obtain ⟨n, hn⟩ := Archimedean.arch (-x - x) zero_lt_one
    use Rat.ofInt (-n)
    suffices -(n • 1) < x by simpa using this
    exact neg_lt.mpr (lt_of_lt_of_le (by simpa using hneg) hn)
  · exact ⟨Rat.ofInt (-1), by simp⟩
  · obtain ⟨n, hn⟩ := Archimedean.arch 1 hxpos
    use Rat.mk' 1 (n + 1) (by simp) (by simp)
simpa using hn.trans_lt (nsmul_lt_nsmul_iff_left hxpos).mpr (by simp)

open scoped Pointwise in
/--
theorem `ratLt_add` / 定理 `ratLt_add`

English:
theorem ratLt_add
  given: (x y : M)
  statement: ratLt (x + y) = ratLt x + ratLt y
  proof: by
  ext a
  rw [Set.mem_add]
  constructor
  · /- Given `a ∈ ratLt 1 (x + y)`, find `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y`
      such that `u + v = a`.
      In a naive attempt, one can take the denominator `d` of `a`,
      and find the largest `u = p / d < x / 1`.
      However, `d` could be too "coars

中文:
定理 ratLt_add
  条件: (x y : M)
  结论: ratLt (x + y) = ratLt x + ratLt y
  证明: by
  ext a
  rw [Set.mem_add]
  constructor
  · /- Given `a ∈ ratLt 1 (x + y)`, find `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y`
      such that `u + v = a`.
      In a naive attempt, one can take the denominator `d` of `a`,
      and find the largest `u = p / d < x / 1`.
      However, `d` could be too "coars

Depends on / 依赖: Archimedean, Archimedean.arch, However, Set.mem_add, Set.mem_ofPred_eq, a.num, attempt, coarse, denominator, enough, ensure, largest, mem_add, mem_ofPred_eq
-/
theorem ratLt_add (x y : M) : ratLt (x + y) = ratLt x + ratLt y := by
  ext a
  rw [Set.mem_add]
  constructor
  · /- Given `a ∈ ratLt 1 (x + y)`, find `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y`
      such that `u + v = a`.
      In a naive attempt, one can take the denominator `d` of `a`,
      and find the largest `u = p / d < x / 1`.
      However, `d` could be too "coarse", and `v = a - u` could be 1/d too large than `y / 1`.
      To ensure a large enough denominator, we take `d * k`, where
      `1 + 1 ≤ k • (d • (x + y) - a.num • 1)`. -/
    intro h
    rw [Set.mem_ofPred_eq] at h
obtain ⟨k, hk⟩ := Archimedean.arch (1 + 1) sub_pos.mpr h
    have hk0 : k != 0 := by
      contrapose! hk
      simp [hk]
    have hka0 : k * a.den != 0 := mul_ne_zero hk0 a.den_ne_zero
    obtain ⟨m, ⟨hm1, hm2⟩, _⟩ := existsUnique_add_zsmul_mem_Ico zero_lt_one 0 (k • a.den • x - 1)
    refine ⟨mkRat m (k * a.den), ?_, mkRat (k * a.num - m) (k * a.den), ?_, ?_⟩
    · rw [mkRat_mem_ratLt hka0, ← smul_smul]
      simpa using hm2
    · have hk' : 1 + (k • a.num • 1 - k • a.den • y) <= k • a.den • x - 1 := by
        rw [smul_add]; rw [smul_sub]; rw [smul_add]; rw [le_sub_iff_add_le]; rw [← sub_le_iff_le_add] at hk
        rw [le_sub_iff_add_le]
        convert! hk using 1
        abel
      have : k • a.num • 1 - k • a.den • y < m • 1 :=
        lt_of_lt_of_le (lt_add_of_pos_left _ zero_lt_one) (by simpa using hk'.trans hm1)
      rw [mkRat_mem_ratLt hka0]; rw [sub_smul]; rw [sub_lt_comm]; rw [← smul_smul]; rw [← smul_smul]; rw [natCast_zsmul]
      exact this
    · rw [Rat.mkRat_add_mkRat_of_den _ _ hka0]
      rw [add_sub_cancel]; rw [Rat.mkRat_mul_left hk0]; rw [Rat.mkRat_num_den']
  · -- `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y` → `u + v ∈ ratLt 1 (x + y)`
    intro ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    rw [Set.mem_ofPred_eq] at hu hv ⊢
    exact num_smul_one_lt_den_smul_add hu hv

/--
theorem `ratLt'_bddAbove` / 定理 `ratLt'_bddAbove`

English:
theorem ratLt'_bddAbove
  given: (x : M)
  statement: BddAbove (ratLt' x)
  proof: Monotone.map_bddAbove Rat.cast_mono ratLt_bddAbove x

中文:
定理 ratLt'_bddAbove
  条件: (x : M)
  结论: BddAbove (ratLt' x)
  证明: Monotone.map_bddAbove Rat.cast_mono ratLt_bddAbove x
-/
theorem ratLt'_bddAbove (x : M) : BddAbove (ratLt' x) :=
Monotone.map_bddAbove Rat.cast_mono ratLt_bddAbove x

/--
theorem `ratLt'_nonempty` / 定理 `ratLt'_nonempty`

English:
theorem ratLt'_nonempty
  given: (x : M)
  statement: (ratLt' x).Nonempty
  proof: Set.image_nonempty.mpr (ratLt_nonempty x)

中文:
定理 ratLt'_nonempty
  条件: (x : M)
  结论: (ratLt' x).Nonempty
  证明: Set.image_nonempty.mpr (ratLt_nonempty x)
-/
theorem ratLt'_nonempty (x : M) : (ratLt' x).Nonempty := Set.image_nonempty.mpr (ratLt_nonempty x)

open scoped Pointwise in
/--
theorem `ratLt'_add` / 定理 `ratLt'_add`

English:
theorem ratLt'_add
  given: (x y : M)
  statement: ratLt' (x + y) = ratLt' x + ratLt' y
  proof: by
  rw [ratLt']; rw [ratLt_add]; rw [Set.image_add]

中文:
定理 ratLt'_add
  条件: (x y : M)
  结论: ratLt' (x + y) = ratLt' x + ratLt' y
  证明: by
  rw [ratLt']; rw [ratLt_add]; rw [Set.image_add]
-/
theorem ratLt'_add (x y : M) : ratLt' (x + y) = ratLt' x + ratLt' y := by
  rw [ratLt']; rw [ratLt_add]; rw [Set.image_add]

variable (M) in
/--
theorem `embedRealFun_zero` / 定理 `embedRealFun_zero`

English:
theorem embedRealFun_zero
  statement: embedRealFun (0 : M) = 0
  proof: by
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 0)
    intro x
    unfold ratLt' ratLt
    suffices forall (y : Rat), y.num • (1 : M) < 0 -> y = x -> x <= 0 by simpa using this
    intro y hy hyx
    rw [← hyx]; rw [Rat.cast_nonpos]; rw [← Rat.num_nonpos]
    exact (neg_of_smul_neg_right 

中文:
定理 embedRealFun_zero
  结论: embed实数Fun (0 : M) = 0
  证明: by
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 0)
    intro x
    unfold ratLt' ratLt
    suffices forall (y : Rat), y.num • (1 : M) < 0 -> y = x -> x <= 0 by simpa using this
    intro y hy hyx
    rw [← hyx]; rw [Rat.cast_nonpos]; rw [← Rat.num_nonpos]
    exact (neg_of_smul_neg_right 

Depends on / 依赖: Rat.cast_nonpos, Rat.num_nonpos, _bddAbove, _nonempty, cast_nonpos, csSup_le, le_antisymm, le_csSup_iff, mem_upperBounds, neg_of_smul_neg_right, num_nonpos, y.num, zero_le_one
-/
theorem embedRealFun_zero : embedRealFun (0 : M) = 0 := by
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 0)
    intro x
    unfold ratLt' ratLt
    suffices forall (y : Rat), y.num • (1 : M) < 0 -> y = x -> x <= 0 by simpa using this
    intro y hy hyx
    rw [← hyx]; rw [Rat.cast_nonpos]; rw [← Rat.num_nonpos]
    exact (neg_of_smul_neg_right hy zero_le_one).le
  · rw [le_csSup_iff (ratLt'_bddAbove (0 : M)) (ratLt'_nonempty 0)]
    intro x
    rw [mem_upperBounds]
    suffices (forall (y : Rat), y.num • (1 : M) < 0 -> y <= x) -> 0 <= x by simpa using this
    intro h
    have h' (y : Rat) (hy : y < 0) : y <= x := by
exact h _ (smul_neg_iff_of_neg_left (by simpa using hy)).mpr zero_lt_one
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, by simpa using hy, hxy⟩

/--
theorem `embedRealFun_add` / 定理 `embedRealFun_add`

English:
theorem embedRealFun_add
  given: (x y : M)
  statement: embedRealFun (x + y) = embedRealFun x + embedRealFun y
  proof: by
  rw [embedRealFun]; rw [ratLt'_add]; rw [csSup_add (ratLt'_nonempty x) (ratLt'_bddAbove x)
    (ratLt'_nonempty y) (ratLt'_bddAbove y)]

中文:
定理 embedRealFun_add
  条件: (x y : M)
  结论: embed实数Fun (x + y) = embed实数Fun x + embed实数Fun y
  证明: by
  rw [embedRealFun]; rw [ratLt'_add]; rw [csSup_add (ratLt'_nonempty x) (ratLt'_bddAbove x)
    (ratLt'_nonempty y) (ratLt'_bddAbove y)]

Depends on / 依赖: _add, _bddAbove, _nonempty, csSup_add, embedRealFun
-/
theorem embedRealFun_add (x y : M) : embedRealFun (x + y) = embedRealFun x + embedRealFun y := by
  rw [embedRealFun]; rw [ratLt'_add]; rw [csSup_add (ratLt'_nonempty x) (ratLt'_bddAbove x)
    (ratLt'_nonempty y) (ratLt'_bddAbove y)]

variable (M) in
/--
theorem `embedRealFun_strictMono` / 定理 `embedRealFun_strictMono`

English:
theorem embedRealFun_strictMono
  statement: StrictMono (embedRealFun (M := M))
  proof: by
  intro x y h
  have hyz : 0 < y - x := sub_pos.mpr h
  have hy : y = y - x + x := (sub_add_cancel y x).symm
  apply lt_of_sub_pos
  rw [hy]; rw [embedRealFun_add]; rw [add_sub_cancel_right]
  obtain ⟨n, hn⟩ := Archimedean.arch 1 hyz
  have : (Rat.mk' 1 (n + 1) (by simp) (by simp) : Real) in ratL

中文:
定理 embedRealFun_strictMono
  结论: StrictMono (embed实数Fun (M := M))
  证明: by
  intro x y h
  have hyz : 0 < y - x := sub_pos.mpr h
  have hy : y = y - x + x := (sub_add_cancel y x).symm
  apply lt_of_sub_pos
  rw [hy]; rw [embedRealFun_add]; rw [add_sub_cancel_right]
  obtain ⟨n, hn⟩ := Archimedean.arch 1 hyz
  have : (Rat.mk' 1 (n + 1) (by simp) (by simp) : Real) in ratL

Depends on / 依赖: Archimedean, Archimedean.arch, Rat.mk, Rat.num_pos, _bddAbove, add_sub_cancel_right, embedRealFun_add, hn.trans_lt, lt_csSup_of_lt, lt_of_sub_pos, nsmul_lt_nsmul_left, num_pos, sub_add_cancel, sub_pos, sub_pos.mpr, trans_lt
-/
theorem embedRealFun_strictMono : StrictMono (embedRealFun (M := M)) := by
  intro x y h
  have hyz : 0 < y - x := sub_pos.mpr h
  have hy : y = y - x + x := (sub_add_cancel y x).symm
  apply lt_of_sub_pos
  rw [hy]; rw [embedRealFun_add]; rw [add_sub_cancel_right]
  obtain ⟨n, hn⟩ := Archimedean.arch 1 hyz
  have : (Rat.mk' 1 (n + 1) (by simp) (by simp) : Real) in ratLt' (y - x) := by
simpa using hn.trans_lt nsmul_lt_nsmul_left hyz (show n < n + 1 by simp)
  exact lt_csSup_of_lt (ratLt'_bddAbove (y - x)) this (by simp [← Rat.num_pos])

variable (M) in
/-- The bundled `M →+o ℝ` for archimedean `M` that preserves `1`. -/
noncomputable
/--
Definition of `embedReal` / `embedReal` 的定义

English:
definition embedReal
  signature: : M ->+o Real where
  body: embedRealFun
  map_zero' := embedRealFun_zero M
  map_add' := embedRealFun_add
  monotone' := (embedRealFun_strictMono M).monotone

中文:
定义 embedReal
  签名: : M ->+o 实数 where
  定义体: embedRealFun
  map_zero' := embedRealFun_zero M
  map_add' := embedRealFun_add
  monotone' := (embedRealFun_strictMono M).monotone

Depends on / 依赖: embedRealFun
-/
def embedReal : M ->+o Real where
  toFun := embedRealFun
  map_zero' := embedRealFun_zero M
  map_add' := embedRealFun_add
  monotone' := (embedRealFun_strictMono M).monotone

/--
theorem `embedReal_apply` / 定理 `embedReal_apply`

English:
theorem embedReal_apply
  given: (a : M)
  statement: embedReal M a = embedRealFun a
  proof: by rfl

中文:
定理 embedReal_apply
  条件: (a : M)
  结论: embed实数 M a = embed实数Fun a
  证明: by rfl
-/
theorem embedReal_apply (a : M) : embedReal M a = embedRealFun a := by rfl

variable (M) in
/--
theorem `embedReal_injective` / 定理 `embedReal_injective`

English:
theorem embedReal_injective
  statement: Function.Injective (embedReal M)
  proof: (embedRealFun_strictMono M).injective

@[simp]

中文:
定理 embedReal_injective
  结论: Function.Injective (embed实数 M)
  证明: (embedRealFun_strictMono M).injective

@[simp]

Depends on / 依赖: embedRealFun_strictMono, injective
-/
theorem embedReal_injective : Function.Injective (embedReal M) :=
  (embedRealFun_strictMono M).injective

@[simp]
/--
theorem `embedReal_one` / 定理 `embedReal_one`

English:
theorem embedReal_one
  statement: (embedReal M) 1 = 1
  proof: by
  rw [embedReal_apply]
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 1)
    suffices forall (x : Rat), x.num • (1 : M) < (x.den : Int) • (1 : M) -> (x : Real) <= 1 by simpa using this
    intro x hx
    suffices x <= 1 by norm_cast
    simpa [Rat.le_iff] using ((smul_lt_smul_iff_of_pos_

中文:
定理 embedReal_one
  结论: (embed实数 M) 1 = 1
  证明: by
  rw [embedReal_apply]
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 1)
    suffices forall (x : Rat), x.num • (1 : M) < (x.den : Int) • (1 : M) -> (x : Real) <= 1 by simpa using this
    intro x hx
    suffices x <= 1 by norm_cast
    simpa [Rat.le_iff] using ((smul_lt_smul_iff_of_pos_

Depends on / 依赖: Rat.le_iff, _bddAbove, _nonempty, csSup_le, embedReal_apply, le_antisymm, le_csSup_iff, le_iff, mem_upperBounds, simp_rw, smul_lt_smul_iff_of_pos_right, x.den, x.num, y.den, y.num, zero_lt_one
-/
theorem embedReal_one : (embedReal M) 1 = 1 := by
  rw [embedReal_apply]
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 1)
    suffices forall (x : Rat), x.num • (1 : M) < (x.den : Int) • (1 : M) -> (x : Real) <= 1 by simpa using this
    intro x hx
    suffices x <= 1 by norm_cast
    simpa [Rat.le_iff] using ((smul_lt_smul_iff_of_pos_right zero_lt_one).mp hx).le
  · rw [le_csSup_iff (ratLt'_bddAbove (1 : M)) (ratLt'_nonempty 1)]
    simp_rw [mem_upperBounds]
    suffices forall (x : Real), (forall (y : Rat), y.num • (1 : M) < (y.den : Int) • 1 -> y <= x) -> 1 <= x by
      simpa using this
    intro x h
    have h' (y : Rat) (hy : y < 1) : y <= x :=
      h _ ((smul_lt_smul_iff_of_pos_right zero_lt_one).mpr (by simpa using (Rat.lt_iff _ _).mp hy))
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, (by norm_cast at hy), hxy⟩

omit [One M] [ZeroLEOneClass M] [NeZero (1 : M)] in
variable (M) in
/--
theorem `exists_orderAddMonoidHom_real_injective` / 定理 `exists_orderAddMonoidHom_real_injective`

English:
theorem exists_orderAddMonoidHom_real_injective
  proof: by
  cases subsingleton_or_nontrivial M
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · obtain ⟨a, ha⟩ := exists_ne (0 : M)
    let one : One M := ⟨|a|⟩
    have : ZeroLEOneClass M := ⟨abs_nonneg a⟩
    have : NeZero (1 : M) := ⟨abs_ne_zero.mpr ha⟩
    exact ⟨embedReal M, embedReal_injective

中文:
定理 exists_orderAddMonoidHom_real_injective
  证明: by
  cases subsingleton_or_nontrivial M
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · obtain ⟨a, ha⟩ := exists_ne (0 : M)
    let one : One M := ⟨|a|⟩
    have : ZeroLEOneClass M := ⟨abs_nonneg a⟩
    have : NeZero (1 : M) := ⟨abs_ne_zero.mpr ha⟩
    exact ⟨embedReal M, embedReal_injective

Depends on / 依赖: Function, Function.injective_of_subsingleton, NeZero, ZeroLEOneClass, abs_ne_zero, abs_ne_zero.mpr, abs_nonneg, embedReal, embedReal_injective, exists_ne, injective_of_subsingleton, subsingleton_or_nontrivial
-/
theorem exists_orderAddMonoidHom_real_injective :
    exists f : M ->+o Real, Function.Injective f := by
  cases subsingleton_or_nontrivial M
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · obtain ⟨a, ha⟩ := exists_ne (0 : M)
    let one : One M := ⟨|a|⟩
    have : ZeroLEOneClass M := ⟨abs_nonneg a⟩
    have : NeZero (1 : M) := ⟨abs_ne_zero.mpr ha⟩
    exact ⟨embedReal M, embedReal_injective M⟩

end Archimedean
