/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.PNat.Notation
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `IsPeriodicPt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `ptsOfPeriod f n` : the set `{x | IsPeriodicPt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodicPts f` : the set of all periodic points of `f`.
* `minimalPeriod f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.
* `orbit f x`: the cycle `[x, f x, f (f x), ...]` for a periodic point.
* `MulAction.period g x` : the minimal period of a point `x` under the multiplicative action of `g`;
  an equivalent `AddAction.period g x` is defined for additive actions.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : IsPeriodicPt f n x` including
arithmetic operations on `n` and `h.map (hg : SemiconjBy g f f')`. We also prove that `f`
is bijective on each set `ptsOfPeriod f n` and on `periodicPts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimalPeriod f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/

@[expose] public section

assert_not_exists MonoidWithZero


open Set

namespace Function

open Function (Commute)

variable {α : Type*} {β : Type*} {f fa : α -> α} {fb : β -> β} {x y : α} {m n : Nat}

/--
Definition of `IsPeriodicPt` / `IsPeriodicPt` 的定义

English:
definition IsPeriodicPt
  signature: (f : α -> α) (n : Nat) (x : α)
  body: IsFixedPt f^[n] x

中文:
定义 IsPeriodicPt
  签名: (f : α -> α) (n : 自然数) (x : α)
  定义体: IsFixedPt f^[n] x

Depends on / 依赖: IsFixedPt
-/
def IsPeriodicPt (f : α -> α) (n : Nat) (x : α) :=
  IsFixedPt f^[n] x

/--
theorem `IsFixedPt.isPeriodicPt` / 定理 `IsFixedPt.isPeriodicPt`

English:
theorem IsFixedPt.isPeriodicPt
  given: (hf : IsFixedPt f x) (n : Nat)
  statement: IsPeriodicPt f n x
  proof: hf.iterate n

中文:
定理 IsFixedPt.isPeriodicPt
  条件: (hf : IsFixedPt f x) (n : 自然数)
  结论: IsPeriodicPt f n x
  证明: hf.iterate n

Depends on / 依赖: hf.iterate, iterate
-/
theorem IsFixedPt.isPeriodicPt (hf : IsFixedPt f x) (n : Nat) : IsPeriodicPt f n x :=
  hf.iterate n

/--
theorem `is_periodic_id` / 定理 `is_periodic_id`

English:
theorem is_periodic_id
  given: (n : Nat) (x : α)
  statement: IsPeriodicPt id n x
  proof: (isFixedPt_id x).isPeriodicPt n

中文:
定理 is_periodic_id
  条件: (n : 自然数) (x : α)
  结论: IsPeriodicPt id n x
  证明: (isFixedPt_id x).isPeriodicPt n

Depends on / 依赖: isFixedPt_id, isPeriodicPt
-/
theorem is_periodic_id (n : Nat) (x : α) : IsPeriodicPt id n x :=
  (isFixedPt_id x).isPeriodicPt n

/--
theorem `isPeriodicPt_zero` / 定理 `isPeriodicPt_zero`

English:
theorem isPeriodicPt_zero
  given: (f : α -> α) (x : α)
  statement: IsPeriodicPt f 0 x
  proof: isFixedPt_id x

中文:
定理 isPeriodicPt_zero
  条件: (f : α -> α) (x : α)
  结论: IsPeriodicPt f 0 x
  证明: isFixedPt_id x

Depends on / 依赖: isFixedPt_id
-/
theorem isPeriodicPt_zero (f : α -> α) (x : α) : IsPeriodicPt f 0 x :=
  isFixedPt_id x

namespace IsPeriodicPt

@[nontriviality]
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton α] (f : α -> α) (n : Nat) (x : α)
  statement: IsPeriodicPt f n x
  proof: IsFixedPt.of_subsingleton _ _

中文:
定理 of_subsingleton
  条件: [子单例 α] (f : α -> α) (n : 自然数) (x : α)
  结论: IsPeriodicPt f n x
  证明: IsFixedPt.of_subsingleton _ _

Depends on / 依赖: IsFixedPt, IsFixedPt.of_subsingleton, of_subsingleton
-/
theorem of_subsingleton [Subsingleton α] (f : α -> α) (n : Nat) (x : α) : IsPeriodicPt f n x :=
  IsFixedPt.of_subsingleton _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] {f
  body: IsFixedPt.decidable

中文:
实例 [DecidableEq
  签名: α] {f
  定义体: IsFixedPt.decidable

Depends on / 依赖: IsFixedPt, IsFixedPt.decidable, decidable
-/
instance [DecidableEq α] {f : α -> α} {n : Nat} {x : α} : Decidable (IsPeriodicPt f n x) :=
  IsFixedPt.decidable

/--
theorem `isFixedPt` / 定理 `isFixedPt`

English:
theorem isFixedPt
  given: (hf : IsPeriodicPt f n x)
  statement: IsFixedPt f^[n] x
  proof: hf

中文:
定理 isFixedPt
  条件: (hf : IsPeriodicPt f n x)
  结论: IsFixedPt f^[n] x
  证明: hf
-/
protected theorem isFixedPt (hf : IsPeriodicPt f n x) : IsFixedPt f^[n] x :=
  hf

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (hx : IsPeriodicPt fa n x) {g : α -> β} (hg : Semiconj g fa fb)
  proof: IsFixedPt.map hx (hg.iterate_right n)

中文:
定理 map
  条件: (hx : IsPeriodicPt fa n x) {g : α -> β} (hg : Semiconj g fa fb)
  证明: IsFixedPt.map hx (hg.iterate_right n)
-/
protected theorem map (hx : IsPeriodicPt fa n x) {g : α -> β} (hg : Semiconj g fa fb) :
    IsPeriodicPt fb n (g x) :=
  IsFixedPt.map hx (hg.iterate_right n)

/--
theorem `apply_iterate` / 定理 `apply_iterate`

English:
theorem apply_iterate
  given: (hx : IsPeriodicPt f n x) (m : Nat)
  statement: IsPeriodicPt f n (f^[m] x)
  proof: hx.map Commute.iterate_self f m

中文:
定理 apply_iterate
  条件: (hx : IsPeriodicPt f n x) (m : 自然数)
  结论: IsPeriodicPt f n (f^[m] x)
  证明: hx.map Commute.iterate_self f m

Depends on / 依赖: Commute, Commute.iterate_self, hx.map, iterate_self
-/
theorem apply_iterate (hx : IsPeriodicPt f n x) (m : Nat) : IsPeriodicPt f n (f^[m] x) :=
hx.map Commute.iterate_self f m

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: (hx : IsPeriodicPt f n x)
  statement: IsPeriodicPt f n (f x)
  proof: hx.apply_iterate 1

中文:
定理 apply
  条件: (hx : IsPeriodicPt f n x)
  结论: IsPeriodicPt f n (f x)
  证明: hx.apply_iterate 1
-/
protected theorem apply (hx : IsPeriodicPt f n x) : IsPeriodicPt f n (f x) :=
  hx.apply_iterate 1

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x)
  proof: by
  rw [IsPeriodicPt]; rw [iterate_add]
  exact hn.comp hm

中文:
定理 add
  条件: (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x)
  证明: by
  rw [IsPeriodicPt]; rw [iterate_add]
  exact hn.comp hm
-/
protected theorem add (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x) :
    IsPeriodicPt f (n + m) x := by
  rw [IsPeriodicPt]; rw [iterate_add]
  exact hn.comp hm

/--
theorem `left_of_add` / 定理 `left_of_add`

English:
theorem left_of_add
  given: (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x)
  proof: by
  rw [IsPeriodicPt]; rw [iterate_add] at hn
  exact hn.left_of_comp hm

中文:
定理 left_of_add
  条件: (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x)
  证明: by
  rw [IsPeriodicPt]; rw [iterate_add] at hn
  exact hn.left_of_comp hm

Depends on / 依赖: IsPeriodicPt, hn.left_of_comp, iterate_add, left_of_comp
-/
theorem left_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x) :
    IsPeriodicPt f n x := by
  rw [IsPeriodicPt]; rw [iterate_add] at hn
  exact hn.left_of_comp hm

/--
theorem `right_of_add` / 定理 `right_of_add`

English:
theorem right_of_add
  given: (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x)
  proof: by
  rw [add_comm] at hn
  exact hn.left_of_add hm

中文:
定理 right_of_add
  条件: (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x)
  证明: by
  rw [add_comm] at hn
  exact hn.left_of_add hm

Depends on / 依赖: add_comm, hn.left_of_add, left_of_add
-/
theorem right_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x) :
    IsPeriodicPt f m x := by
  rw [add_comm] at hn
  exact hn.left_of_add hm

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x)
  proof: by
  rcases le_total n m with h | h
  · refine left_of_add ?_ hn
    rwa [tsub_add_cancel_of_le h]
  · rw [tsub_eq_zero_iff_le.mpr h]
    apply isPeriodicPt_zero

中文:
定理 sub
  条件: (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x)
  证明: by
  rcases le_total n m with h | h
  · refine left_of_add ?_ hn
    rwa [tsub_add_cancel_of_le h]
  · rw [tsub_eq_zero_iff_le.mpr h]
    apply isPeriodicPt_zero
-/
protected theorem sub (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m - n) x := by
  rcases le_total n m with h | h
  · refine left_of_add ?_ hn
    rwa [tsub_add_cancel_of_le h]
  · rw [tsub_eq_zero_iff_le.mpr h]
    apply isPeriodicPt_zero

/--
theorem `mul_const` / 定理 `mul_const`

English:
theorem mul_const
  given: (hm : IsPeriodicPt f m x) (n : Nat)
  statement: IsPeriodicPt f (m * n) x
  proof: by
  simp only [IsPeriodicPt, iterate_mul, hm.isFixedPt.iterate n]

中文:
定理 mul_const
  条件: (hm : IsPeriodicPt f m x) (n : 自然数)
  结论: IsPeriodicPt f (m * n) x
  证明: by
  simp only [IsPeriodicPt, iterate_mul, hm.isFixedPt.iterate n]
-/
protected theorem mul_const (hm : IsPeriodicPt f m x) (n : Nat) : IsPeriodicPt f (m * n) x := by
  simp only [IsPeriodicPt, iterate_mul, hm.isFixedPt.iterate n]

/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: (hm : IsPeriodicPt f m x) (n : Nat)
  statement: IsPeriodicPt f (n * m) x
  proof: by
  simp only [mul_comm n, hm.mul_const n]

中文:
定理 const_mul
  条件: (hm : IsPeriodicPt f m x) (n : 自然数)
  结论: IsPeriodicPt f (n * m) x
  证明: by
  simp only [mul_comm n, hm.mul_const n]
-/
protected theorem const_mul (hm : IsPeriodicPt f m x) (n : Nat) : IsPeriodicPt f (n * m) x := by
  simp only [mul_comm n, hm.mul_const n]

/--
theorem `trans_dvd` / 定理 `trans_dvd`

English:
theorem trans_dvd
  given: (hm : IsPeriodicPt f m x) {n : Nat} (hn : m ∣ n)
  statement: IsPeriodicPt f n x
  proof: let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k

中文:
定理 trans_dvd
  条件: (hm : IsPeriodicPt f m x) {n : 自然数} (hn : m ∣ n)
  结论: IsPeriodicPt f n x
  证明: let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k

Depends on / 依赖: hk.symm, hm.mul_const, mul_const
-/
theorem trans_dvd (hm : IsPeriodicPt f m x) {n : Nat} (hn : m ∣ n) : IsPeriodicPt f n x :=
  let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: (hf : IsPeriodicPt f n x) (m : Nat)
  statement: IsPeriodicPt f^[m] n x
  proof: by
  rw [IsPeriodicPt]; rw [← iterate_mul]; rw [mul_comm]; rw [iterate_mul]
  exact hf.isFixedPt.iterate m

中文:
定理 iterate
  条件: (hf : IsPeriodicPt f n x) (m : 自然数)
  结论: IsPeriodicPt f^[m] n x
  证明: by
  rw [IsPeriodicPt]; rw [← iterate_mul]; rw [mul_comm]; rw [iterate_mul]
  exact hf.isFixedPt.iterate m
-/
protected theorem iterate (hf : IsPeriodicPt f n x) (m : Nat) : IsPeriodicPt f^[m] n x := by
  rw [IsPeriodicPt]; rw [← iterate_mul]; rw [mul_comm]; rw [iterate_mul]
  exact hf.isFixedPt.iterate m

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x)
  proof: by
  rw [IsPeriodicPt]; rw [hco.comp_iterate]
  exact IsFixedPt.comp hf hg

中文:
定理 comp
  条件: {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x)
  证明: by
  rw [IsPeriodicPt]; rw [hco.comp_iterate]
  exact IsFixedPt.comp hf hg

Depends on / 依赖: IsFixedPt, IsFixedPt.comp, IsPeriodicPt, comp_iterate, hco.comp_iterate
-/
theorem comp {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) :
    IsPeriodicPt (f ∘ g) n x := by
  rw [IsPeriodicPt]; rw [hco.comp_iterate]
  exact IsFixedPt.comp hf hg

/--
theorem `comp_lcm` / 定理 `comp_lcm`

English:
theorem comp_lcm
  statement: {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f m x)
  proof: (hf.trans_dvd <| Nat.dvd_lcm_left _ _).comp hco (hg.trans_dvd <| Nat.dvd_lcm_right _ _)

中文:
定理 comp_lcm
  结论: {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f m x)
  证明: (hf.trans_dvd <| Nat.dvd_lcm_left _ _).comp hco (hg.trans_dvd <| Nat.dvd_lcm_right _ _)

Depends on / 依赖: Nat.dvd_lcm_left, Nat.dvd_lcm_right, dvd_lcm_left, dvd_lcm_right, hf.trans_dvd, hg.trans_dvd, trans_dvd
-/
theorem comp_lcm {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f m x)
    (hg : IsPeriodicPt g n x) : IsPeriodicPt (f ∘ g) (Nat.lcm m n) x :=
  (hf.trans_dvd <| Nat.dvd_lcm_left _ _).comp hco (hg.trans_dvd <| Nat.dvd_lcm_right _ _)

/--
theorem `left_of_comp` / 定理 `left_of_comp`

English:
theorem left_of_comp
  statement: {g : α -> α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) n x)
  proof: by
  rw [IsPeriodicPt]; rw [hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg

中文:
定理 left_of_comp
  结论: {g : α -> α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) n x)
  证明: by
  rw [IsPeriodicPt]; rw [hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg

Depends on / 依赖: IsPeriodicPt, comp_iterate, hco.comp_iterate, hfg.left_of_comp, left_of_comp
-/
theorem left_of_comp {g : α -> α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) n x)
    (hg : IsPeriodicPt g n x) : IsPeriodicPt f n x := by
  rw [IsPeriodicPt]; rw [hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg

/--
theorem `iterate_mod_apply` / 定理 `iterate_mod_apply`

English:
theorem iterate_mod_apply
  given: (h : IsPeriodicPt f n x) (m : Nat)
  statement: f^[m % n] x = f^[m] x
  proof: by
  conv_rhs => rw [← Nat.mod_add_div m n, iterate_add_apply, (h.mul_const _).eq]

中文:
定理 iterate_mod_apply
  条件: (h : IsPeriodicPt f n x) (m : 自然数)
  结论: f^[m % n] x = f^[m] x
  证明: by
  conv_rhs => rw [← Nat.mod_add_div m n, iterate_add_apply, (h.mul_const _).eq]

Depends on / 依赖: Nat.mod_add_div, conv_rhs, h.mul_const, iterate_add_apply, mod_add_div, mul_const
-/
theorem iterate_mod_apply (h : IsPeriodicPt f n x) (m : Nat) : f^[m % n] x = f^[m] x := by
  conv_rhs => rw [← Nat.mod_add_div m n, iterate_add_apply, (h.mul_const _).eq]

/--
theorem `mod` / 定理 `mod`

English:
theorem mod
  given: (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x)
  proof: (hn.iterate_mod_apply m).trans hm

中文:
定理 mod
  条件: (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x)
  证明: (hn.iterate_mod_apply m).trans hm
-/
protected theorem mod (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m % n) x :=
  (hn.iterate_mod_apply m).trans hm

/--
theorem `gcd` / 定理 `gcd`

English:
theorem gcd
  given: (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x)
  proof: by
  revert hm hn
  refine Nat.gcd.induction m n (fun n _ hn => ?_) fun m n _ ih hm hn => ?_
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact ih (hn.mod hm) hm

中文:
定理 最大公约数
  条件: (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x)
  证明: by
  revert hm hn
  refine Nat.gcd.induction m n (fun n _ hn => ?_) fun m n _ ih hm hn => ?_
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact ih (hn.mod hm) hm
-/
protected theorem gcd (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m.gcd n) x := by
  revert hm hn
  refine Nat.gcd.induction m n (fun n _ hn => ?_) fun m n _ ih hm hn => ?_
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact ih (hn.mod hm) hm

/--
theorem `eq_of_apply_eq_same` / 定理 `eq_of_apply_eq_same`

English:
theorem eq_of_apply_eq_same
  statement: (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n)
  proof: by
  rw [← hx.eq]; rw [← hy.eq]; rw [← iterate_pred_comp_of_pos f hn]; rw [comp_apply]; rw [comp_apply]; rw [h]

中文:
定理 eq_of_apply_eq_same
  结论: (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n)
  证明: by
  rw [← hx.eq]; rw [← hy.eq]; rw [← iterate_pred_comp_of_pos f hn]; rw [comp_apply]; rw [comp_apply]; rw [h]

Depends on / 依赖: comp_apply, hx.eq, hy.eq, iterate_pred_comp_of_pos
-/
theorem eq_of_apply_eq_same (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n)
    (h : f x = f y) : x = y := by
  rw [← hx.eq]; rw [← hy.eq]; rw [← iterate_pred_comp_of_pos f hn]; rw [comp_apply]; rw [comp_apply]; rw [h]

/--
theorem `eq_of_apply_eq` / 定理 `eq_of_apply_eq`

English:
theorem eq_of_apply_eq
  statement: (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0 < m) (hn : 0 < n)
  proof: (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (Nat.mul_pos hm hn) h

中文:
定理 eq_of_apply_eq
  结论: (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0 < m) (hn : 0 < n)
  证明: (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (Nat.mul_pos hm hn) h

Depends on / 依赖: Nat.mul_pos, const_mul, eq_of_apply_eq_same, hx.mul_const, hy.const_mul, mul_const, mul_pos
-/
theorem eq_of_apply_eq (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0 < m) (hn : 0 < n)
    (h : f x = f y) : x = y :=
  (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (Nat.mul_pos hm hn) h

end IsPeriodicPt

/--
Definition of `ptsOfPeriod` / `ptsOfPeriod` 的定义

English:
definition ptsOfPeriod
  signature: (f : α -> α) (n : Nat)
  body: { x : α | IsPeriodicPt f n x }

@[simp]

中文:
定义 ptsOfPeriod
  签名: (f : α -> α) (n : 自然数)
  定义体: { x : α | IsPeriodicPt f n x }

@[simp]

Depends on / 依赖: IsPeriodicPt
-/
def ptsOfPeriod (f : α -> α) (n : Nat) : Set α :=
  { x : α | IsPeriodicPt f n x }

@[simp]
/--
theorem `mem_ptsOfPeriod` / 定理 `mem_ptsOfPeriod`

English:
theorem mem_ptsOfPeriod
  statement: x in ptsOfPeriod f n ↔ IsPeriodicPt f n x
  proof: Iff.rfl

中文:
定理 mem_ptsOfPeriod
  结论: x in ptsOfPeriod f n ↔ IsPeriodicPt f n x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ptsOfPeriod : x in ptsOfPeriod f n ↔ IsPeriodicPt f n x :=
  Iff.rfl

/--
theorem `Semiconj.mapsTo_ptsOfPeriod` / 定理 `Semiconj.mapsTo_ptsOfPeriod`

English:
theorem Semiconj.mapsTo_ptsOfPeriod
  given: {g : α -> β} (h : Semiconj g fa fb) (n : Nat)
  proof: (h.iterate_right n).mapsTo_fixedPoints

中文:
定理 Semiconj.mapsTo_ptsOfPeriod
  条件: {g : α -> β} (h : Semiconj g fa fb) (n : 自然数)
  证明: (h.iterate_right n).mapsTo_fixedPoints

Depends on / 依赖: h.iterate_right, iterate_right, mapsTo_fixedPoints
-/
theorem Semiconj.mapsTo_ptsOfPeriod {g : α -> β} (h : Semiconj g fa fb) (n : Nat) :
    MapsTo g (ptsOfPeriod fa n) (ptsOfPeriod fb n) :=
  (h.iterate_right n).mapsTo_fixedPoints

/--
theorem `bijOn_ptsOfPeriod` / 定理 `bijOn_ptsOfPeriod`

English:
theorem bijOn_ptsOfPeriod
  given: (f : α -> α) {n : Nat} (hn : 0 < n)
  proof: ⟨(Commute.refl f).mapsTo_ptsOfPeriod n, fun _ hx _ hy hxy => hx.eq_of_apply_eq_same hy hn hxy,
    fun x hx =>
    ⟨f^[n.pred] x, hx.apply_iterate _, by
      rw [← comp_apply (f := f)]; rw [comp_iterate_pred_of_pos f hn]; rw [hx.eq]⟩⟩

中文:
定理 bijOn_ptsOfPeriod
  条件: (f : α -> α) {n : 自然数} (hn : 0 < n)
  证明: ⟨(Commute.refl f).mapsTo_ptsOfPeriod n, fun _ hx _ hy hxy => hx.eq_of_apply_eq_same hy hn hxy,
    fun x hx =>
    ⟨f^[n.pred] x, hx.apply_iterate _, by
      rw [← comp_apply (f := f)]; rw [comp_iterate_pred_of_pos f hn]; rw [hx.eq]⟩⟩

Depends on / 依赖: Commute, Commute.refl, apply_iterate, comp_apply, comp_iterate_pred_of_pos, eq_of_apply_eq_same, hx.apply_iterate, hx.eq, hx.eq_of_apply_eq_same, mapsTo_ptsOfPeriod, n.pred
-/
theorem bijOn_ptsOfPeriod (f : α -> α) {n : Nat} (hn : 0 < n) :
    BijOn f (ptsOfPeriod f n) (ptsOfPeriod f n) :=
  ⟨(Commute.refl f).mapsTo_ptsOfPeriod n, fun _ hx _ hy hxy => hx.eq_of_apply_eq_same hy hn hxy,
    fun x hx =>
    ⟨f^[n.pred] x, hx.apply_iterate _, by
      rw [← comp_apply (f := f)]; rw [comp_iterate_pred_of_pos f hn]; rw [hx.eq]⟩⟩

/--
Definition of `periodicPts` / `periodicPts` 的定义

English:
definition periodicPts
  signature: (f : α -> α)
  body: { x : α | exists n > 0, IsPeriodicPt f n x }

中文:
定义 periodicPts
  签名: (f : α -> α)
  定义体: { x : α | exists n > 0, IsPeriodicPt f n x }

Depends on / 依赖: IsPeriodicPt
-/
def periodicPts (f : α -> α) : Set α :=
  { x : α | exists n > 0, IsPeriodicPt f n x }

/--
theorem `mk_mem_periodicPts` / 定理 `mk_mem_periodicPts`

English:
theorem mk_mem_periodicPts
  given: (hn : 0 < n) (hx : IsPeriodicPt f n x)
  statement: x in periodicPts f
  proof: ⟨n, hn, hx⟩

中文:
定理 mk_mem_periodicPts
  条件: (hn : 0 < n) (hx : IsPeriodicPt f n x)
  结论: x in periodicPts f
  证明: ⟨n, hn, hx⟩
-/
theorem mk_mem_periodicPts (hn : 0 < n) (hx : IsPeriodicPt f n x) : x in periodicPts f :=
  ⟨n, hn, hx⟩

/--
theorem `mem_periodicPts` / 定理 `mem_periodicPts`

English:
theorem mem_periodicPts
  statement: x in periodicPts f ↔ exists n > 0, IsPeriodicPt f n x
  proof: Iff.rfl

中文:
定理 mem_periodicPts
  结论: x in periodicPts f ↔ 存在 n > 0, IsPeriodicPt f n x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_periodicPts : x in periodicPts f ↔ exists n > 0, IsPeriodicPt f n x :=
  Iff.rfl

/--
theorem `periodicPts_subset_range` / 定理 `periodicPts_subset_range`

English:
theorem periodicPts_subset_range
  statement: periodicPts f subseteq range f
  proof: by
  intro x h
  rw [mem_periodicPts] at h
  rcases h with ⟨n, _, h⟩
  use f^[n - 1] x
  nth_rw 1 [← iterate_one f]
  rw [← iterate_add_apply]; rw [Nat.add_sub_cancel' (by lia)]
  exact h

中文:
定理 periodicPts_subset_range
  结论: periodicPts f subseteq range f
  证明: by
  intro x h
  rw [mem_periodicPts] at h
  rcases h with ⟨n, _, h⟩
  use f^[n - 1] x
  nth_rw 1 [← iterate_one f]
  rw [← iterate_add_apply]; rw [Nat.add_sub_cancel' (by lia)]
  exact h

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, iterate_add_apply, iterate_one, mem_periodicPts, nth_rw
-/
theorem periodicPts_subset_range : periodicPts f subseteq range f := by
  intro x h
  rw [mem_periodicPts] at h
  rcases h with ⟨n, _, h⟩
  use f^[n - 1] x
  nth_rw 1 [← iterate_one f]
  rw [← iterate_add_apply]; rw [Nat.add_sub_cancel' (by lia)]
  exact h

/--
theorem `isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate` / 定理 `isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate`

English:
theorem isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
  statement: (hx : x in periodicPts f)
  proof: by
  rcases hx with ⟨r, hr, hr'⟩
  suffices n <= (n / r + 1) * r by
    unfold IsPeriodicPt IsFixedPt
    convert! (hm.apply_iterate ((n / r + 1) * r - n)).eq <;>
      rw [← iterate_add_apply]; rw [Nat.sub_add_cancel this]; rw [iterate_mul]; rw [(hr'.iterate _).eq]
  rw [Nat.add_mul]; rw [one_mul]


中文:
定理 isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
  结论: (hx : x in periodicPts f)
  证明: by
  rcases hx with ⟨r, hr, hr'⟩
  suffices n <= (n / r + 1) * r by
    unfold IsPeriodicPt IsFixedPt
    convert! (hm.apply_iterate ((n / r + 1) * r - n)).eq <;>
      rw [← iterate_add_apply]; rw [Nat.sub_add_cancel this]; rw [iterate_mul]; rw [(hr'.iterate _).eq]
  rw [Nat.add_mul]; rw [one_mul]


Depends on / 依赖: IsFixedPt, IsPeriodicPt, Nat.add_mul, Nat.lt_div_mul_add, Nat.sub_add_cancel, add_mul, apply_iterate, convert, hm.apply_iterate, iterate, iterate_add_apply, iterate_mul, lt_div_mul_add, one_mul, sub_add_cancel
-/
theorem isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate (hx : x in periodicPts f)
    (hm : IsPeriodicPt f m (f^[n] x)) : IsPeriodicPt f m x := by
  rcases hx with ⟨r, hr, hr'⟩
  suffices n <= (n / r + 1) * r by
    unfold IsPeriodicPt IsFixedPt
    convert! (hm.apply_iterate ((n / r + 1) * r - n)).eq <;>
      rw [← iterate_add_apply]; rw [Nat.sub_add_cancel this]; rw [iterate_mul]; rw [(hr'.iterate _).eq]
  rw [Nat.add_mul]; rw [one_mul]
  exact (Nat.lt_div_mul_add hr).le

variable (f)

/--
theorem `bUnion_ptsOfPeriod` / 定理 `bUnion_ptsOfPeriod`

English:
theorem bUnion_ptsOfPeriod
  statement: ⋃ n > 0, ptsOfPeriod f n = periodicPts f
  proof: Set.ext fun x => by simp [mem_periodicPts]

中文:
定理 bUnion_ptsOfPeriod
  结论: ⋃ n > 0, ptsOfPeriod f n = periodicPts f
  证明: Set.ext fun x => by simp [mem_periodicPts]

Depends on / 依赖: Set.ext, mem_periodicPts
-/
theorem bUnion_ptsOfPeriod : ⋃ n > 0, ptsOfPeriod f n = periodicPts f :=
  Set.ext fun x => by simp [mem_periodicPts]

/--
theorem `iUnion_pnat_ptsOfPeriod` / 定理 `iUnion_pnat_ptsOfPeriod`

English:
theorem iUnion_pnat_ptsOfPeriod
  statement: ⋃ n : Nat+, ptsOfPeriod f n = periodicPts f
  proof: iSup_subtype.trans bUnion_ptsOfPeriod f

中文:
定理 iUnion_pnat_ptsOfPeriod
  结论: ⋃ n : 自然数+, ptsOfPeriod f n = periodicPts f
  证明: iSup_subtype.trans bUnion_ptsOfPeriod f

Depends on / 依赖: bUnion_ptsOfPeriod, iSup_subtype, iSup_subtype.trans
-/
theorem iUnion_pnat_ptsOfPeriod : ⋃ n : Nat+, ptsOfPeriod f n = periodicPts f :=
iSup_subtype.trans bUnion_ptsOfPeriod f

variable {f}

/--
theorem `Semiconj.mapsTo_periodicPts` / 定理 `Semiconj.mapsTo_periodicPts`

English:
theorem Semiconj.mapsTo_periodicPts
  given: {g : α -> β} (h : Semiconj g fa fb)
  proof: fun _ ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

noncomputable section

中文:
定理 Semiconj.mapsTo_periodicPts
  条件: {g : α -> β} (h : Semiconj g fa fb)
  证明: fun _ ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

noncomputable section

Depends on / 依赖: hx.map
-/
theorem Semiconj.mapsTo_periodicPts {g : α -> β} (h : Semiconj g fa fb) :
    MapsTo g (periodicPts fa) (periodicPts fb) := fun _ ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

noncomputable section

open scoped Classical in
/--
Definition of `minimalPeriod` / `minimalPeriod` 的定义

English:
definition minimalPeriod
  signature: (f : α -> α) (x : α)
  body: if h : x in periodicPts f then Nat.find h else 0

中文:
定义 minimalPeriod
  签名: (f : α -> α) (x : α)
  定义体: if h : x in periodicPts f then Nat.find h else 0

Depends on / 依赖: Nat.find, periodicPts
-/
def minimalPeriod (f : α -> α) (x : α) :=
  if h : x in periodicPts f then Nat.find h else 0

/--
theorem `isPeriodicPt_minimalPeriod` / 定理 `isPeriodicPt_minimalPeriod`

English:
theorem isPeriodicPt_minimalPeriod
  given: (f : α -> α) (x : α)
  statement: IsPeriodicPt f (minimalPeriod f x) x
  proof: by
  classical
  delta minimalPeriod
  split_ifs with hx
  · exact (Nat.find_spec hx).2
  · exact isPeriodicPt_zero f x

@[simp]

中文:
定理 isPeriodicPt_minimalPeriod
  条件: (f : α -> α) (x : α)
  结论: IsPeriodicPt f (minimalPeriod f x) x
  证明: by
  classical
  delta minimalPeriod
  split_ifs with hx
  · exact (Nat.find_spec hx).2
  · exact isPeriodicPt_zero f x

@[simp]

Depends on / 依赖: Nat.find_spec, classical, find_spec, isPeriodicPt_zero, minimalPeriod, split_ifs
-/
theorem isPeriodicPt_minimalPeriod (f : α -> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x := by
  classical
  delta minimalPeriod
  split_ifs with hx
  · exact (Nat.find_spec hx).2
  · exact isPeriodicPt_zero f x

@[simp]
/--
theorem `iterate_minimalPeriod` / 定理 `iterate_minimalPeriod`

English:
theorem iterate_minimalPeriod
  statement: f^[minimalPeriod f x] x = x
  proof: isPeriodicPt_minimalPeriod f x

@[simp]

中文:
定理 iterate_minimalPeriod
  结论: f^[minimalPeriod f x] x = x
  证明: isPeriodicPt_minimalPeriod f x

@[simp]

Depends on / 依赖: isPeriodicPt_minimalPeriod
-/
theorem iterate_minimalPeriod : f^[minimalPeriod f x] x = x :=
  isPeriodicPt_minimalPeriod f x

@[simp]
/--
theorem `iterate_add_minimalPeriod_eq` / 定理 `iterate_add_minimalPeriod_eq`

English:
theorem iterate_add_minimalPeriod_eq
  statement: f^[n + minimalPeriod f x] x = f^[n] x
  proof: by
  rw [iterate_add_apply]
  congr
  exact isPeriodicPt_minimalPeriod f x

@[simp]

中文:
定理 iterate_add_minimalPeriod_eq
  结论: f^[n + minimalPeriod f x] x = f^[n] x
  证明: by
  rw [iterate_add_apply]
  congr
  exact isPeriodicPt_minimalPeriod f x

@[simp]

Depends on / 依赖: isPeriodicPt_minimalPeriod, iterate_add_apply
-/
theorem iterate_add_minimalPeriod_eq : f^[n + minimalPeriod f x] x = f^[n] x := by
  rw [iterate_add_apply]
  congr
  exact isPeriodicPt_minimalPeriod f x

@[simp]
/--
theorem `iterate_mod_minimalPeriod_eq` / 定理 `iterate_mod_minimalPeriod_eq`

English:
theorem iterate_mod_minimalPeriod_eq
  statement: f^[n % minimalPeriod f x] x = f^[n] x
  proof: (isPeriodicPt_minimalPeriod f x).iterate_mod_apply n

中文:
定理 iterate_mod_minimalPeriod_eq
  结论: f^[n % minimalPeriod f x] x = f^[n] x
  证明: (isPeriodicPt_minimalPeriod f x).iterate_mod_apply n

Depends on / 依赖: isPeriodicPt_minimalPeriod, iterate_mod_apply
-/
theorem iterate_mod_minimalPeriod_eq : f^[n % minimalPeriod f x] x = f^[n] x :=
  (isPeriodicPt_minimalPeriod f x).iterate_mod_apply n

/--
theorem `minimalPeriod_pos_of_mem_periodicPts` / 定理 `minimalPeriod_pos_of_mem_periodicPts`

English:
theorem minimalPeriod_pos_of_mem_periodicPts
  given: (hx : x in periodicPts f)
  statement: 0 < minimalPeriod f x
  proof: by
  classical
  simp only [minimalPeriod, dif_pos hx, (Nat.find_spec hx).1.lt]

中文:
定理 minimalPeriod_pos_of_mem_periodicPts
  条件: (hx : x in periodicPts f)
  结论: 0 < minimalPeriod f x
  证明: by
  classical
  simp only [minimalPeriod, dif_pos hx, (Nat.find_spec hx).1.lt]

Depends on / 依赖: Nat.find_spec, classical, dif_pos, find_spec, minimalPeriod
-/
theorem minimalPeriod_pos_of_mem_periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x := by
  classical
  simp only [minimalPeriod, dif_pos hx, (Nat.find_spec hx).1.lt]

/--
theorem `minimalPeriod_eq_zero_of_notMem_periodicPts` / 定理 `minimalPeriod_eq_zero_of_notMem_periodicPts`

English:
theorem minimalPeriod_eq_zero_of_notMem_periodicPts
  given: (hx : x ∉ periodicPts f)
  proof: by simp only [minimalPeriod, dif_neg hx]

中文:
定理 minimalPeriod_eq_zero_of_notMem_periodicPts
  条件: (hx : x ∉ periodicPts f)
  证明: by simp only [minimalPeriod, dif_neg hx]

Depends on / 依赖: dif_neg, minimalPeriod
-/
theorem minimalPeriod_eq_zero_of_notMem_periodicPts (hx : x ∉ periodicPts f) :
    minimalPeriod f x = 0 := by simp only [minimalPeriod, dif_neg hx]

/--
theorem `IsPeriodicPt.minimalPeriod_pos` / 定理 `IsPeriodicPt.minimalPeriod_pos`

English:
theorem IsPeriodicPt.minimalPeriod_pos
  given: (hn : 0 < n) (hx : IsPeriodicPt f n x)
  proof: minimalPeriod_pos_of_mem_periodicPts mk_mem_periodicPts hn hx

中文:
定理 IsPeriodicPt.minimalPeriod_pos
  条件: (hn : 0 < n) (hx : IsPeriodicPt f n x)
  证明: minimalPeriod_pos_of_mem_periodicPts mk_mem_periodicPts hn hx

Depends on / 依赖: minimalPeriod_pos_of_mem_periodicPts, mk_mem_periodicPts
-/
theorem IsPeriodicPt.minimalPeriod_pos (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    0 < minimalPeriod f x :=
minimalPeriod_pos_of_mem_periodicPts mk_mem_periodicPts hn hx

/--
theorem `minimalPeriod_pos_iff_mem_periodicPts` / 定理 `minimalPeriod_pos_iff_mem_periodicPts`

English:
theorem minimalPeriod_pos_iff_mem_periodicPts
  statement: 0 < minimalPeriod f x ↔ x in periodicPts f
  proof: ⟨not_imp_not.1 fun h => by simp only [minimalPeriod, dif_neg h, lt_irrefl 0, not_false_iff],
    minimalPeriod_pos_of_mem_periodicPts⟩

中文:
定理 minimalPeriod_pos_iff_mem_periodicPts
  结论: 0 < minimalPeriod f x ↔ x in periodicPts f
  证明: ⟨not_imp_not.1 fun h => by simp only [minimalPeriod, dif_neg h, lt_irrefl 0, not_false_iff],
    minimalPeriod_pos_of_mem_periodicPts⟩

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, SMul.smul_stabilizer_def, Subgroup, Subgroup.coe_mul, Subtype, Subtype.coe_inj, coe_inj, coe_mul, coe_one, dif_neg, lt_irrefl, minimalPeriod, minimalPeriod_pos_of_mem_periodicPts, mul_smul, not_false_iff, not_imp_not, one_smul, smul_stabilizer_def
-/
theorem minimalPeriod_pos_iff_mem_periodicPts : 0 < minimalPeriod f x ↔ x in periodicPts f :=
  ⟨not_imp_not.1 fun h => by simp only [minimalPeriod, dif_neg h, lt_irrefl 0, not_false_iff],
    minimalPeriod_pos_of_mem_periodicPts⟩

/--
theorem `minimalPeriod_eq_zero_iff_notMem_periodicPts` / 定理 `minimalPeriod_eq_zero_iff_notMem_periodicPts`

English:
theorem minimalPeriod_eq_zero_iff_notMem_periodicPts
  proof: by
  rw [← minimalPeriod_pos_iff_mem_periodicPts]; rw [not_lt]; rw [nonpos_iff_eq_zero]

中文:
定理 minimalPeriod_eq_zero_iff_notMem_periodicPts
  证明: by
  rw [← minimalPeriod_pos_iff_mem_periodicPts]; rw [not_lt]; rw [nonpos_iff_eq_zero]

Depends on / 依赖: minimalPeriod_pos_iff_mem_periodicPts, nonpos_iff_eq_zero, not_lt
-/
theorem minimalPeriod_eq_zero_iff_notMem_periodicPts :
    minimalPeriod f x = 0 ↔ x ∉ periodicPts f := by
  rw [← minimalPeriod_pos_iff_mem_periodicPts]; rw [not_lt]; rw [nonpos_iff_eq_zero]

/--
theorem `IsPeriodicPt.minimalPeriod_le` / 定理 `IsPeriodicPt.minimalPeriod_le`

English:
theorem IsPeriodicPt.minimalPeriod_le
  given: (hn : 0 < n) (hx : IsPeriodicPt f n x)
  proof: by
  classical
  rw [minimalPeriod]; rw [dif_pos (mk_mem_periodicPts hn hx)]
  exact Nat.find_min' (mk_mem_periodicPts hn hx) ⟨hn, hx⟩

中文:
定理 IsPeriodicPt.minimalPeriod_le
  条件: (hn : 0 < n) (hx : IsPeriodicPt f n x)
  证明: by
  classical
  rw [minimalPeriod]; rw [dif_pos (mk_mem_periodicPts hn hx)]
  exact Nat.find_min' (mk_mem_periodicPts hn hx) ⟨hn, hx⟩

Depends on / 依赖: Nat.find_min, classical, dif_pos, find_min, minimalPeriod, mk_mem_periodicPts
-/
theorem IsPeriodicPt.minimalPeriod_le (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    minimalPeriod f x <= n := by
  classical
  rw [minimalPeriod]; rw [dif_pos (mk_mem_periodicPts hn hx)]
  exact Nat.find_min' (mk_mem_periodicPts hn hx) ⟨hn, hx⟩

/--
theorem `minimalPeriod_apply_iterate` / 定理 `minimalPeriod_apply_iterate`

English:
theorem minimalPeriod_apply_iterate
  given: (hx : x in periodicPts f) (n : Nat)
  proof: by
  apply
    (IsPeriodicPt.minimalPeriod_le (minimalPeriod_pos_of_mem_periodicPts hx) _).antisymm
      ((isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hx
            (isPeriodicPt_minimalPeriod f _)).minimalPeriod_le
        (minimalPeriod_pos_of_mem_periodicPts _))
  · exact (isPeriodi

中文:
定理 minimalPeriod_apply_iterate
  条件: (hx : x in periodicPts f) (n : 自然数)
  证明: by
  apply
    (IsPeriodicPt.minimalPeriod_le (minimalPeriod_pos_of_mem_periodicPts hx) _).antisymm
      ((isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hx
            (isPeriodicPt_minimalPeriod f _)).minimalPeriod_le
        (minimalPeriod_pos_of_mem_periodicPts _))
  · exact (isPeriodi

Depends on / 依赖: IsPeriodicPt, IsPeriodicPt.minimalPeriod_le, antisymm, apply_iterate, hx.apply_iterate, isPeriodicPt_minimalPeriod, isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate, minimalPeriod_le, minimalPeriod_pos_of_mem_periodicPts
-/
theorem minimalPeriod_apply_iterate (hx : x in periodicPts f) (n : Nat) :
    minimalPeriod f (f^[n] x) = minimalPeriod f x := by
  apply
    (IsPeriodicPt.minimalPeriod_le (minimalPeriod_pos_of_mem_periodicPts hx) _).antisymm
      ((isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hx
            (isPeriodicPt_minimalPeriod f _)).minimalPeriod_le
        (minimalPeriod_pos_of_mem_periodicPts _))
  · exact (isPeriodicPt_minimalPeriod f x).apply_iterate n
  · rcases hx with ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.apply_iterate n⟩

/--
theorem `minimalPeriod_apply` / 定理 `minimalPeriod_apply`

English:
theorem minimalPeriod_apply
  given: (hx : x in periodicPts f)
  statement: minimalPeriod f (f x) = minimalPeriod f x
  proof: minimalPeriod_apply_iterate hx 1

中文:
定理 minimalPeriod_apply
  条件: (hx : x in periodicPts f)
  结论: minimalPeriod f (f x) = minimalPeriod f x
  证明: minimalPeriod_apply_iterate hx 1

Depends on / 依赖: minimalPeriod_apply_iterate
-/
theorem minimalPeriod_apply (hx : x in periodicPts f) : minimalPeriod f (f x) = minimalPeriod f x :=
  minimalPeriod_apply_iterate hx 1

/--
theorem `le_of_lt_minimalPeriod_of_iterate_eq` / 定理 `le_of_lt_minimalPeriod_of_iterate_eq`

English:
theorem le_of_lt_minimalPeriod_of_iterate_eq
  statement: {m n : Nat} (hm : m < minimalPeriod f x)
  proof: by
  by_contra! hmn'
  rw [← Nat.add_sub_of_le hmn'.le]; rw [add_comm]; rw [iterate_add_apply] at hmn
  exact ((IsPeriodicPt.minimalPeriod_le (tsub_pos_of_lt hmn')
    (isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
      (minimalPeriod_pos_iff_mem_periodicPts.1 hm.pos) hmn)).trans (Nat.sub

中文:
定理 le_of_lt_minimalPeriod_of_iterate_eq
  结论: {m n : 自然数} (hm : m < minimalPeriod f x)
  证明: by
  by_contra! hmn'
  rw [← Nat.add_sub_of_le hmn'.le]; rw [add_comm]; rw [iterate_add_apply] at hmn
  exact ((IsPeriodicPt.minimalPeriod_le (tsub_pos_of_lt hmn')
    (isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
      (minimalPeriod_pos_iff_mem_periodicPts.1 hm.pos) hmn)).trans (Nat.sub

Depends on / 依赖: IsPeriodicPt, IsPeriodicPt.minimalPeriod_le, Nat.add_sub_of_le, Nat.sub_le, add_comm, add_sub_of_le, hm.pos, isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate, iterate_add_apply, minimalPeriod_le, minimalPeriod_pos_iff_mem_periodicPts, not_gt, sub_le, tsub_pos_of_lt
-/
theorem le_of_lt_minimalPeriod_of_iterate_eq {m n : Nat} (hm : m < minimalPeriod f x)
    (hmn : f^[m] x = f^[n] x) : m <= n := by
  by_contra! hmn'
  rw [← Nat.add_sub_of_le hmn'.le]; rw [add_comm]; rw [iterate_add_apply] at hmn
  exact ((IsPeriodicPt.minimalPeriod_le (tsub_pos_of_lt hmn')
    (isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
      (minimalPeriod_pos_iff_mem_periodicPts.1 hm.pos) hmn)).trans (Nat.sub_le m n)).not_gt hm

/--
theorem `iterate_injOn_Iio_minimalPeriod` / 定理 `iterate_injOn_Iio_minimalPeriod`

English:
theorem iterate_injOn_Iio_minimalPeriod
  statement: (Iio <| minimalPeriod f x).InjOn (f^[·] x)
  proof: fun _m hm _n hn hmn => (le_of_lt_minimalPeriod_of_iterate_eq hm hmn).antisymm
    (le_of_lt_minimalPeriod_of_iterate_eq hn hmn.symm)

中文:
定理 iterate_injOn_Iio_minimalPeriod
  结论: (左无界右开区间 <| minimalPeriod f x).单射限制 (f^[·] x)
  证明: fun _m hm _n hn hmn => (le_of_lt_minimalPeriod_of_iterate_eq hm hmn).antisymm
    (le_of_lt_minimalPeriod_of_iterate_eq hn hmn.symm)

Depends on / 依赖: antisymm, hmn.symm, le_of_lt_minimalPeriod_of_iterate_eq
-/
theorem iterate_injOn_Iio_minimalPeriod : (Iio <| minimalPeriod f x).InjOn (f^[·] x) :=
  fun _m hm _n hn hmn => (le_of_lt_minimalPeriod_of_iterate_eq hm hmn).antisymm
    (le_of_lt_minimalPeriod_of_iterate_eq hn hmn.symm)

/--
theorem `iterate_eq_iterate_iff_of_lt_minimalPeriod` / 定理 `iterate_eq_iterate_iff_of_lt_minimalPeriod`

English:
theorem iterate_eq_iterate_iff_of_lt_minimalPeriod
  statement: {m n : Nat} (hm : m < minimalPeriod f x)
  proof: iterate_injOn_Iio_minimalPeriod.eq_iff hm hn

中文:
定理 iterate_eq_iterate_iff_of_lt_minimalPeriod
  结论: {m n : 自然数} (hm : m < minimalPeriod f x)
  证明: iterate_injOn_Iio_minimalPeriod.eq_iff hm hn

Depends on / 依赖: eq_iff, iterate_injOn_Iio_minimalPeriod, iterate_injOn_Iio_minimalPeriod.eq_iff
-/
theorem iterate_eq_iterate_iff_of_lt_minimalPeriod {m n : Nat} (hm : m < minimalPeriod f x)
    (hn : n < minimalPeriod f x) : f^[m] x = f^[n] x ↔ m = n :=
  iterate_injOn_Iio_minimalPeriod.eq_iff hm hn

/--
theorem `minimalPeriod_id` / 定理 `minimalPeriod_id`

English:
theorem minimalPeriod_id
  statement: minimalPeriod id x = 1
  proof: ((is_periodic_id _ _).minimalPeriod_le Nat.one_pos).antisymm
    (Nat.succ_le_of_lt ((is_periodic_id _ _).minimalPeriod_pos Nat.one_pos))

@[simp]

中文:
定理 minimalPeriod_id
  结论: minimalPeriod id x = 1
  证明: ((is_periodic_id _ _).minimalPeriod_le Nat.one_pos).antisymm
    (Nat.succ_le_of_lt ((is_periodic_id _ _).minimalPeriod_pos Nat.one_pos))

@[simp]
-/
@[simp] theorem minimalPeriod_id : minimalPeriod id x = 1 :=
  ((is_periodic_id _ _).minimalPeriod_le Nat.one_pos).antisymm
    (Nat.succ_le_of_lt ((is_periodic_id _ _).minimalPeriod_pos Nat.one_pos))

@[simp]
/--
theorem `minimalPeriod_eq_one_iff_isFixedPt` / 定理 `minimalPeriod_eq_one_iff_isFixedPt`

English:
theorem minimalPeriod_eq_one_iff_isFixedPt
  statement: minimalPeriod f x = 1 ↔ IsFixedPt f x
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← iterate_one f]
    refine Function.IsPeriodicPt.isFixedPt ?_
    rw [← h]
    exact isPeriodicPt_minimalPeriod f x
  · exact
      ((h.isPeriodicPt 1).minimalPeriod_le Nat.one_pos).antisymm
        (Nat.succ_le_of_lt ((h.isPeriodicPt 1).minimalPeriod_

中文:
定理 minimalPeriod_eq_one_iff_isFixedPt
  结论: minimalPeriod f x = 1 ↔ IsFixedPt f x
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← iterate_one f]
    refine Function.IsPeriodicPt.isFixedPt ?_
    rw [← h]
    exact isPeriodicPt_minimalPeriod f x
  · exact
      ((h.isPeriodicPt 1).minimalPeriod_le Nat.one_pos).antisymm
        (Nat.succ_le_of_lt ((h.isPeriodicPt 1).minimalPeriod_

Depends on / 依赖: Function, Function.IsPeriodicPt.isFixedPt, IsPeriodicPt, Nat.one_pos, Nat.succ_le_of_lt, antisymm, h.isPeriodicPt, isFixedPt, isPeriodicPt, isPeriodicPt_minimalPeriod, iterate_one, minimalPeriod_le, minimalPeriod_pos, one_pos, succ_le_of_lt
-/
theorem minimalPeriod_eq_one_iff_isFixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← iterate_one f]
    refine Function.IsPeriodicPt.isFixedPt ?_
    rw [← h]
    exact isPeriodicPt_minimalPeriod f x
  · exact
      ((h.isPeriodicPt 1).minimalPeriod_le Nat.one_pos).antisymm
        (Nat.succ_le_of_lt ((h.isPeriodicPt 1).minimalPeriod_pos Nat.one_pos))

@[nontriviality]
/--
theorem `minimalPeriod_eq_one_of_subsingleton` / 定理 `minimalPeriod_eq_one_of_subsingleton`

English:
theorem minimalPeriod_eq_one_of_subsingleton
  given: [Subsingleton α]
  statement: minimalPeriod f x = 1
  proof: by
  simp [nontriviality]

中文:
定理 minimalPeriod_eq_one_of_subsingleton
  条件: [子单例 α]
  结论: minimalPeriod f x = 1
  证明: by
  simp [nontriviality]

Depends on / 依赖: nontriviality
-/
theorem minimalPeriod_eq_one_of_subsingleton [Subsingleton α] : minimalPeriod f x = 1 := by
  simp [nontriviality]

/--
theorem `IsPeriodicPt.eq_zero_of_lt_minimalPeriod` / 定理 `IsPeriodicPt.eq_zero_of_lt_minimalPeriod`

English:
theorem IsPeriodicPt.eq_zero_of_lt_minimalPeriod
  statement: (hx : IsPeriodicPt f n x)
  proof: Eq.symm
    (eq_or_lt_of_le <| n.zero_le).resolve_right fun hn0 => not_lt.2 (hx.minimalPeriod_le hn0) hn

中文:
定理 IsPeriodicPt.eq_zero_of_lt_minimalPeriod
  结论: (hx : IsPeriodicPt f n x)
  证明: Eq.symm
    (eq_or_lt_of_le <| n.zero_le).resolve_right fun hn0 => not_lt.2 (hx.minimalPeriod_le hn0) hn

Depends on / 依赖: Eq.symm, eq_or_lt_of_le, hx.minimalPeriod_le, minimalPeriod_le, n.zero_le, not_lt, resolve_right, zero_le
-/
theorem IsPeriodicPt.eq_zero_of_lt_minimalPeriod (hx : IsPeriodicPt f n x)
    (hn : n < minimalPeriod f x) : n = 0 :=
Eq.symm
    (eq_or_lt_of_le <| n.zero_le).resolve_right fun hn0 => not_lt.2 (hx.minimalPeriod_le hn0) hn

/--
theorem `not_isPeriodicPt_of_pos_of_lt_minimalPeriod` / 定理 `not_isPeriodicPt_of_pos_of_lt_minimalPeriod`

English:
theorem not_isPeriodicPt_of_pos_of_lt_minimalPeriod

中文:
定理 not_isPeriodicPt_of_pos_of_lt_minimalPeriod
-/
theorem not_isPeriodicPt_of_pos_of_lt_minimalPeriod :
    forall {n : Nat} (_ : n != 0) (_ : n < minimalPeriod f x), ¬IsPeriodicPt f n x
  | 0, n0, _ => (n0 rfl).elim
  | _ + 1, _, hn => fun hp => Nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimalPeriod hn)

/--
theorem `IsPeriodicPt.minimalPeriod_dvd` / 定理 `IsPeriodicPt.minimalPeriod_dvd`

English:
theorem IsPeriodicPt.minimalPeriod_dvd
  given: (hx : IsPeriodicPt f n x)
  statement: minimalPeriod f x ∣ n
  proof: (eq_or_lt_of_le <| n.zero_le).elim (fun hn0 => hn0 ▸ Nat.dvd_zero _) fun hn0 =>
Nat.dvd_iff_mod_eq_zero.2
(hx.mod <| isPeriodicPt_minimalPeriod f x).eq_zero_of_lt_minimalPeriod
Nat.mod_lt _ hx.minimalPeriod_pos hn0

中文:
定理 IsPeriodicPt.minimalPeriod_dvd
  条件: (hx : IsPeriodicPt f n x)
  结论: minimalPeriod f x ∣ n
  证明: (eq_or_lt_of_le <| n.zero_le).elim (fun hn0 => hn0 ▸ Nat.dvd_zero _) fun hn0 =>
Nat.dvd_iff_mod_eq_zero.2
(hx.mod <| isPeriodicPt_minimalPeriod f x).eq_zero_of_lt_minimalPeriod
Nat.mod_lt _ hx.minimalPeriod_pos hn0

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, Nat.dvd_zero, Nat.mod_lt, dvd_iff_mod_eq_zero, dvd_zero, eq_or_lt_of_le, eq_zero_of_lt_minimalPeriod, hx.minimalPeriod_pos, hx.mod, isPeriodicPt_minimalPeriod, minimalPeriod_pos, mod_lt, n.zero_le, zero_le
-/
theorem IsPeriodicPt.minimalPeriod_dvd (hx : IsPeriodicPt f n x) : minimalPeriod f x ∣ n :=
  (eq_or_lt_of_le <| n.zero_le).elim (fun hn0 => hn0 ▸ Nat.dvd_zero _) fun hn0 =>
Nat.dvd_iff_mod_eq_zero.2
(hx.mod <| isPeriodicPt_minimalPeriod f x).eq_zero_of_lt_minimalPeriod
Nat.mod_lt _ hx.minimalPeriod_pos hn0

/--
theorem `isPeriodicPt_iff_minimalPeriod_dvd` / 定理 `isPeriodicPt_iff_minimalPeriod_dvd`

English:
theorem isPeriodicPt_iff_minimalPeriod_dvd
  statement: IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
  proof: ⟨IsPeriodicPt.minimalPeriod_dvd, fun h => (isPeriodicPt_minimalPeriod f x).trans_dvd h⟩

中文:
定理 isPeriodicPt_iff_minimalPeriod_dvd
  结论: IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
  证明: ⟨IsPeriodicPt.minimalPeriod_dvd, fun h => (isPeriodicPt_minimalPeriod f x).trans_dvd h⟩

Depends on / 依赖: IsPeriodicPt, IsPeriodicPt.minimalPeriod_dvd, isPeriodicPt_minimalPeriod, minimalPeriod_dvd, trans_dvd
-/
theorem isPeriodicPt_iff_minimalPeriod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n :=
  ⟨IsPeriodicPt.minimalPeriod_dvd, fun h => (isPeriodicPt_minimalPeriod f x).trans_dvd h⟩

open Nat

/--
theorem `minimalPeriod_eq_minimalPeriod_iff` / 定理 `minimalPeriod_eq_minimalPeriod_iff`

English:
theorem minimalPeriod_eq_minimalPeriod_iff
  given: {g : β -> β} {y : β}
  proof: by
  simp_rw [isPeriodicPt_iff_minimalPeriod_dvd, dvd_right_iff_eq]

中文:
定理 minimalPeriod_eq_minimalPeriod_iff
  条件: {g : β -> β} {y : β}
  证明: by
  simp_rw [isPeriodicPt_iff_minimalPeriod_dvd, dvd_right_iff_eq]

Depends on / 依赖: dvd_right_iff_eq, isPeriodicPt_iff_minimalPeriod_dvd, simp_rw
-/
theorem minimalPeriod_eq_minimalPeriod_iff {g : β -> β} {y : β} :
    minimalPeriod f x = minimalPeriod g y ↔ forall n, IsPeriodicPt f n x ↔ IsPeriodicPt g n y := by
  simp_rw [isPeriodicPt_iff_minimalPeriod_dvd, dvd_right_iff_eq]

/--
theorem `Commute.minimalPeriod_of_comp_dvd_lcm` / 定理 `Commute.minimalPeriod_of_comp_dvd_lcm`

English:
theorem Commute.minimalPeriod_of_comp_dvd_lcm
  given: {g : α -> α} (h : Commute f g)
  proof: by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  exact (isPeriodicPt_minimalPeriod f x).comp_lcm h (isPeriodicPt_minimalPeriod g x)

中文:
定理 Commute.minimalPeriod_of_comp_dvd_lcm
  条件: {g : α -> α} (h : Commute f g)
  证明: by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  exact (isPeriodicPt_minimalPeriod f x).comp_lcm h (isPeriodicPt_minimalPeriod g x)

Depends on / 依赖: comp_lcm, isPeriodicPt_iff_minimalPeriod_dvd, isPeriodicPt_minimalPeriod
-/
theorem Commute.minimalPeriod_of_comp_dvd_lcm {g : α -> α} (h : Commute f g) :
    minimalPeriod (f ∘ g) x ∣ Nat.lcm (minimalPeriod f x) (minimalPeriod g x) := by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  exact (isPeriodicPt_minimalPeriod f x).comp_lcm h (isPeriodicPt_minimalPeriod g x)

/--
theorem `minimalPeriod_iterate_eq_div_gcd_aux` / 定理 `minimalPeriod_iterate_eq_div_gcd_aux`

English:
theorem minimalPeriod_iterate_eq_div_gcd_aux
  given: (h : 0 < gcd (minimalPeriod f x) n)
  proof: by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt]; rw [IsFixedPt]; rw [← iterate_mul]; rw [← Nat.mul_div_assoc _ (gcd_dvd_left _ _)]; rw [mul_comm]; rw [Nat.mul_div_assoc _ (gcd_dvd_right _ _)]; rw [mul_comm]; rw [iterate_mul]
    exact (isPeriodicPt_minimalP

中文:
定理 minimalPeriod_iterate_eq_div_gcd_aux
  条件: (h : 0 < 最大公约数 (minimalPeriod f x) n)
  证明: by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt]; rw [IsFixedPt]; rw [← iterate_mul]; rw [← Nat.mul_div_assoc _ (gcd_dvd_left _ _)]; rw [mul_comm]; rw [Nat.mul_div_assoc _ (gcd_dvd_right _ _)]; rw [mul_comm]; rw [iterate_mul]
    exact (isPeriodicPt_minimalP
-/
private theorem minimalPeriod_iterate_eq_div_gcd_aux (h : 0 < gcd (minimalPeriod f x) n) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n := by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt]; rw [IsFixedPt]; rw [← iterate_mul]; rw [← Nat.mul_div_assoc _ (gcd_dvd_left _ _)]; rw [mul_comm]; rw [Nat.mul_div_assoc _ (gcd_dvd_right _ _)]; rw [mul_comm]; rw [iterate_mul]
    exact (isPeriodicPt_minimalPeriod f x).iterate _
  · apply Coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h)
    apply Nat.dvd_of_mul_dvd_mul_right h
    rw [Nat.div_mul_cancel (gcd_dvd_left _ _)]; rw [mul_assoc]; rw [Nat.div_mul_cancel (gcd_dvd_right _ _)]; rw [mul_comm]
    apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt]; rw [IsFixedPt]; rw [iterate_mul]
    exact isPeriodicPt_minimalPeriod _ _

/--
theorem `minimalPeriod_iterate_eq_div_gcd` / 定理 `minimalPeriod_iterate_eq_div_gcd`

English:
theorem minimalPeriod_iterate_eq_div_gcd
  given: (h : n != 0)
  proof: minimalPeriod_iterate_eq_div_gcd_aux gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h)

中文:
定理 minimalPeriod_iterate_eq_div_gcd
  条件: (h : n != 0)
  证明: minimalPeriod_iterate_eq_div_gcd_aux gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h)

Depends on / 依赖: Nat.pos_of_ne_zero, gcd_pos_of_pos_right, minimalPeriod_iterate_eq_div_gcd_aux, pos_of_ne_zero
-/
theorem minimalPeriod_iterate_eq_div_gcd (h : n != 0) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n :=
minimalPeriod_iterate_eq_div_gcd_aux gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h)

/--
theorem `minimalPeriod_iterate_eq_div_gcd'` / 定理 `minimalPeriod_iterate_eq_div_gcd'`

English:
theorem minimalPeriod_iterate_eq_div_gcd'
  given: (h : x in periodicPts f)
  proof: minimalPeriod_iterate_eq_div_gcd_aux
    gcd_pos_of_pos_left n (minimalPeriod_pos_iff_mem_periodicPts.mpr h)

中文:
定理 minimalPeriod_iterate_eq_div_gcd'
  条件: (h : x in periodicPts f)
  证明: minimalPeriod_iterate_eq_div_gcd_aux
    gcd_pos_of_pos_left n (minimalPeriod_pos_iff_mem_periodicPts.mpr h)

Depends on / 依赖: gcd_pos_of_pos_left, minimalPeriod_iterate_eq_div_gcd_aux, minimalPeriod_pos_iff_mem_periodicPts, minimalPeriod_pos_iff_mem_periodicPts.mpr
-/
theorem minimalPeriod_iterate_eq_div_gcd' (h : x in periodicPts f) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n :=
minimalPeriod_iterate_eq_div_gcd_aux
    gcd_pos_of_pos_left n (minimalPeriod_pos_iff_mem_periodicPts.mpr h)

/--
Definition of `periodicOrbit` / `periodicOrbit` 的定义

English:
definition periodicOrbit
  signature: (f : α -> α) (x : α)
  body: (List.range (minimalPeriod f x)).map fun n => f^[n] x

中文:
定义 periodicOrbit
  签名: (f : α -> α) (x : α)
  定义体: (List.range (minimalPeriod f x)).map fun n => f^[n] x

Depends on / 依赖: List.range, minimalPeriod
-/
def periodicOrbit (f : α -> α) (x : α) : Cycle α :=
  (List.range (minimalPeriod f x)).map fun n => f^[n] x

/--
theorem `periodicOrbit_def` / 定理 `periodicOrbit_def`

English:
theorem periodicOrbit_def
  given: (f : α -> α) (x : α)
  proof: rfl

中文:
定理 periodicOrbit_def
  条件: (f : α -> α) (x : α)
  证明: rfl
-/
theorem periodicOrbit_def (f : α -> α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x)).map fun n => f^[n] x :=
  rfl

/--
theorem `periodicOrbit_eq_cycle_map` / 定理 `periodicOrbit_eq_cycle_map`

English:
theorem periodicOrbit_eq_cycle_map
  given: (f : α -> α) (x : α)
  proof: rfl

@[simp]

中文:
定理 periodicOrbit_eq_cycle_map
  条件: (f : α -> α) (x : α)
  证明: rfl

@[simp]
-/
theorem periodicOrbit_eq_cycle_map (f : α -> α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x) : Cycle Nat).map fun n => f^[n] x :=
  rfl

@[simp]
/--
theorem `periodicOrbit_length` / 定理 `periodicOrbit_length`

English:
theorem periodicOrbit_length
  statement: (periodicOrbit f x).length = minimalPeriod f x
  proof: by
  rw [periodicOrbit]; rw [Cycle.length_coe]; rw [List.length_map]; rw [List.length_range]

@[simp]

中文:
定理 periodicOrbit_length
  结论: (periodicOrbit f x).length = minimalPeriod f x
  证明: by
  rw [periodicOrbit]; rw [Cycle.length_coe]; rw [List.length_map]; rw [List.length_range]

@[simp]

Depends on / 依赖: Cycle.length_coe, List.length_map, List.length_range, length_coe, length_map, length_range, periodicOrbit
-/
theorem periodicOrbit_length : (periodicOrbit f x).length = minimalPeriod f x := by
  rw [periodicOrbit]; rw [Cycle.length_coe]; rw [List.length_map]; rw [List.length_range]

@[simp]
/--
theorem `periodicOrbit_eq_nil_iff_not_periodic_pt` / 定理 `periodicOrbit_eq_nil_iff_not_periodic_pt`

English:
theorem periodicOrbit_eq_nil_iff_not_periodic_pt
  proof: by
  simp only [periodicOrbit.eq_1, Cycle.coe_eq_nil, List.map_eq_nil_iff, List.range_eq_nil]
  exact minimalPeriod_eq_zero_iff_notMem_periodicPts

中文:
定理 periodicOrbit_eq_nil_iff_not_periodic_pt
  证明: by
  simp only [periodicOrbit.eq_1, Cycle.coe_eq_nil, List.map_eq_nil_iff, List.range_eq_nil]
  exact minimalPeriod_eq_zero_iff_notMem_periodicPts

Depends on / 依赖: Cycle.coe_eq_nil, List.map_eq_nil_iff, List.range_eq_nil, coe_eq_nil, eq_1, map_eq_nil_iff, minimalPeriod_eq_zero_iff_notMem_periodicPts, periodicOrbit, periodicOrbit.eq_1, range_eq_nil
-/
theorem periodicOrbit_eq_nil_iff_not_periodic_pt :
    periodicOrbit f x = Cycle.nil ↔ x ∉ periodicPts f := by
  simp only [periodicOrbit.eq_1, Cycle.coe_eq_nil, List.map_eq_nil_iff, List.range_eq_nil]
  exact minimalPeriod_eq_zero_iff_notMem_periodicPts

/--
theorem `periodicOrbit_eq_nil_of_not_periodic_pt` / 定理 `periodicOrbit_eq_nil_of_not_periodic_pt`

English:
theorem periodicOrbit_eq_nil_of_not_periodic_pt
  given: (h : x ∉ periodicPts f)
  proof: periodicOrbit_eq_nil_iff_not_periodic_pt.2 h

@[simp]

中文:
定理 periodicOrbit_eq_nil_of_not_periodic_pt
  条件: (h : x ∉ periodicPts f)
  证明: periodicOrbit_eq_nil_iff_not_periodic_pt.2 h

@[simp]

Depends on / 依赖: periodicOrbit_eq_nil_iff_not_periodic_pt
-/
theorem periodicOrbit_eq_nil_of_not_periodic_pt (h : x ∉ periodicPts f) :
    periodicOrbit f x = Cycle.nil :=
  periodicOrbit_eq_nil_iff_not_periodic_pt.2 h

@[simp]
/--
theorem `mem_periodicOrbit_iff` / 定理 `mem_periodicOrbit_iff`

English:
theorem mem_periodicOrbit_iff
  given: (hx : x in periodicPts f)
  proof: by
  simp only [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range]
  use fun ⟨a, _, ha'⟩ => ⟨a, ha'⟩
  rintro ⟨n, rfl⟩
  use n % minimalPeriod f x, mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx)
  rw [iterate_mod_minimalPeriod_eq]

中文:
定理 mem_periodicOrbit_iff
  条件: (hx : x in periodicPts f)
  证明: by
  simp only [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range]
  use fun ⟨a, _, ha'⟩ => ⟨a, ha'⟩
  rintro ⟨n, rfl⟩
  use n % minimalPeriod f x, mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx)
  rw [iterate_mod_minimalPeriod_eq]

Depends on / 依赖: Cycle.mem_coe_iff, List.mem_map, List.mem_range, iterate_mod_minimalPeriod_eq, mem_coe_iff, mem_map, mem_range, minimalPeriod, minimalPeriod_pos_of_mem_periodicPts, mod_lt, periodicOrbit
-/
theorem mem_periodicOrbit_iff (hx : x in periodicPts f) :
    y in periodicOrbit f x ↔ exists n, f^[n] x = y := by
  simp only [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range]
  use fun ⟨a, _, ha'⟩ => ⟨a, ha'⟩
  rintro ⟨n, rfl⟩
  use n % minimalPeriod f x, mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx)
  rw [iterate_mod_minimalPeriod_eq]

/--
theorem `iterate_mem_periodicOrbit` / 定理 `iterate_mem_periodicOrbit`

English:
theorem iterate_mem_periodicOrbit
  given: (hx : x in periodicPts f) (n : Nat)
  proof: by
  simp [hx]

@[simp]

中文:
定理 iterate_mem_periodicOrbit
  条件: (hx : x in periodicPts f) (n : 自然数)
  证明: by
  simp [hx]

@[simp]
-/
theorem iterate_mem_periodicOrbit (hx : x in periodicPts f) (n : Nat) :
    f^[n] x in periodicOrbit f x := by
  simp [hx]

@[simp]
/--
theorem `exists_iterate_apply_eq_of_mem_periodicPts` / 定理 `exists_iterate_apply_eq_of_mem_periodicPts`

English:
theorem exists_iterate_apply_eq_of_mem_periodicPts
  given: (hx : x in periodicPts f)
  statement: exists n, f^[n] x = x
  proof: by
  simpa only [← mem_periodicOrbit_iff hx] using! iterate_mem_periodicOrbit hx 0

中文:
定理 存在_iterate_apply_eq_of_mem_periodicPts
  条件: (hx : x in periodicPts f)
  结论: 存在 n, f^[n] x = x
  证明: by
  simpa only [← mem_periodicOrbit_iff hx] using! iterate_mem_periodicOrbit hx 0

Depends on / 依赖: iterate_mem_periodicOrbit, mem_periodicOrbit_iff
-/
theorem exists_iterate_apply_eq_of_mem_periodicPts (hx : x in periodicPts f) : exists n, f^[n] x = x := by
  simpa only [← mem_periodicOrbit_iff hx] using! iterate_mem_periodicOrbit hx 0

/--
theorem `self_mem_periodicOrbit` / 定理 `self_mem_periodicOrbit`

English:
theorem self_mem_periodicOrbit
  given: (hx : x in periodicPts f)
  statement: x in periodicOrbit f x
  proof: by
  simp [hx]

中文:
定理 self_mem_periodicOrbit
  条件: (hx : x in periodicPts f)
  结论: x in periodicOrbit f x
  证明: by
  simp [hx]
-/
theorem self_mem_periodicOrbit (hx : x in periodicPts f) : x in periodicOrbit f x := by
  simp [hx]

/--
theorem `nodup_periodicOrbit` / 定理 `nodup_periodicOrbit`

English:
theorem nodup_periodicOrbit
  statement: (periodicOrbit f x).Nodup
  proof: by
  rw [periodicOrbit]; rw [Cycle.nodup_coe_iff]; rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro m hm n hn hmn
  rw [List.mem_range] at hm hn
  rwa [iterate_eq_iterate_iff_of_lt_minimalPeriod hm hn] at hmn

中文:
定理 nodup_periodicOrbit
  结论: (periodicOrbit f x).Nodup
  证明: by
  rw [periodicOrbit]; rw [Cycle.nodup_coe_iff]; rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro m hm n hn hmn
  rw [List.mem_range] at hm hn
  rwa [iterate_eq_iterate_iff_of_lt_minimalPeriod hm hn] at hmn

Depends on / 依赖: Cycle.nodup_coe_iff, List.mem_range, List.nodup_map_iff_inj_on, List.nodup_range, iterate_eq_iterate_iff_of_lt_minimalPeriod, mem_range, nodup_coe_iff, nodup_map_iff_inj_on, nodup_range, periodicOrbit
-/
theorem nodup_periodicOrbit : (periodicOrbit f x).Nodup := by
  rw [periodicOrbit]; rw [Cycle.nodup_coe_iff]; rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro m hm n hn hmn
  rw [List.mem_range] at hm hn
  rwa [iterate_eq_iterate_iff_of_lt_minimalPeriod hm hn] at hmn

/--
theorem `periodicOrbit_apply_iterate_eq` / 定理 `periodicOrbit_apply_iterate_eq`

English:
theorem periodicOrbit_apply_iterate_eq
  given: (hx : x in periodicPts f) (n : Nat)
  proof: Eq.symm Cycle.coe_eq_coe.2 .intro n
    List.ext_get (by simp [minimalPeriod_apply_iterate hx]) fun m _ _ => by
      simp [List.getElem_rotate, iterate_add_apply]

中文:
定理 periodicOrbit_apply_iterate_eq
  条件: (hx : x in periodicPts f) (n : 自然数)
  证明: Eq.symm Cycle.coe_eq_coe.2 .intro n
    List.ext_get (by simp [minimalPeriod_apply_iterate hx]) fun m _ _ => by
      simp [List.getElem_rotate, iterate_add_apply]

Depends on / 依赖: Cycle.coe_eq_coe, Eq.symm, List.ext_get, List.getElem_rotate, coe_eq_coe, ext_get, getElem_rotate, iterate_add_apply, minimalPeriod_apply_iterate
-/
theorem periodicOrbit_apply_iterate_eq (hx : x in periodicPts f) (n : Nat) :
    periodicOrbit f (f^[n] x) = periodicOrbit f x :=
Eq.symm Cycle.coe_eq_coe.2 .intro n
    List.ext_get (by simp [minimalPeriod_apply_iterate hx]) fun m _ _ => by
      simp [List.getElem_rotate, iterate_add_apply]

/--
theorem `periodicOrbit_apply_eq` / 定理 `periodicOrbit_apply_eq`

English:
theorem periodicOrbit_apply_eq
  given: (hx : x in periodicPts f)
  proof: periodicOrbit_apply_iterate_eq hx 1

中文:
定理 periodicOrbit_apply_eq
  条件: (hx : x in periodicPts f)
  证明: periodicOrbit_apply_iterate_eq hx 1

Depends on / 依赖: periodicOrbit_apply_iterate_eq
-/
theorem periodicOrbit_apply_eq (hx : x in periodicPts f) :
    periodicOrbit f (f x) = periodicOrbit f x :=
  periodicOrbit_apply_iterate_eq hx 1

/--
theorem `periodicOrbit_chain` / 定理 `periodicOrbit_chain`

English:
theorem periodicOrbit_chain
  given: (r : α -> α -> Prop) {f : α -> α} {x : α}
  proof: by
  by_cases hx : x in periodicPts f
  · have hx' := minimalPeriod_pos_of_mem_periodicPts hx
    have hM := Nat.sub_add_cancel (succ_le_iff.2 hx')
    rw [periodicOrbit]; rw [← Cycle.map_coe]; rw [Cycle.chain_map]; rw [← hM]; rw [Cycle.chain_range_succ]
    refine ⟨?_, fun H => ⟨?_, fun m hm => H _

中文:
定理 periodicOrbit_chain
  条件: (r : α -> α -> 命题) {f : α -> α} {x : α}
  证明: by
  by_cases hx : x in periodicPts f
  · have hx' := minimalPeriod_pos_of_mem_periodicPts hx
    have hM := Nat.sub_add_cancel (succ_le_iff.2 hx')
    rw [periodicOrbit]; rw [← Cycle.map_coe]; rw [Cycle.chain_map]; rw [← hM]; rw [Cycle.chain_range_succ]
    refine ⟨?_, fun H => ⟨?_, fun m hm => H _

Depends on / 依赖: Cycle.chain_map, Cycle.chain_range_succ, Cycle.map_coe, Nat.lt_succ_iff, Nat.lt_succ_self, Nat.sub_add_cancel, chain_map, chain_range_succ, eq_or_lt_of_le, hm.trans, iterate_minimalPeriod, iterate_zero_apply, lt_succ_iff, lt_succ_self, map_coe, minimalPeriod_pos_of_mem_periodicPts, nth_rw, periodicOrbit, periodicPts, sub_add_cancel
-/
theorem periodicOrbit_chain (r : α -> α -> Prop) {f : α -> α} {x : α} :
    (periodicOrbit f x).Chain r ↔ forall n < minimalPeriod f x, r (f^[n] x) (f^[n + 1] x) := by
  by_cases hx : x in periodicPts f
  · have hx' := minimalPeriod_pos_of_mem_periodicPts hx
    have hM := Nat.sub_add_cancel (succ_le_iff.2 hx')
    rw [periodicOrbit]; rw [← Cycle.map_coe]; rw [Cycle.chain_map]; rw [← hM]; rw [Cycle.chain_range_succ]
    refine ⟨?_, fun H => ⟨?_, fun m hm => H _ (hm.trans (Nat.lt_succ_self _))⟩⟩
    · rintro ⟨hr, H⟩ n hn
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hn) with hM' | hM'
      · rwa [hM', hM, iterate_minimalPeriod]
      · exact H _ hM'
    · rw [iterate_zero_apply]
      nth_rw 3 [← @iterate_minimalPeriod α f x]
      nth_rw 2 [← hM]
      exact H _ (Nat.lt_succ_self _)
  · rw [periodicOrbit_eq_nil_of_not_periodic_pt hx, minimalPeriod_eq_zero_of_notMem_periodicPts hx]
    simp

/--
theorem `periodicOrbit_chain'` / 定理 `periodicOrbit_chain'`

English:
theorem periodicOrbit_chain'
  given: (r : α -> α -> Prop) {f : α -> α} {x : α} (hx : x in periodicPts f)
  proof: by
  rw [periodicOrbit_chain r]
  refine ⟨fun H n => ?_, fun H n _ => H n⟩
  rw [iterate_succ_apply]; rw [← iterate_mod_minimalPeriod_eq]; rw [← iterate_mod_minimalPeriod_eq (n := n)]; rw [← iterate_succ_apply]; rw [minimalPeriod_apply hx]
  exact H _ (mod_lt _ (minimalPeriod_pos_of_mem_periodicPts 

中文:
定理 periodicOrbit_chain'
  条件: (r : α -> α -> 命题) {f : α -> α} {x : α} (hx : x in periodicPts f)
  证明: by
  rw [periodicOrbit_chain r]
  refine ⟨fun H n => ?_, fun H n _ => H n⟩
  rw [iterate_succ_apply]; rw [← iterate_mod_minimalPeriod_eq]; rw [← iterate_mod_minimalPeriod_eq (n := n)]; rw [← iterate_succ_apply]; rw [minimalPeriod_apply hx]
  exact H _ (mod_lt _ (minimalPeriod_pos_of_mem_periodicPts 

Depends on / 依赖: iterate_mod_minimalPeriod_eq, iterate_succ_apply, minimalPeriod_apply, minimalPeriod_pos_of_mem_periodicPts, mod_lt, periodicOrbit_chain
-/
theorem periodicOrbit_chain' (r : α -> α -> Prop) {f : α -> α} {x : α} (hx : x in periodicPts f) :
    (periodicOrbit f x).Chain r ↔ forall n, r (f^[n] x) (f^[n + 1] x) := by
  rw [periodicOrbit_chain r]
  refine ⟨fun H n => ?_, fun H n _ => H n⟩
  rw [iterate_succ_apply]; rw [← iterate_mod_minimalPeriod_eq]; rw [← iterate_mod_minimalPeriod_eq (n := n)]; rw [← iterate_succ_apply]; rw [minimalPeriod_apply hx]
  exact H _ (mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx))

end -- noncomputable

end Function

namespace Function

section Prod

variable {α β : Type*} {f : α -> α} {g : β -> β} {x : α × β} {a : α} {b : β} {m n : Nat}

@[simp]
/--
theorem `isFixedPt_prodMap` / 定理 `isFixedPt_prodMap`

English:
theorem isFixedPt_prodMap
  given: (x : α × β)
  proof: Prod.ext_iff

中文:
定理 isFixedPt_prodMap
  条件: (x : α × β)
  证明: Prod.ext_iff

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
theorem isFixedPt_prodMap (x : α × β) :
    IsFixedPt (Prod.map f g) x ↔ IsFixedPt f x.1 ∧ IsFixedPt g x.2 :=
  Prod.ext_iff

/--
theorem `IsFixedPt.prodMap` / 定理 `IsFixedPt.prodMap`

English:
theorem IsFixedPt.prodMap
  given: (ha : IsFixedPt f a) (hb : IsFixedPt g b)
  proof: (isFixedPt_prodMap _).mpr ⟨ha, hb⟩

@[simp]

中文:
定理 IsFixedPt.prodMap
  条件: (ha : IsFixedPt f a) (hb : IsFixedPt g b)
  证明: (isFixedPt_prodMap _).mpr ⟨ha, hb⟩

@[simp]

Depends on / 依赖: isFixedPt_prodMap
-/
theorem IsFixedPt.prodMap (ha : IsFixedPt f a) (hb : IsFixedPt g b) :
    IsFixedPt (Prod.map f g) (a, b) :=
  (isFixedPt_prodMap _).mpr ⟨ha, hb⟩

@[simp]
/--
theorem `isPeriodicPt_prodMap` / 定理 `isPeriodicPt_prodMap`

English:
theorem isPeriodicPt_prodMap
  given: (x : α × β)
  proof: by
  simp [IsPeriodicPt]

中文:
定理 isPeriodicPt_prodMap
  条件: (x : α × β)
  证明: by
  simp [IsPeriodicPt]

Depends on / 依赖: IsPeriodicPt
-/
theorem isPeriodicPt_prodMap (x : α × β) :
    IsPeriodicPt (Prod.map f g) n x ↔ IsPeriodicPt f n x.1 ∧ IsPeriodicPt g n x.2 := by
  simp [IsPeriodicPt]

/--
theorem `IsPeriodicPt.prodMap` / 定理 `IsPeriodicPt.prodMap`

English:
theorem IsPeriodicPt.prodMap
  given: (ha : IsPeriodicPt f n a) (hb : IsPeriodicPt g n b)
  proof: (isPeriodicPt_prodMap _).mpr ⟨ha, hb⟩

中文:
定理 IsPeriodicPt.prodMap
  条件: (ha : IsPeriodicPt f n a) (hb : IsPeriodicPt g n b)
  证明: (isPeriodicPt_prodMap _).mpr ⟨ha, hb⟩

Depends on / 依赖: isPeriodicPt_prodMap
-/
theorem IsPeriodicPt.prodMap (ha : IsPeriodicPt f n a) (hb : IsPeriodicPt g n b) :
    IsPeriodicPt (Prod.map f g) n (a, b) :=
  (isPeriodicPt_prodMap _).mpr ⟨ha, hb⟩

end Prod

section Pi

variable {ι : Type*} {α : ι -> Type*} {f : forall i, α i -> α i} {x : forall i, α i} {n : Nat}

@[simp]
/--
theorem `isFixedPt_piMap` / 定理 `isFixedPt_piMap`

English:
theorem isFixedPt_piMap
  statement: IsFixedPt (Pi.map f) x ↔ forall i, IsFixedPt (f i) (x i)
  proof: funext_iff

中文:
定理 isFixedPt_piMap
  结论: IsFixedPt (依赖函数类型.map f) x ↔ 对任意 i, IsFixedPt (f i) (x i)
  证明: funext_iff

Depends on / 依赖: funext_iff
-/
theorem isFixedPt_piMap : IsFixedPt (Pi.map f) x ↔ forall i, IsFixedPt (f i) (x i) :=
  funext_iff

/--
theorem `IsFixedPt.piMap` / 定理 `IsFixedPt.piMap`

English:
theorem IsFixedPt.piMap
  given: (h : forall i, IsFixedPt (f i) (x i))
  statement: IsFixedPt (Pi.map f) x
  proof: isFixedPt_piMap.mpr h

@[simp]

中文:
定理 IsFixedPt.piMap
  条件: (h : 对任意 i, IsFixedPt (f i) (x i))
  结论: IsFixedPt (依赖函数类型.map f) x
  证明: isFixedPt_piMap.mpr h

@[simp]

Depends on / 依赖: isFixedPt_piMap, isFixedPt_piMap.mpr
-/
theorem IsFixedPt.piMap (h : forall i, IsFixedPt (f i) (x i)) : IsFixedPt (Pi.map f) x :=
  isFixedPt_piMap.mpr h

@[simp]
/--
theorem `isPeriodicPt_piMap` / 定理 `isPeriodicPt_piMap`

English:
theorem isPeriodicPt_piMap
  statement: IsPeriodicPt (Pi.map f) n x ↔ forall i, IsPeriodicPt (f i) n (x i)
  proof: by
  simp [IsPeriodicPt]

中文:
定理 isPeriodicPt_piMap
  结论: IsPeriodicPt (依赖函数类型.map f) n x ↔ 对任意 i, IsPeriodicPt (f i) n (x i)
  证明: by
  simp [IsPeriodicPt]

Depends on / 依赖: IsPeriodicPt
-/
theorem isPeriodicPt_piMap : IsPeriodicPt (Pi.map f) n x ↔ forall i, IsPeriodicPt (f i) n (x i) := by
  simp [IsPeriodicPt]

/--
theorem `IsPeriodicPt.piMap` / 定理 `IsPeriodicPt.piMap`

English:
theorem IsPeriodicPt.piMap
  given: (h : forall i, IsPeriodicPt (f i) n (x i))
  statement: IsPeriodicPt (Pi.map f) n x
  proof: isPeriodicPt_piMap.mpr h

中文:
定理 IsPeriodicPt.piMap
  条件: (h : 对任意 i, IsPeriodicPt (f i) n (x i))
  结论: IsPeriodicPt (依赖函数类型.map f) n x
  证明: isPeriodicPt_piMap.mpr h

Depends on / 依赖: isPeriodicPt_piMap, isPeriodicPt_piMap.mpr
-/
theorem IsPeriodicPt.piMap (h : forall i, IsPeriodicPt (f i) n (x i)) : IsPeriodicPt (Pi.map f) n x :=
  isPeriodicPt_piMap.mpr h

end Pi

end Function

namespace MulAction

open Function

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/--
The period of a multiplicative action of `g` on `a` is the smallest positive `n` such that
`g ^ n • a = a`, or `0` if such an `n` does not exist.
-/
@[to_additive /-- The period of an additive action of `g` on `a` is the smallest positive `n`
such that `(n • g) +ᵥ a = a`, or `0` if such an `n` does not exist. -/]
/--
Definition of `period` / `period` 的定义

English:
definition period
  signature: (m : M) (a : α)
  body: minimalPeriod (fun x => m • x) a

中文:
定义 period
  签名: (m : M) (a : α)
  定义体: minimalPeriod (fun x => m • x) a

Depends on / 依赖: minimalPeriod
-/
noncomputable def period (m : M) (a : α) : Nat := minimalPeriod (fun x => m • x) a

/-- `MulAction.period m a` is definitionally equal to `Function.minimalPeriod (m • ·) a`. -/
@[to_additive /-- `AddAction.period m a` is definitionally equal to
`Function.minimalPeriod (m +ᵥ ·) a` -/]
/--
theorem `period_eq_minimalPeriod` / 定理 `period_eq_minimalPeriod`

English:
theorem period_eq_minimalPeriod
  given: {m : M} {a : α}
  proof: rfl

中文:
定理 period_eq_minimalPeriod
  条件: {m : M} {a : α}
  证明: rfl
-/
theorem period_eq_minimalPeriod {m : M} {a : α} :
    MulAction.period m a = minimalPeriod (fun x => m • x) a := rfl

/-- `m ^ (period m a)` fixes `a`. -/
@[to_additive (attr := simp) /-- `(period m a) • m` fixes `a`. -/]
/--
theorem `pow_period_smul` / 定理 `pow_period_smul`

English:
theorem pow_period_smul
  given: (m : M) (a : α)
  statement: m ^ (period m a) • a = a
  proof: by
  rw [period_eq_minimalPeriod]; rw [← smul_iterate_apply]; rw [iterate_minimalPeriod]

@[to_additive]

中文:
定理 pow_period_smul
  条件: (m : M) (a : α)
  结论: m ^ (period m a) • a = a
  证明: by
  rw [period_eq_minimalPeriod]; rw [← smul_iterate_apply]; rw [iterate_minimalPeriod]

@[to_additive]

Depends on / 依赖: iterate_minimalPeriod, period_eq_minimalPeriod, smul_iterate_apply
-/
theorem pow_period_smul (m : M) (a : α) : m ^ (period m a) • a = a := by
  rw [period_eq_minimalPeriod]; rw [← smul_iterate_apply]; rw [iterate_minimalPeriod]

@[to_additive]
/--
lemma `isPeriodicPt_smul_iff` / 引理 `isPeriodicPt_smul_iff`

English:
lemma isPeriodicPt_smul_iff
  given: {m : M} {a : α} {n : Nat}
  proof: by
  rw [← smul_iterate_apply]; rw [IsPeriodicPt]; rw [IsFixedPt]

中文:
引理 isPeriodicPt_smul_iff
  条件: {m : M} {a : α} {n : 自然数}
  证明: by
  rw [← smul_iterate_apply]; rw [IsPeriodicPt]; rw [IsFixedPt]

Depends on / 依赖: IsFixedPt, IsPeriodicPt, smul_iterate_apply
-/
lemma isPeriodicPt_smul_iff {m : M} {a : α} {n : Nat} :
    IsPeriodicPt (m • ·) n a ↔ m ^ n • a = a := by
  rw [← smul_iterate_apply]; rw [IsPeriodicPt]; rw [IsFixedPt]

/-! ### Multiples of `MulAction.period`

It is easy to convince oneself that if `g ^ n • a = a` (resp. `(n • g) +ᵥ a = a`),
then `n` must be a multiple of `period g a`.

This also holds for negative powers/multiples.
-/

@[to_additive]
/--
theorem `pow_smul_eq_iff_period_dvd` / 定理 `pow_smul_eq_iff_period_dvd`

English:
theorem pow_smul_eq_iff_period_dvd
  given: {n : Nat} {m : M} {a : α}
  proof: by
  rw [period_eq_minimalPeriod]; rw [← isPeriodicPt_iff_minimalPeriod_dvd]; rw [isPeriodicPt_smul_iff]

@[to_additive]

中文:
定理 pow_smul_eq_iff_period_dvd
  条件: {n : 自然数} {m : M} {a : α}
  证明: by
  rw [period_eq_minimalPeriod]; rw [← isPeriodicPt_iff_minimalPeriod_dvd]; rw [isPeriodicPt_smul_iff]

@[to_additive]

Depends on / 依赖: isPeriodicPt_iff_minimalPeriod_dvd, isPeriodicPt_smul_iff, period_eq_minimalPeriod
-/
theorem pow_smul_eq_iff_period_dvd {n : Nat} {m : M} {a : α} :
    m ^ n • a = a ↔ period m a ∣ n := by
  rw [period_eq_minimalPeriod]; rw [← isPeriodicPt_iff_minimalPeriod_dvd]; rw [isPeriodicPt_smul_iff]

@[to_additive]
/--
theorem `zpow_smul_eq_iff_period_dvd` / 定理 `zpow_smul_eq_iff_period_dvd`

English:
theorem zpow_smul_eq_iff_period_dvd
  given: {j : Int} {g : G} {a : α}
  proof: by
  match j with
  | (n : Nat) => rw [zpow_natCast, Int.natCast_dvd_natCast, pow_smul_eq_iff_period_dvd]
  | -(n + 1 : Nat) =>
    rw [zpow_neg]; rw [zpow_natCast]; rw [inv_smul_eq_iff]; rw [eq_comm]; rw [Int.dvd_neg]; rw [Int.natCast_dvd_natCast]; rw [pow_smul_eq_iff_period_dvd]

@[to_additive (at

中文:
定理 zpow_smul_eq_iff_period_dvd
  条件: {j : 整数} {g : G} {a : α}
  证明: by
  match j with
  | (n : Nat) => rw [zpow_natCast, Int.natCast_dvd_natCast, pow_smul_eq_iff_period_dvd]
  | -(n + 1 : Nat) =>
    rw [zpow_neg]; rw [zpow_natCast]; rw [inv_smul_eq_iff]; rw [eq_comm]; rw [Int.dvd_neg]; rw [Int.natCast_dvd_natCast]; rw [pow_smul_eq_iff_period_dvd]

@[to_additive (at

Depends on / 依赖: Int.dvd_neg, Int.natCast_dvd_natCast, dvd_neg, eq_comm, equiv.symm, inv_smul_eq_iff, natCast_dvd_natCast, pow_smul_eq_iff_period_dvd, zpow_natCast, zpow_neg
-/
theorem zpow_smul_eq_iff_period_dvd {j : Int} {g : G} {a : α} :
    g ^ j • a = a ↔ (period g a : Int) ∣ j := by
  match j with
  | (n : Nat) => rw [zpow_natCast, Int.natCast_dvd_natCast, pow_smul_eq_iff_period_dvd]
  | -(n + 1 : Nat) =>
    rw [zpow_neg]; rw [zpow_natCast]; rw [inv_smul_eq_iff]; rw [eq_comm]; rw [Int.dvd_neg]; rw [Int.natCast_dvd_natCast]; rw [pow_smul_eq_iff_period_dvd]

@[to_additive (attr := simp)]
/--
theorem `pow_mod_period_smul` / 定理 `pow_mod_period_smul`

English:
theorem pow_mod_period_smul
  given: (n : Nat) {m : M} {a : α}
  proof: by
  conv_rhs => rw [← Nat.mod_add_div n (period m a), pow_add, mul_smul,
    pow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]

中文:
定理 pow_mod_period_smul
  条件: (n : 自然数) {m : M} {a : α}
  证明: by
  conv_rhs => rw [← Nat.mod_add_div n (period m a), pow_add, mul_smul,
    pow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.mod_add_div, conv_rhs, dvd_mul_right, mod_add_div, mul_smul, period, pow_add, pow_smul_eq_iff_period_dvd, pow_smul_eq_iff_period_dvd.mpr
-/
theorem pow_mod_period_smul (n : Nat) {m : M} {a : α} :
    m ^ (n % period m a) • a = m ^ n • a := by
  conv_rhs => rw [← Nat.mod_add_div n (period m a), pow_add, mul_smul,
    pow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]
/--
theorem `zpow_mod_period_smul` / 定理 `zpow_mod_period_smul`

English:
theorem zpow_mod_period_smul
  given: (j : Int) {g : G} {a : α}
  proof: by
  conv_rhs => rw [← Int.emod_add_mul_ediv j (period g a), zpow_add, mul_smul,
    zpow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]

中文:
定理 zpow_mod_period_smul
  条件: (j : 整数) {g : G} {a : α}
  证明: by
  conv_rhs => rw [← Int.emod_add_mul_ediv j (period g a), zpow_add, mul_smul,
    zpow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]

Depends on / 依赖: Int.emod_add_mul_ediv, conv_rhs, dvd_mul_right, emod_add_mul_ediv, mul_smul, period, zpow_add, zpow_smul_eq_iff_period_dvd, zpow_smul_eq_iff_period_dvd.mpr
-/
theorem zpow_mod_period_smul (j : Int) {g : G} {a : α} :
    g ^ (j % (period g a : Int)) • a = g ^ j • a := by
  conv_rhs => rw [← Int.emod_add_mul_ediv j (period g a), zpow_add, mul_smul,
    zpow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]
/--
theorem `pow_add_period_smul` / 定理 `pow_add_period_smul`

English:
theorem pow_add_period_smul
  given: (n : Nat) (m : M) (a : α)
  proof: by
  rw [← pow_mod_period_smul]; rw [Nat.add_mod_right]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]

中文:
定理 pow_add_period_smul
  条件: (n : 自然数) (m : M) (a : α)
  证明: by
  rw [← pow_mod_period_smul]; rw [Nat.add_mod_right]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.add_mod_right, add_mod_right, pow_mod_period_smul
-/
theorem pow_add_period_smul (n : Nat) (m : M) (a : α) :
    m ^ (n + period m a) • a = m ^ n • a := by
  rw [← pow_mod_period_smul]; rw [Nat.add_mod_right]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]
/--
theorem `pow_period_add_smul` / 定理 `pow_period_add_smul`

English:
theorem pow_period_add_smul
  given: (n : Nat) (m : M) (a : α)
  proof: by
  rw [← pow_mod_period_smul]; rw [Nat.add_mod_left]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]

中文:
定理 pow_period_add_smul
  条件: (n : 自然数) (m : M) (a : α)
  证明: by
  rw [← pow_mod_period_smul]; rw [Nat.add_mod_left]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.add_mod_left, add_mod_left, pow_mod_period_smul
-/
theorem pow_period_add_smul (n : Nat) (m : M) (a : α) :
    m ^ (period m a + n) • a = m ^ n • a := by
  rw [← pow_mod_period_smul]; rw [Nat.add_mod_left]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]
/--
theorem `zpow_add_period_smul` / 定理 `zpow_add_period_smul`

English:
theorem zpow_add_period_smul
  given: (i : Int) (g : G) (a : α)
  proof: by
  rw [← zpow_mod_period_smul]; rw [Int.add_emod_right]; rw [zpow_mod_period_smul]

@[to_additive (attr := simp)]

中文:
定理 zpow_add_period_smul
  条件: (i : 整数) (g : G) (a : α)
  证明: by
  rw [← zpow_mod_period_smul]; rw [Int.add_emod_right]; rw [zpow_mod_period_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: Int.add_emod_right, add_emod_right, zpow_mod_period_smul
-/
theorem zpow_add_period_smul (i : Int) (g : G) (a : α) :
    g ^ (i + period g a) • a = g ^ i • a := by
  rw [← zpow_mod_period_smul]; rw [Int.add_emod_right]; rw [zpow_mod_period_smul]

@[to_additive (attr := simp)]
/--
theorem `zpow_period_add_smul` / 定理 `zpow_period_add_smul`

English:
theorem zpow_period_add_smul
  given: (i : Int) (g : G) (a : α)
  proof: by
  rw [← zpow_mod_period_smul]; rw [Int.add_emod_left]; rw [zpow_mod_period_smul]

中文:
定理 zpow_period_add_smul
  条件: (i : 整数) (g : G) (a : α)
  证明: by
  rw [← zpow_mod_period_smul]; rw [Int.add_emod_left]; rw [zpow_mod_period_smul]

Depends on / 依赖: Int.add_emod_left, add_emod_left, zpow_mod_period_smul
-/
theorem zpow_period_add_smul (i : Int) (g : G) (a : α) :
    g ^ (period g a + i) • a = g ^ i • a := by
  rw [← zpow_mod_period_smul]; rw [Int.add_emod_left]; rw [zpow_mod_period_smul]

variable {a : G} {b : α}

@[to_additive]
/--
theorem `pow_smul_eq_iff_minimalPeriod_dvd` / 定理 `pow_smul_eq_iff_minimalPeriod_dvd`

English:
theorem pow_smul_eq_iff_minimalPeriod_dvd
  given: {n : Nat}
  proof: by
  rw [← period_eq_minimalPeriod]; rw [pow_smul_eq_iff_period_dvd]

@[to_additive]

中文:
定理 pow_smul_eq_iff_minimalPeriod_dvd
  条件: {n : 自然数}
  证明: by
  rw [← period_eq_minimalPeriod]; rw [pow_smul_eq_iff_period_dvd]

@[to_additive]

Depends on / 依赖: period_eq_minimalPeriod, pow_smul_eq_iff_period_dvd
-/
theorem pow_smul_eq_iff_minimalPeriod_dvd {n : Nat} :
    a ^ n • b = b ↔ minimalPeriod (a • ·) b ∣ n := by
  rw [← period_eq_minimalPeriod]; rw [pow_smul_eq_iff_period_dvd]

@[to_additive]
/--
theorem `zpow_smul_eq_iff_minimalPeriod_dvd` / 定理 `zpow_smul_eq_iff_minimalPeriod_dvd`

English:
theorem zpow_smul_eq_iff_minimalPeriod_dvd
  given: {n : Int}
  proof: by
  rw [← period_eq_minimalPeriod]; rw [zpow_smul_eq_iff_period_dvd]

中文:
定理 zpow_smul_eq_iff_minimalPeriod_dvd
  条件: {n : 整数}
  证明: by
  rw [← period_eq_minimalPeriod]; rw [zpow_smul_eq_iff_period_dvd]

Depends on / 依赖: period_eq_minimalPeriod, zpow_smul_eq_iff_period_dvd
-/
theorem zpow_smul_eq_iff_minimalPeriod_dvd {n : Int} :
    a ^ n • b = b ↔ (minimalPeriod (a • ·) b : Int) ∣ n := by
  rw [← period_eq_minimalPeriod]; rw [zpow_smul_eq_iff_period_dvd]

variable (a b)

@[to_additive (attr := simp)]
/--
theorem `pow_smul_mod_minimalPeriod` / 定理 `pow_smul_mod_minimalPeriod`

English:
theorem pow_smul_mod_minimalPeriod
  given: (n : Nat)
  proof: by
  rw [← period_eq_minimalPeriod]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]

中文:
定理 pow_smul_mod_minimalPeriod
  条件: (n : 自然数)
  证明: by
  rw [← period_eq_minimalPeriod]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: period_eq_minimalPeriod, pow_mod_period_smul
-/
theorem pow_smul_mod_minimalPeriod (n : Nat) :
    a ^ (n % minimalPeriod (a • ·) b) • b = a ^ n • b := by
  rw [← period_eq_minimalPeriod]; rw [pow_mod_period_smul]

@[to_additive (attr := simp)]
/--
theorem `zpow_smul_mod_minimalPeriod` / 定理 `zpow_smul_mod_minimalPeriod`

English:
theorem zpow_smul_mod_minimalPeriod
  given: (n : Int)
  proof: by
  rw [← period_eq_minimalPeriod]; rw [zpow_mod_period_smul]

中文:
定理 zpow_smul_mod_minimalPeriod
  条件: (n : 整数)
  证明: by
  rw [← period_eq_minimalPeriod]; rw [zpow_mod_period_smul]

Depends on / 依赖: period_eq_minimalPeriod, zpow_mod_period_smul
-/
theorem zpow_smul_mod_minimalPeriod (n : Int) :
    a ^ (n % (minimalPeriod (a • ·) b : Int)) • b = a ^ n • b := by
  rw [← period_eq_minimalPeriod]; rw [zpow_mod_period_smul]

end MulAction
