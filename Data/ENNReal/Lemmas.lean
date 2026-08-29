/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Some lemmas on extended non-negative reals

These are some lemmas split off from `ENNReal.Basic` because they need a lot more imports.
They are probably good targets for further cleanup or moves.
-/

public section


open Function Set NNReal

variable {α : Type*}

namespace ENNReal

@[simp, norm_cast]
/--
theorem `coe_indicator` / 定理 `coe_indicator`

English:
theorem coe_indicator
  given: {α} (s : Set α) (f : α -> Real>=0) (a : α)
  proof: map_indicator ofNNRealHom _ _ _

中文:
定理 coe_indicator
  条件: {α} (s : Set α) (f : α -> 实数>=0) (a : α)
  证明: map_indicator ofNNRealHom _ _ _

Depends on / 依赖: map_indicator, ofNNRealHom
-/
theorem coe_indicator {α} (s : Set α) (f : α -> Real>=0) (a : α) :
    ((s.indicator f a : Real>=0) : Real>=0∞) = s.indicator (fun x => ↑(f x)) a :=
  map_indicator ofNNRealHom _ _ _

section Order

@[simp, norm_cast]
/--
theorem `coe_finset_sup` / 定理 `coe_finset_sup`

English:
theorem coe_finset_sup
  given: {s : Finset α} {f : α -> Real>=0}
  statement: ↑(s.sup f) = s.sup fun x => (f x : Real>=0∞)
  proof: Finset.apply_sup_eq_sup_comp_of_linearOrder _ coe_mono rfl

中文:
定理 coe_finset_sup
  条件: {s : Finset α} {f : α -> 实数>=0}
  结论: ↑(s.sup f) = s.sup fun x => (f x : 实数>=0∞)
  证明: Finset.apply_sup_eq_sup_comp_of_linearOrder _ coe_mono rfl

Depends on / 依赖: Finset, Finset.apply_sup_eq_sup_comp_of_linearOrder, apply_sup_eq_sup_comp_of_linearOrder, coe_mono
-/
theorem coe_finset_sup {s : Finset α} {f : α -> Real>=0} : ↑(s.sup f) = s.sup fun x => (f x : Real>=0∞) :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder _ coe_mono rfl

end Order

end ENNReal
