/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Torsion group of `ZMod p` for prime `p`

This file shows that the `ZMod p` has `p - 1` roots-of-unity.

-/

public section

namespace ZMod

/--
lemma `rootsOfUnity_eq_top` / 引理 `rootsOfUnity_eq_top`

English:
lemma rootsOfUnity_eq_top
  given: {p : Nat} [Fact p.Prime]
  proof: by
  ext
  simpa [Units.ext_iff] using pow_card_sub_one_eq_one (Units.ne_zero _)

中文:
引理 rootsOfUnity_eq_top
  条件: {p : 自然数} [Fact p.素]
  证明: by
  ext
  simpa [Units.ext_iff] using pow_card_sub_one_eq_one (Units.ne_zero _)

Depends on / 依赖: Units.ext_iff, Units.ne_zero, ext_iff, ne_zero, pow_card_sub_one_eq_one
-/
lemma rootsOfUnity_eq_top {p : Nat} [Fact p.Prime] :
    (rootsOfUnity (p - 1) (ZMod p)) = ⊤ := by
  ext
  simpa [Units.ext_iff] using pow_card_sub_one_eq_one (Units.ne_zero _)

instance {p : Nat} [Fact p.Prime] : HasEnoughRootsOfUnity (ZMod p) (p - 1) := by
  have : NeZero (p - 1) := ⟨by have : 2 <= p := Nat.Prime.two_le Fact.out; grind⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have := Nat.card_congr (MulEquiv.subgroupCongr (ZMod.rootsOfUnity_eq_top (p := p))).toEquiv
  rw [this]
  simp [Fintype.card_units]

end ZMod
