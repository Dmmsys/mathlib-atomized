/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Congruence modulo multiples and congruence modulo `AddSubgroup.zmultiples _`

In this file we show that in an additive commutative group, the congruence relation `a ≡ b [PMOD p]`
is equivalent to the coercions of `a` and `b` to `G ⧸ AddSubgroup.zmultiples p` being equal.
-/

public section

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G] {a b p : G}

/--
theorem `modEq_iff_eq_mod_zmultiples` / 定理 `modEq_iff_eq_mod_zmultiples`

English:
theorem modEq_iff_eq_mod_zmultiples
  statement: a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) = b
  proof: by
  rw [modEq_comm]
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]

中文:
定理 modEq_iff_eq_mod_zmultiples
  结论: a ≡ b [PMOD p] ↔ (a : G ⧸ 加法子群.zmultiples p) = b
  证明: by
  rw [modEq_comm]
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, QuotientAddGroup, QuotientAddGroup.eq_iff_sub_mem, eq_comm, eq_iff_sub_mem, eq_sub_iff_add_eq, mem_zmultiples_iff, modEq_comm, modEq_iff_eq_add_zsmul, simp_rw
-/
theorem modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) = b := by
  rw [modEq_comm]
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]

/--
theorem `not_modEq_iff_ne_mod_zmultiples` / 定理 `not_modEq_iff_ne_mod_zmultiples`

English:
theorem not_modEq_iff_ne_mod_zmultiples
  proof: modEq_iff_eq_mod_zmultiples.not

中文:
定理 not_modEq_iff_ne_mod_zmultiples
  证明: modEq_iff_eq_mod_zmultiples.not

Depends on / 依赖: modEq_iff_eq_mod_zmultiples, modEq_iff_eq_mod_zmultiples.not
-/
theorem not_modEq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) != b :=
  modEq_iff_eq_mod_zmultiples.not

end AddCommGroup
