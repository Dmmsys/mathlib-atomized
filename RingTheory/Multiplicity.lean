/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes, Daniel Weber
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multiplicity of a divisor

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `emultiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity a b`: a `ℕ`-valued version of `multiplicity`, defaulting for `1` instead of `⊤`.
  The reason for using `1` as a default value instead of `0` is to have `multiplicity_eq_zero_iff`.
* `FiniteMultiplicity a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/

@[expose] public section

assert_not_exists Field

variable {α β : Type*}

open Nat

/--
Definition of `FiniteMultiplicity` / `FiniteMultiplicity` 的定义

English:
abbreviation FiniteMultiplicity
  signature: [Monoid α] (a b : α)
  body: exists n : Nat, ¬a ^ (n + 1) ∣ b

中文:
缩写 FiniteMultiplicity
  签名: [Monoid α] (a b : α)
  定义体: exists n : Nat, ¬a ^ (n + 1) ∣ b

Depends on / 依赖: MulAction
-/
abbrev FiniteMultiplicity [Monoid α] (a b : α) : Prop :=
  exists n : Nat, ¬a ^ (n + 1) ∣ b

open scoped Classical in
/--
Definition of `emultiplicity` / `emultiplicity` 的定义

English:
definition emultiplicity
  signature: [Monoid α] (a b : α)
  body: if h : FiniteMultiplicity a b then Nat.find h else ⊤

中文:
定义 emultiplicity
  签名: [Monoid α] (a b : α)
  定义体: if h : FiniteMultiplicity a b then Nat.find h else ⊤

Depends on / 依赖: DistribMulAction, FiniteMultiplicity, Nat.find
-/
noncomputable def emultiplicity [Monoid α] (a b : α) : Nat∞ :=
  if h : FiniteMultiplicity a b then Nat.find h else ⊤

/--
Definition of `multiplicity` / `multiplicity` 的定义

English:
definition multiplicity
  signature: [Monoid α] (a b : α)
  body: (emultiplicity a b).untopD 1

中文:
定义 multiplicity
  签名: [Monoid α] (a b : α)
  定义体: (emultiplicity a b).untopD 1

Depends on / 依赖: DistribMulAction, emultiplicity, untopD
-/
noncomputable def multiplicity [Monoid α] (a b : α) : Nat :=
  (emultiplicity a b).untopD 1

section Monoid

variable [Monoid α] [Monoid β] {a b : α}

@[simp]
/--
theorem `emultiplicity_eq_top` / 定理 `emultiplicity_eq_top`

English:
theorem emultiplicity_eq_top
  proof: by
  simp [emultiplicity]

中文:
定理 emultiplicity_eq_top
  证明: by
  simp [emultiplicity]

Depends on / 依赖: emultiplicity
-/
theorem emultiplicity_eq_top :
    emultiplicity a b = ⊤ ↔ ¬FiniteMultiplicity a b := by
  simp [emultiplicity]

/--
theorem `emultiplicity_lt_top` / 定理 `emultiplicity_lt_top`

English:
theorem emultiplicity_lt_top
  given: {a b : α}
  statement: emultiplicity a b < ⊤ ↔ FiniteMultiplicity a b
  proof: by
  simp [lt_top_iff_ne_top, emultiplicity_eq_top]

中文:
定理 emultiplicity_lt_top
  条件: {a b : α}
  结论: emultiplicity a b < ⊤ ↔ FiniteMultiplicity a b
  证明: by
  simp [lt_top_iff_ne_top, emultiplicity_eq_top]

Depends on / 依赖: emultiplicity_eq_top, lt_top_iff_ne_top
-/
theorem emultiplicity_lt_top {a b : α} : emultiplicity a b < ⊤ ↔ FiniteMultiplicity a b := by
  simp [lt_top_iff_ne_top, emultiplicity_eq_top]

/--
theorem `finiteMultiplicity_iff_emultiplicity_ne_top` / 定理 `finiteMultiplicity_iff_emultiplicity_ne_top`

English:
theorem finiteMultiplicity_iff_emultiplicity_ne_top
  proof: by simp

中文:
定理 finiteMultiplicity_iff_emultiplicity_ne_top
  证明: by simp
-/
theorem finiteMultiplicity_iff_emultiplicity_ne_top :
    FiniteMultiplicity a b ↔ emultiplicity a b != ⊤ := by simp

/--
theorem `finiteMultiplicity_of_emultiplicity_eq_natCast` / 定理 `finiteMultiplicity_of_emultiplicity_eq_natCast`

English:
theorem finiteMultiplicity_of_emultiplicity_eq_natCast
  given: {n : Nat} (h : emultiplicity a b = n)
  proof: by
  by_contra nh
  rw [← emultiplicity_eq_top]; rw [h] at nh
  trivial

中文:
定理 finiteMultiplicity_of_emultiplicity_eq_natCast
  条件: {n : 自然数} (h : emultiplicity a b = n)
  证明: by
  by_contra nh
  rw [← emultiplicity_eq_top]; rw [h] at nh
  trivial

Depends on / 依赖: emultiplicity_eq_top
-/
theorem finiteMultiplicity_of_emultiplicity_eq_natCast {n : Nat} (h : emultiplicity a b = n) :
    FiniteMultiplicity a b := by
  by_contra nh
  rw [← emultiplicity_eq_top]; rw [h] at nh
  trivial

/--
theorem `multiplicity_eq_of_emultiplicity_eq_some` / 定理 `multiplicity_eq_of_emultiplicity_eq_some`

English:
theorem multiplicity_eq_of_emultiplicity_eq_some
  given: {n : Nat} (h : emultiplicity a b = n)
  proof: by
  simp [multiplicity, h]
  rfl

中文:
定理 multiplicity_eq_of_emultiplicity_eq_some
  条件: {n : 自然数} (h : emultiplicity a b = n)
  证明: by
  simp [multiplicity, h]
  rfl

Depends on / 依赖: multiplicity
-/
theorem multiplicity_eq_of_emultiplicity_eq_some {n : Nat} (h : emultiplicity a b = n) :
    multiplicity a b = n := by
  simp [multiplicity, h]
  rfl

/--
theorem `emultiplicity_ne_of_multiplicity_ne` / 定理 `emultiplicity_ne_of_multiplicity_ne`

English:
theorem emultiplicity_ne_of_multiplicity_ne
  given: {n : Nat}
  proof: mt multiplicity_eq_of_emultiplicity_eq_some

中文:
定理 emultiplicity_ne_of_multiplicity_ne
  条件: {n : 自然数}
  证明: mt multiplicity_eq_of_emultiplicity_eq_some

Depends on / 依赖: multiplicity_eq_of_emultiplicity_eq_some
-/
theorem emultiplicity_ne_of_multiplicity_ne {n : Nat} :
    multiplicity a b != n -> emultiplicity a b != n :=
  mt multiplicity_eq_of_emultiplicity_eq_some

/--
theorem `FiniteMultiplicity.emultiplicity_eq_multiplicity` / 定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`

English:
theorem FiniteMultiplicity.emultiplicity_eq_multiplicity
  given: (h : FiniteMultiplicity a b)
  proof: by
  cases hm : emultiplicity a b
  · simp [h] at hm
  rw [multiplicity_eq_of_emultiplicity_eq_some hm]

中文:
定理 FiniteMultiplicity.emultiplicity_eq_multiplicity
  条件: (h : FiniteMultiplicity a b)
  证明: by
  cases hm : emultiplicity a b
  · simp [h] at hm
  rw [multiplicity_eq_of_emultiplicity_eq_some hm]

Depends on / 依赖: emultiplicity, multiplicity_eq_of_emultiplicity_eq_some
-/
theorem FiniteMultiplicity.emultiplicity_eq_multiplicity (h : FiniteMultiplicity a b) :
    emultiplicity a b = multiplicity a b := by
  cases hm : emultiplicity a b
  · simp [h] at hm
  rw [multiplicity_eq_of_emultiplicity_eq_some hm]

/--
theorem `FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq` / 定理 `FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq`

English:
theorem FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq
  statement: {n : Nat}
  proof: by
  simp [h.emultiplicity_eq_multiplicity]

中文:
定理 FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq
  结论: {n : 自然数}
  证明: by
  simp [h.emultiplicity_eq_multiplicity]

Depends on / 依赖: emultiplicity_eq_multiplicity, h.emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq {n : Nat}
    (h : FiniteMultiplicity a b) : emultiplicity a b = n ↔ multiplicity a b = n := by
  simp [h.emultiplicity_eq_multiplicity]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `emultiplicity_eq_iff_multiplicity_eq_of_ne_one` / 定理 `emultiplicity_eq_iff_multiplicity_eq_of_ne_one`

English:
theorem emultiplicity_eq_iff_multiplicity_eq_of_ne_one
  given: {n : Nat} (h : n != 1)
  proof: by
  constructor
  · exact multiplicity_eq_of_emultiplicity_eq_some
  · intro h₂
    simpa [multiplicity, WithTop.untopD_eq_iff, h] using! h₂

中文:
定理 emultiplicity_eq_iff_multiplicity_eq_of_ne_one
  条件: {n : 自然数} (h : n != 1)
  证明: by
  constructor
  · exact multiplicity_eq_of_emultiplicity_eq_some
  · intro h₂
    simpa [multiplicity, WithTop.untopD_eq_iff, h] using! h₂

Depends on / 依赖: WithTop, WithTop.untopD_eq_iff, multiplicity, multiplicity_eq_of_emultiplicity_eq_some, untopD_eq_iff
-/
theorem emultiplicity_eq_iff_multiplicity_eq_of_ne_one {n : Nat} (h : n != 1) :
    emultiplicity a b = n ↔ multiplicity a b = n := by
  constructor
  · exact multiplicity_eq_of_emultiplicity_eq_some
  · intro h₂
    simpa [multiplicity, WithTop.untopD_eq_iff, h] using! h₂

/--
theorem `emultiplicity_eq_zero_iff_multiplicity_eq_zero` / 定理 `emultiplicity_eq_zero_iff_multiplicity_eq_zero`

English:
theorem emultiplicity_eq_zero_iff_multiplicity_eq_zero
  proof: emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one

@[simp]

中文:
定理 emultiplicity_eq_zero_iff_multiplicity_eq_zero
  证明: emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one

@[simp]

Depends on / 依赖: emultiplicity_eq_iff_multiplicity_eq_of_ne_one, zero_ne_one
-/
theorem emultiplicity_eq_zero_iff_multiplicity_eq_zero :
    emultiplicity a b = 0 ↔ multiplicity a b = 0 :=
  emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one

@[simp]
/--
theorem `multiplicity_eq_one_of_not_finiteMultiplicity` / 定理 `multiplicity_eq_one_of_not_finiteMultiplicity`

English:
theorem multiplicity_eq_one_of_not_finiteMultiplicity
  given: (h : ¬FiniteMultiplicity a b)
  proof: by
  rw [multiplicity]; rw [emultiplicity_eq_top.mpr h]
  decide

@[simp]

中文:
定理 multiplicity_eq_one_of_not_finiteMultiplicity
  条件: (h : ¬FiniteMultiplicity a b)
  证明: by
  rw [multiplicity]; rw [emultiplicity_eq_top.mpr h]
  decide

@[simp]

Depends on / 依赖: Nontrivial, T0Space, emultiplicity_eq_top, emultiplicity_eq_top.mpr, multiplicity
-/
theorem multiplicity_eq_one_of_not_finiteMultiplicity (h : ¬FiniteMultiplicity a b) :
    multiplicity a b = 1 := by
  rw [multiplicity]; rw [emultiplicity_eq_top.mpr h]
  decide

@[simp]
/--
theorem `multiplicity_le_emultiplicity` / 定理 `multiplicity_le_emultiplicity`

English:
theorem multiplicity_le_emultiplicity
  proof: by
  by_cases hf : FiniteMultiplicity a b
  · simp [hf.emultiplicity_eq_multiplicity]
  · simp [hf, emultiplicity_eq_top.2]

中文:
定理 multiplicity_le_emultiplicity
  证明: by
  by_cases hf : FiniteMultiplicity a b
  · simp [hf.emultiplicity_eq_multiplicity]
  · simp [hf, emultiplicity_eq_top.2]

Depends on / 依赖: FiniteMultiplicity, emultiplicity_eq_multiplicity, emultiplicity_eq_top, hf.emultiplicity_eq_multiplicity
-/
theorem multiplicity_le_emultiplicity :
    multiplicity a b <= emultiplicity a b := by
  by_cases hf : FiniteMultiplicity a b
  · simp [hf.emultiplicity_eq_multiplicity]
  · simp [hf, emultiplicity_eq_top.2]

-- Cannot be @[simp] because `β`, `c`, and `d` cannot be inferred by `simp`.
/--
theorem `multiplicity_eq_of_emultiplicity_eq` / 定理 `multiplicity_eq_of_emultiplicity_eq`

English:
theorem multiplicity_eq_of_emultiplicity_eq
  statement: {c d : β}
  proof: by
  unfold multiplicity
  rw [h]

中文:
定理 multiplicity_eq_of_emultiplicity_eq
  结论: {c d : β}
  证明: by
  unfold multiplicity
  rw [h]

Depends on / 依赖: multiplicity
-/
theorem multiplicity_eq_of_emultiplicity_eq {c d : β}
    (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = multiplicity c d := by
  unfold multiplicity
  rw [h]

/--
theorem `multiplicity_le_of_emultiplicity_le` / 定理 `multiplicity_le_of_emultiplicity_le`

English:
theorem multiplicity_le_of_emultiplicity_le
  given: {n : Nat} (h : emultiplicity a b <= n)
  proof: by
  exact_mod_cast multiplicity_le_emultiplicity.trans h

中文:
定理 multiplicity_le_of_emultiplicity_le
  条件: {n : 自然数} (h : emultiplicity a b <= n)
  证明: by
  exact_mod_cast multiplicity_le_emultiplicity.trans h

Depends on / 依赖: multiplicity_le_emultiplicity, multiplicity_le_emultiplicity.trans
-/
theorem multiplicity_le_of_emultiplicity_le {n : Nat} (h : emultiplicity a b <= n) :
    multiplicity a b <= n := by
  exact_mod_cast multiplicity_le_emultiplicity.trans h

/--
theorem `FiniteMultiplicity.emultiplicity_le_of_multiplicity_le` / 定理 `FiniteMultiplicity.emultiplicity_le_of_multiplicity_le`

English:
theorem FiniteMultiplicity.emultiplicity_le_of_multiplicity_le
  statement: (hfin : FiniteMultiplicity a b)
  proof: by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

中文:
定理 FiniteMultiplicity.emultiplicity_le_of_multiplicity_le
  结论: (hfin : FiniteMultiplicity a b)
  证明: by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

Depends on / 依赖: assumption_mod_cast, emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.emultiplicity_le_of_multiplicity_le (hfin : FiniteMultiplicity a b)
    {n : Nat} (h : multiplicity a b <= n) : emultiplicity a b <= n := by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

/--
theorem `le_emultiplicity_of_le_multiplicity` / 定理 `le_emultiplicity_of_le_multiplicity`

English:
theorem le_emultiplicity_of_le_multiplicity
  given: {n : Nat} (h : n <= multiplicity a b)
  proof: by
  exact_mod_cast (WithTop.coe_mono h).trans multiplicity_le_emultiplicity

中文:
定理 le_emultiplicity_of_le_multiplicity
  条件: {n : 自然数} (h : n <= multiplicity a b)
  证明: by
  exact_mod_cast (WithTop.coe_mono h).trans multiplicity_le_emultiplicity

Depends on / 依赖: WithTop, WithTop.coe_mono, coe_mono, multiplicity_le_emultiplicity
-/
theorem le_emultiplicity_of_le_multiplicity {n : Nat} (h : n <= multiplicity a b) :
    n <= emultiplicity a b := by
  exact_mod_cast (WithTop.coe_mono h).trans multiplicity_le_emultiplicity

/--
theorem `FiniteMultiplicity.le_multiplicity_of_le_emultiplicity` / 定理 `FiniteMultiplicity.le_multiplicity_of_le_emultiplicity`

English:
theorem FiniteMultiplicity.le_multiplicity_of_le_emultiplicity
  statement: (hfin : FiniteMultiplicity a b)
  proof: by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

中文:
定理 FiniteMultiplicity.le_multiplicity_of_le_emultiplicity
  结论: (hfin : FiniteMultiplicity a b)
  证明: by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

Depends on / 依赖: assumption_mod_cast, emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.le_multiplicity_of_le_emultiplicity (hfin : FiniteMultiplicity a b)
    {n : Nat} (h : n <= emultiplicity a b) : n <= multiplicity a b := by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

/--
theorem `multiplicity_lt_of_emultiplicity_lt` / 定理 `multiplicity_lt_of_emultiplicity_lt`

English:
theorem multiplicity_lt_of_emultiplicity_lt
  given: {n : Nat} (h : emultiplicity a b < n)
  proof: by
  exact_mod_cast multiplicity_le_emultiplicity.trans_lt h

中文:
定理 multiplicity_lt_of_emultiplicity_lt
  条件: {n : 自然数} (h : emultiplicity a b < n)
  证明: by
  exact_mod_cast multiplicity_le_emultiplicity.trans_lt h

Depends on / 依赖: multiplicity_le_emultiplicity, multiplicity_le_emultiplicity.trans_lt, trans_lt
-/
theorem multiplicity_lt_of_emultiplicity_lt {n : Nat} (h : emultiplicity a b < n) :
    multiplicity a b < n := by
  exact_mod_cast multiplicity_le_emultiplicity.trans_lt h

/--
theorem `FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt` / 定理 `FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt`

English:
theorem FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt
  statement: (hfin : FiniteMultiplicity a b)
  proof: by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

中文:
定理 FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt
  结论: (hfin : FiniteMultiplicity a b)
  证明: by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

Depends on / 依赖: assumption_mod_cast, emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt (hfin : FiniteMultiplicity a b)
    {n : Nat} (h : multiplicity a b < n) : emultiplicity a b < n := by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

/--
theorem `lt_emultiplicity_of_lt_multiplicity` / 定理 `lt_emultiplicity_of_lt_multiplicity`

English:
theorem lt_emultiplicity_of_lt_multiplicity
  given: {n : Nat} (h : n < multiplicity a b)
  proof: by
  exact_mod_cast (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity

中文:
定理 lt_emultiplicity_of_lt_multiplicity
  条件: {n : 自然数} (h : n < multiplicity a b)
  证明: by
  exact_mod_cast (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity

Depends on / 依赖: WithTop, WithTop.coe_strictMono, coe_strictMono, multiplicity_le_emultiplicity, trans_le
-/
theorem lt_emultiplicity_of_lt_multiplicity {n : Nat} (h : n < multiplicity a b) :
    n < emultiplicity a b := by
  exact_mod_cast (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity

/--
theorem `FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity` / 定理 `FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity`

English:
theorem FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity
  statement: (hfin : FiniteMultiplicity a b)
  proof: by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

中文:
定理 FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity
  结论: (hfin : FiniteMultiplicity a b)
  证明: by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

Depends on / 依赖: UniformSpace, assumption_mod_cast, completableTopField_of_complete, emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity (hfin : FiniteMultiplicity a b)
    {n : Nat} (h : n < emultiplicity a b) : n < multiplicity a b := by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

/--
theorem `emultiplicity_pos_iff` / 定理 `emultiplicity_pos_iff`

English:
theorem emultiplicity_pos_iff
  proof: by
  simp [pos_iff_ne_zero, pos_iff_ne_zero, emultiplicity_eq_zero_iff_multiplicity_eq_zero]

中文:
定理 emultiplicity_pos_iff
  证明: by
  simp [pos_iff_ne_zero, pos_iff_ne_zero, emultiplicity_eq_zero_iff_multiplicity_eq_zero]

Depends on / 依赖: emultiplicity_eq_zero_iff_multiplicity_eq_zero, pos_iff_ne_zero
-/
theorem emultiplicity_pos_iff :
    0 < emultiplicity a b ↔ 0 < multiplicity a b := by
  simp [pos_iff_ne_zero, pos_iff_ne_zero, emultiplicity_eq_zero_iff_multiplicity_eq_zero]

/--
theorem `FiniteMultiplicity.def` / 定理 `FiniteMultiplicity.def`

English:
theorem FiniteMultiplicity.def
  statement: FiniteMultiplicity a b ↔ exists n : Nat, ¬a ^ (n + 1) ∣ b
  proof: Iff.rfl

中文:
定理 FiniteMultiplicity.def
  结论: FiniteMultiplicity a b ↔ 存在 n : 自然数, ¬a ^ (n + 1) ∣ b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem FiniteMultiplicity.def : FiniteMultiplicity a b ↔ exists n : Nat, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl

/--
theorem `FiniteMultiplicity.not_dvd_of_one_right` / 定理 `FiniteMultiplicity.not_dvd_of_one_right`

English:
theorem FiniteMultiplicity.not_dvd_of_one_right
  statement: FiniteMultiplicity a 1 -> ¬a ∣ 1
  proof: fun ⟨n, hn⟩ ⟨d, hd⟩ => hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]

中文:
定理 FiniteMultiplicity.not_dvd_of_one_right
  结论: FiniteMultiplicity a 1 -> ¬a ∣ 1
  证明: fun ⟨n, hn⟩ ⟨d, hd⟩ => hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]

Depends on / 依赖: hd.symm, pow_mul_pow_eq_one
-/
theorem FiniteMultiplicity.not_dvd_of_one_right : FiniteMultiplicity a 1 -> ¬a ∣ 1 :=
  fun ⟨n, hn⟩ ⟨d, hd⟩ => hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]
/--
theorem `Int.natCast_emultiplicity` / 定理 `Int.natCast_emultiplicity`

English:
theorem Int.natCast_emultiplicity
  given: (a b : Nat)
  proof: by
  unfold emultiplicity FiniteMultiplicity
  congr! <;> norm_cast

@[norm_cast]

中文:
定理 Int.natCast_emultiplicity
  条件: (a b : 自然数)
  证明: by
  unfold emultiplicity FiniteMultiplicity
  congr! <;> norm_cast

@[norm_cast]

Depends on / 依赖: FiniteMultiplicity, emultiplicity
-/
theorem Int.natCast_emultiplicity (a b : Nat) :
    emultiplicity (a : Int) (b : Int) = emultiplicity a b := by
  unfold emultiplicity FiniteMultiplicity
  congr! <;> norm_cast

@[norm_cast]
/--
theorem `Int.natCast_multiplicity` / 定理 `Int.natCast_multiplicity`

English:
theorem Int.natCast_multiplicity
  given: (a b : Nat)
  statement: multiplicity (a : Int) (b : Int) = multiplicity a b
  proof: multiplicity_eq_of_emultiplicity_eq (natCast_emultiplicity a b)

中文:
定理 Int.natCast_multiplicity
  条件: (a b : 自然数)
  结论: multiplicity (a : 整数) (b : 整数) = multiplicity a b
  证明: multiplicity_eq_of_emultiplicity_eq (natCast_emultiplicity a b)

Depends on / 依赖: multiplicity_eq_of_emultiplicity_eq, natCast_emultiplicity
-/
theorem Int.natCast_multiplicity (a b : Nat) : multiplicity (a : Int) (b : Int) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (natCast_emultiplicity a b)

/--
theorem `FiniteMultiplicity.not_iff_forall` / 定理 `FiniteMultiplicity.not_iff_forall`

English:
theorem FiniteMultiplicity.not_iff_forall
  statement: ¬FiniteMultiplicity a b ↔ forall n : Nat, a ^ n ∣ b
  proof: ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [_root_.pow_zero]
        exact one_dvd _)
      (by simpa [FiniteMultiplicity] using h),
    by simp [FiniteMultiplicity]; tauto⟩

中文:
定理 FiniteMultiplicity.not_iff_forall
  结论: ¬FiniteMultiplicity a b ↔ 对任意 n : 自然数, a ^ n ∣ b
  证明: ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [_root_.pow_zero]
        exact one_dvd _)
      (by simpa [FiniteMultiplicity] using h),
    by simp [FiniteMultiplicity]; tauto⟩

Depends on / 依赖: FiniteMultiplicity, Nat.casesOn, _root_, _root_.pow_zero, casesOn, one_dvd, pow_zero
-/
theorem FiniteMultiplicity.not_iff_forall : ¬FiniteMultiplicity a b ↔ forall n : Nat, a ^ n ∣ b :=
  ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [_root_.pow_zero]
        exact one_dvd _)
      (by simpa [FiniteMultiplicity] using h),
    by simp [FiniteMultiplicity]; tauto⟩

/--
theorem `FiniteMultiplicity.not_isUnit` / 定理 `FiniteMultiplicity.not_isUnit`

English:
theorem FiniteMultiplicity.not_isUnit
  given: (h : FiniteMultiplicity a b)
  statement: ¬IsUnit a
  proof: let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)

@[deprecated (since := "2026-08-02")]
alias FiniteMultiplicity.not_unit := FiniteMultiplicity.not_isUnit

中文:
定理 FiniteMultiplicity.not_isUnit
  条件: (h : FiniteMultiplicity a b)
  结论: ¬IsUnit a
  证明: let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)

@[deprecated (since := "2026-08-02")]
alias FiniteMultiplicity.not_unit := FiniteMultiplicity.not_isUnit

Depends on / 依赖: IsUnit, IsUnit.dvd, IsUnit.pow
-/
theorem FiniteMultiplicity.not_isUnit (h : FiniteMultiplicity a b) : ¬IsUnit a :=
  let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)

@[deprecated (since := "2026-08-02")]
alias FiniteMultiplicity.not_unit := FiniteMultiplicity.not_isUnit

/--
theorem `FiniteMultiplicity.mul_left` / 定理 `FiniteMultiplicity.mul_left`

English:
theorem FiniteMultiplicity.mul_left
  given: {c : α}
  proof: fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩

中文:
定理 FiniteMultiplicity.mul_left
  条件: {c : α}
  证明: fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩

Depends on / 依赖: UniformContinuousConstSMul, UniformContinuousConstSMul.instContinuousConstSMul, instContinuousConstSMul
-/
theorem FiniteMultiplicity.mul_left {c : α} :
    FiniteMultiplicity a (b * c) -> FiniteMultiplicity a b := fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩

/--
theorem `pow_dvd_of_le_emultiplicity` / 定理 `pow_dvd_of_le_emultiplicity`

English:
theorem pow_dvd_of_le_emultiplicity
  given: {k : Nat} (hk : k <= emultiplicity a b)
  proof: by classical
  cases k
  · simp
  unfold emultiplicity at hk
  split at hk
  · norm_cast at hk
    simpa using (Nat.find_min _ (lt_of_succ_le hk))
  · apply FiniteMultiplicity.not_iff_forall.mp ‹_›

中文:
定理 pow_dvd_of_le_emultiplicity
  条件: {k : 自然数} (hk : k <= emultiplicity a b)
  证明: by classical
  cases k
  · simp
  unfold emultiplicity at hk
  split at hk
  · norm_cast at hk
    simpa using (Nat.find_min _ (lt_of_succ_le hk))
  · apply FiniteMultiplicity.not_iff_forall.mp ‹_›

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.not_iff_forall.mp, Nat.find_min, classical, emultiplicity, find_min, lt_of_succ_le, not_iff_forall
-/
theorem pow_dvd_of_le_emultiplicity {k : Nat} (hk : k <= emultiplicity a b) :
    a ^ k ∣ b := by classical
  cases k
  · simp
  unfold emultiplicity at hk
  split at hk
  · norm_cast at hk
    simpa using (Nat.find_min _ (lt_of_succ_le hk))
  · apply FiniteMultiplicity.not_iff_forall.mp ‹_›

/--
theorem `pow_dvd_of_le_multiplicity` / 定理 `pow_dvd_of_le_multiplicity`

English:
theorem pow_dvd_of_le_multiplicity
  given: {k : Nat} (hk : k <= multiplicity a b)
  proof: pow_dvd_of_le_emultiplicity (le_emultiplicity_of_le_multiplicity hk)

@[simp]

中文:
定理 pow_dvd_of_le_multiplicity
  条件: {k : 自然数} (hk : k <= multiplicity a b)
  证明: pow_dvd_of_le_emultiplicity (le_emultiplicity_of_le_multiplicity hk)

@[simp]

Depends on / 依赖: le_emultiplicity_of_le_multiplicity, pow_dvd_of_le_emultiplicity
-/
theorem pow_dvd_of_le_multiplicity {k : Nat} (hk : k <= multiplicity a b) :
    a ^ k ∣ b := pow_dvd_of_le_emultiplicity (le_emultiplicity_of_le_multiplicity hk)

@[simp]
/--
theorem `pow_multiplicity_dvd` / 定理 `pow_multiplicity_dvd`

English:
theorem pow_multiplicity_dvd
  given: (a b : α)
  statement: a ^ (multiplicity a b) ∣ b
  proof: pow_dvd_of_le_multiplicity le_rfl

中文:
定理 pow_multiplicity_dvd
  条件: (a b : α)
  结论: a ^ (multiplicity a b) ∣ b
  证明: pow_dvd_of_le_multiplicity le_rfl

Depends on / 依赖: IsCentralScalar, UniformContinuousConstSMul, UniformContinuousConstSMul.op, le_rfl, pow_dvd_of_le_multiplicity
-/
theorem pow_multiplicity_dvd (a b : α) : a ^ (multiplicity a b) ∣ b :=
  pow_dvd_of_le_multiplicity le_rfl

/--
theorem `not_pow_dvd_of_emultiplicity_lt` / 定理 `not_pow_dvd_of_emultiplicity_lt`

English:
theorem not_pow_dvd_of_emultiplicity_lt
  given: {m : Nat} (hm : emultiplicity a b < m)
  proof: fun nh => by
  unfold emultiplicity at hm
  split at hm
  · simp only [cast_lt, find_lt_iff] at hm
    obtain ⟨n, hn1, hn2⟩ := hm
    exact hn2 ((pow_dvd_pow _ hn1).trans nh)
  · simp at hm

中文:
定理 not_pow_dvd_of_emultiplicity_lt
  条件: {m : 自然数} (hm : emultiplicity a b < m)
  证明: fun nh => by
  unfold emultiplicity at hm
  split at hm
  · simp only [cast_lt, find_lt_iff] at hm
    obtain ⟨n, hn1, hn2⟩ := hm
    exact hn2 ((pow_dvd_pow _ hn1).trans nh)
  · simp at hm

Depends on / 依赖: cast_lt, emultiplicity, find_lt_iff, pow_dvd_pow
-/
theorem not_pow_dvd_of_emultiplicity_lt {m : Nat} (hm : emultiplicity a b < m) :
    ¬a ^ m ∣ b := fun nh => by
  unfold emultiplicity at hm
  split at hm
  · simp only [cast_lt, find_lt_iff] at hm
    obtain ⟨n, hn1, hn2⟩ := hm
    exact hn2 ((pow_dvd_pow _ hn1).trans nh)
  · simp at hm

/--
theorem `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt` / 定理 `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`

English:
theorem FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
  statement: (hf : FiniteMultiplicity a b) {m : Nat}
  proof: by
  apply not_pow_dvd_of_emultiplicity_lt
  rw [hf.emultiplicity_eq_multiplicity]
  norm_cast

中文:
定理 FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
  结论: (hf : FiniteMultiplicity a b) {m : 自然数}
  证明: by
  apply not_pow_dvd_of_emultiplicity_lt
  rw [hf.emultiplicity_eq_multiplicity]
  norm_cast

Depends on / 依赖: emultiplicity_eq_multiplicity, hf.emultiplicity_eq_multiplicity, not_pow_dvd_of_emultiplicity_lt
-/
theorem FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : Nat}
    (hm : multiplicity a b < m) : ¬a ^ m ∣ b := by
  apply not_pow_dvd_of_emultiplicity_lt
  rw [hf.emultiplicity_eq_multiplicity]
  norm_cast

/--
theorem `multiplicity_pos_of_dvd` / 定理 `multiplicity_pos_of_dvd`

English:
theorem multiplicity_pos_of_dvd
  given: (hdiv : a ∣ b)
  statement: 0 < multiplicity a b
  proof: by
  refine Nat.pos_iff_ne_zero.2 fun h => ?_
  simpa [hdiv] using FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
    (by by_contra! nh; simp [nh] at h) (lt_one_iff.mpr h)

中文:
定理 multiplicity_pos_of_dvd
  条件: (hdiv : a ∣ b)
  结论: 0 < multiplicity a b
  证明: by
  refine Nat.pos_iff_ne_zero.2 fun h => ?_
  simpa [hdiv] using FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
    (by by_contra! nh; simp [nh] at h) (lt_one_iff.mpr h)

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt, Nat.pos_iff_ne_zero, lt_one_iff, lt_one_iff.mpr, not_pow_dvd_of_multiplicity_lt, pos_iff_ne_zero
-/
theorem multiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < multiplicity a b := by
  refine Nat.pos_iff_ne_zero.2 fun h => ?_
  simpa [hdiv] using FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
    (by by_contra! nh; simp [nh] at h) (lt_one_iff.mpr h)

/--
theorem `emultiplicity_pos_of_dvd` / 定理 `emultiplicity_pos_of_dvd`

English:
theorem emultiplicity_pos_of_dvd
  given: (hdiv : a ∣ b)
  statement: 0 < emultiplicity a b
  proof: lt_emultiplicity_of_lt_multiplicity (multiplicity_pos_of_dvd hdiv)

中文:
定理 emultiplicity_pos_of_dvd
  条件: (hdiv : a ∣ b)
  结论: 0 < emultiplicity a b
  证明: lt_emultiplicity_of_lt_multiplicity (multiplicity_pos_of_dvd hdiv)

Depends on / 依赖: lt_emultiplicity_of_lt_multiplicity, multiplicity_pos_of_dvd
-/
theorem emultiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < emultiplicity a b :=
  lt_emultiplicity_of_lt_multiplicity (multiplicity_pos_of_dvd hdiv)

/--
theorem `emultiplicity_eq_of_dvd_of_not_dvd` / 定理 `emultiplicity_eq_of_dvd_of_not_dvd`

English:
theorem emultiplicity_eq_of_dvd_of_not_dvd
  given: {k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b)
  proof: by classical
  have : FiniteMultiplicity a b := ⟨k, hsucc⟩
  simp only [emultiplicity, this, ↓reduceDIte, Nat.cast_inj, find_eq_iff, hsucc, not_false_eq_true,
    Decidable.not_not, true_and]
  exact fun n hn => (pow_dvd_pow _ hn).trans hk

中文:
定理 emultiplicity_eq_of_dvd_of_not_dvd
  条件: {k : 自然数} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b)
  证明: by classical
  have : FiniteMultiplicity a b := ⟨k, hsucc⟩
  simp only [emultiplicity, this, ↓reduceDIte, Nat.cast_inj, find_eq_iff, hsucc, not_false_eq_true,
    Decidable.not_not, true_and]
  exact fun n hn => (pow_dvd_pow _ hn).trans hk

Depends on / 依赖: Decidable, Decidable.not_not, FiniteMultiplicity, Nat.cast_inj, cast_inj, classical, emultiplicity, find_eq_iff, not_false_eq_true, not_not, pow_dvd_pow, reduceDIte, true_and
-/
theorem emultiplicity_eq_of_dvd_of_not_dvd {k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    emultiplicity a b = k := by classical
  have : FiniteMultiplicity a b := ⟨k, hsucc⟩
  simp only [emultiplicity, this, ↓reduceDIte, Nat.cast_inj, find_eq_iff, hsucc, not_false_eq_true,
    Decidable.not_not, true_and]
  exact fun n hn => (pow_dvd_pow _ hn).trans hk

/--
theorem `multiplicity_eq_of_dvd_of_not_dvd` / 定理 `multiplicity_eq_of_dvd_of_not_dvd`

English:
theorem multiplicity_eq_of_dvd_of_not_dvd
  given: {k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b)
  proof: multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_of_dvd_of_not_dvd hk hsucc)

中文:
定理 multiplicity_eq_of_dvd_of_not_dvd
  条件: {k : 自然数} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b)
  证明: multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_of_dvd_of_not_dvd hk hsucc)

Depends on / 依赖: emultiplicity_eq_of_dvd_of_not_dvd, multiplicity_eq_of_emultiplicity_eq_some
-/
theorem multiplicity_eq_of_dvd_of_not_dvd {k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    multiplicity a b = k :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_of_dvd_of_not_dvd hk hsucc)

/--
theorem `le_emultiplicity_of_pow_dvd` / 定理 `le_emultiplicity_of_pow_dvd`

English:
theorem le_emultiplicity_of_pow_dvd
  given: {k : Nat} (hk : a ^ k ∣ b)
  proof: le_of_not_gt fun hk' => not_pow_dvd_of_emultiplicity_lt hk' hk

中文:
定理 le_emultiplicity_of_pow_dvd
  条件: {k : 自然数} (hk : a ^ k ∣ b)
  证明: le_of_not_gt fun hk' => not_pow_dvd_of_emultiplicity_lt hk' hk

Depends on / 依赖: le_of_not_gt, not_pow_dvd_of_emultiplicity_lt
-/
theorem le_emultiplicity_of_pow_dvd {k : Nat} (hk : a ^ k ∣ b) :
    k <= emultiplicity a b :=
  le_of_not_gt fun hk' => not_pow_dvd_of_emultiplicity_lt hk' hk

/--
theorem `FiniteMultiplicity.le_multiplicity_of_pow_dvd` / 定理 `FiniteMultiplicity.le_multiplicity_of_pow_dvd`

English:
theorem FiniteMultiplicity.le_multiplicity_of_pow_dvd
  statement: (hf : FiniteMultiplicity a b)
  proof: hf.le_multiplicity_of_le_emultiplicity (le_emultiplicity_of_pow_dvd hk)

中文:
定理 FiniteMultiplicity.le_multiplicity_of_pow_dvd
  结论: (hf : FiniteMultiplicity a b)
  证明: hf.le_multiplicity_of_le_emultiplicity (le_emultiplicity_of_pow_dvd hk)

Depends on / 依赖: hf.le_multiplicity_of_le_emultiplicity, le_emultiplicity_of_pow_dvd, le_multiplicity_of_le_emultiplicity
-/
theorem FiniteMultiplicity.le_multiplicity_of_pow_dvd (hf : FiniteMultiplicity a b)
    {k : Nat} (hk : a ^ k ∣ b) : k <= multiplicity a b :=
  hf.le_multiplicity_of_le_emultiplicity (le_emultiplicity_of_pow_dvd hk)

/--
theorem `pow_dvd_iff_le_emultiplicity` / 定理 `pow_dvd_iff_le_emultiplicity`

English:
theorem pow_dvd_iff_le_emultiplicity
  given: {k : Nat}
  proof: ⟨le_emultiplicity_of_pow_dvd, pow_dvd_of_le_emultiplicity⟩

中文:
定理 pow_dvd_iff_le_emultiplicity
  条件: {k : 自然数}
  证明: ⟨le_emultiplicity_of_pow_dvd, pow_dvd_of_le_emultiplicity⟩

Depends on / 依赖: le_emultiplicity_of_pow_dvd, pow_dvd_of_le_emultiplicity
-/
theorem pow_dvd_iff_le_emultiplicity {k : Nat} :
    a ^ k ∣ b ↔ k <= emultiplicity a b :=
  ⟨le_emultiplicity_of_pow_dvd, pow_dvd_of_le_emultiplicity⟩

/--
theorem `FiniteMultiplicity.pow_dvd_iff_le_multiplicity` / 定理 `FiniteMultiplicity.pow_dvd_iff_le_multiplicity`

English:
theorem FiniteMultiplicity.pow_dvd_iff_le_multiplicity
  given: (hf : FiniteMultiplicity a b) {k : Nat}
  proof: by
  exact_mod_cast hf.emultiplicity_eq_multiplicity ▸ pow_dvd_iff_le_emultiplicity

中文:
定理 FiniteMultiplicity.pow_dvd_iff_le_multiplicity
  条件: (hf : FiniteMultiplicity a b) {k : 自然数}
  证明: by
  exact_mod_cast hf.emultiplicity_eq_multiplicity ▸ pow_dvd_iff_le_emultiplicity

Depends on / 依赖: emultiplicity_eq_multiplicity, hf.emultiplicity_eq_multiplicity, pow_dvd_iff_le_emultiplicity
-/
theorem FiniteMultiplicity.pow_dvd_iff_le_multiplicity (hf : FiniteMultiplicity a b) {k : Nat} :
    a ^ k ∣ b ↔ k <= multiplicity a b := by
  exact_mod_cast hf.emultiplicity_eq_multiplicity ▸ pow_dvd_iff_le_emultiplicity

/--
theorem `emultiplicity_lt_iff_not_dvd` / 定理 `emultiplicity_lt_iff_not_dvd`

English:
theorem emultiplicity_lt_iff_not_dvd
  given: {k : Nat}
  proof: by rw [pow_dvd_iff_le_emultiplicity, not_le]

中文:
定理 emultiplicity_lt_iff_not_dvd
  条件: {k : 自然数}
  证明: by rw [pow_dvd_iff_le_emultiplicity, not_le]

Depends on / 依赖: not_le, pow_dvd_iff_le_emultiplicity
-/
theorem emultiplicity_lt_iff_not_dvd {k : Nat} :
    emultiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [pow_dvd_iff_le_emultiplicity, not_le]

/--
theorem `FiniteMultiplicity.multiplicity_lt_iff_not_dvd` / 定理 `FiniteMultiplicity.multiplicity_lt_iff_not_dvd`

English:
theorem FiniteMultiplicity.multiplicity_lt_iff_not_dvd
  given: {k : Nat} (hf : FiniteMultiplicity a b)
  proof: by rw [hf.pow_dvd_iff_le_multiplicity, not_le]

中文:
定理 FiniteMultiplicity.multiplicity_lt_iff_not_dvd
  条件: {k : 自然数} (hf : FiniteMultiplicity a b)
  证明: by rw [hf.pow_dvd_iff_le_multiplicity, not_le]

Depends on / 依赖: hf.pow_dvd_iff_le_multiplicity, not_le, pow_dvd_iff_le_multiplicity
-/
theorem FiniteMultiplicity.multiplicity_lt_iff_not_dvd {k : Nat} (hf : FiniteMultiplicity a b) :
    multiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [hf.pow_dvd_iff_le_multiplicity, not_le]

/--
theorem `emultiplicity_eq_coe` / 定理 `emultiplicity_eq_coe`

English:
theorem emultiplicity_eq_coe
  given: {n : Nat}
  proof: by
  constructor
  · intro h
    constructor
    · apply pow_dvd_of_le_emultiplicity
      simp [h]
    · apply not_pow_dvd_of_emultiplicity_lt
      rw [h]
      norm_cast
      simp
  · rw [and_imp]
    apply emultiplicity_eq_of_dvd_of_not_dvd

中文:
定理 emultiplicity_eq_coe
  条件: {n : 自然数}
  证明: by
  constructor
  · intro h
    constructor
    · apply pow_dvd_of_le_emultiplicity
      simp [h]
    · apply not_pow_dvd_of_emultiplicity_lt
      rw [h]
      norm_cast
      simp
  · rw [and_imp]
    apply emultiplicity_eq_of_dvd_of_not_dvd

Depends on / 依赖: and_imp, emultiplicity_eq_of_dvd_of_not_dvd, not_pow_dvd_of_emultiplicity_lt, pow_dvd_of_le_emultiplicity
-/
theorem emultiplicity_eq_coe {n : Nat} :
    emultiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  constructor
  · intro h
    constructor
    · apply pow_dvd_of_le_emultiplicity
      simp [h]
    · apply not_pow_dvd_of_emultiplicity_lt
      rw [h]
      norm_cast
      simp
  · rw [and_imp]
    apply emultiplicity_eq_of_dvd_of_not_dvd

/--
theorem `FiniteMultiplicity.multiplicity_eq_iff` / 定理 `FiniteMultiplicity.multiplicity_eq_iff`

English:
theorem FiniteMultiplicity.multiplicity_eq_iff
  given: (hf : FiniteMultiplicity a b) {n : Nat}
  proof: by
  simp [← emultiplicity_eq_coe, hf.emultiplicity_eq_multiplicity]

中文:
定理 FiniteMultiplicity.multiplicity_eq_iff
  条件: (hf : FiniteMultiplicity a b) {n : 自然数}
  证明: by
  simp [← emultiplicity_eq_coe, hf.emultiplicity_eq_multiplicity]

Depends on / 依赖: emultiplicity_eq_coe, emultiplicity_eq_multiplicity, hf.emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.multiplicity_eq_iff (hf : FiniteMultiplicity a b) {n : Nat} :
    multiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  simp [← emultiplicity_eq_coe, hf.emultiplicity_eq_multiplicity]

/--
theorem `emultiplicity_eq_ofNat` / 定理 `emultiplicity_eq_ofNat`

English:
theorem emultiplicity_eq_ofNat
  given: {a b n : Nat} [n.AtLeastTwo]
  proof: emultiplicity_eq_coe

@[simp]

中文:
定理 emultiplicity_eq_ofNat
  条件: {a b n : 自然数} [n.AtLeastTwo]
  证明: emultiplicity_eq_coe

@[simp]

Depends on / 依赖: emultiplicity_eq_coe
-/
theorem emultiplicity_eq_ofNat {a b n : Nat} [n.AtLeastTwo] :
    emultiplicity a b = (ofNat(n) : Nat∞) ↔ a ^ ofNat(n) ∣ b ∧ ¬a ^ (ofNat(n) + 1) ∣ b :=
  emultiplicity_eq_coe

@[simp]
/--
theorem `FiniteMultiplicity.not_of_isUnit_left` / 定理 `FiniteMultiplicity.not_of_isUnit_left`

English:
theorem FiniteMultiplicity.not_of_isUnit_left
  given: (b : α) (ha : IsUnit a)
  statement: ¬FiniteMultiplicity a b
  proof: (·.not_isUnit ha)

中文:
定理 FiniteMultiplicity.not_of_isUnit_left
  条件: (b : α) (ha : IsUnit a)
  结论: ¬FiniteMultiplicity a b
  证明: (·.not_isUnit ha)

Depends on / 依赖: not_isUnit
-/
theorem FiniteMultiplicity.not_of_isUnit_left (b : α) (ha : IsUnit a) : ¬FiniteMultiplicity a b :=
  (·.not_isUnit ha)

/--
theorem `FiniteMultiplicity.not_of_one_left` / 定理 `FiniteMultiplicity.not_of_one_left`

English:
theorem FiniteMultiplicity.not_of_one_left
  given: (b : α)
  statement: ¬ FiniteMultiplicity 1 b
  proof: by simp

@[simp]

中文:
定理 FiniteMultiplicity.not_of_one_left
  条件: (b : α)
  结论: ¬ FiniteMultiplicity 1 b
  证明: by simp

@[simp]
-/
theorem FiniteMultiplicity.not_of_one_left (b : α) : ¬ FiniteMultiplicity 1 b := by simp

@[simp]
/--
theorem `emultiplicity_one_left` / 定理 `emultiplicity_one_left`

English:
theorem emultiplicity_one_left
  given: (b : α)
  statement: emultiplicity 1 b = ⊤
  proof: emultiplicity_eq_top.2 (FiniteMultiplicity.not_of_one_left _)

@[simp]

中文:
定理 emultiplicity_one_left
  条件: (b : α)
  结论: emultiplicity 1 b = ⊤
  证明: emultiplicity_eq_top.2 (FiniteMultiplicity.not_of_one_left _)

@[simp]

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.not_of_one_left, emultiplicity_eq_top, not_of_one_left
-/
theorem emultiplicity_one_left (b : α) : emultiplicity 1 b = ⊤ :=
  emultiplicity_eq_top.2 (FiniteMultiplicity.not_of_one_left _)

@[simp]
/--
theorem `FiniteMultiplicity.one_right` / 定理 `FiniteMultiplicity.one_right`

English:
theorem FiniteMultiplicity.one_right
  given: (ha : FiniteMultiplicity a 1)
  statement: multiplicity a 1 = 0
  proof: by
  simp [ha.multiplicity_eq_iff, ha.not_dvd_of_one_right]

中文:
定理 FiniteMultiplicity.one_right
  条件: (ha : FiniteMultiplicity a 1)
  结论: multiplicity a 1 = 0
  证明: by
  simp [ha.multiplicity_eq_iff, ha.not_dvd_of_one_right]

Depends on / 依赖: ha.multiplicity_eq_iff, ha.not_dvd_of_one_right, multiplicity_eq_iff, not_dvd_of_one_right
-/
theorem FiniteMultiplicity.one_right (ha : FiniteMultiplicity a 1) : multiplicity a 1 = 0 := by
  simp [ha.multiplicity_eq_iff, ha.not_dvd_of_one_right]

/--
theorem `FiniteMultiplicity.not_of_unit_left` / 定理 `FiniteMultiplicity.not_of_unit_left`

English:
theorem FiniteMultiplicity.not_of_unit_left
  given: (a : α) (u : αˣ)
  statement: ¬ FiniteMultiplicity (u : α) a
  proof: FiniteMultiplicity.not_of_isUnit_left a u.isUnit

中文:
定理 FiniteMultiplicity.not_of_unit_left
  条件: (a : α) (u : αˣ)
  结论: ¬ FiniteMultiplicity (u : α) a
  证明: FiniteMultiplicity.not_of_isUnit_left a u.isUnit

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.not_of_isUnit_left, isUnit, not_of_isUnit_left, u.isUnit
-/
theorem FiniteMultiplicity.not_of_unit_left (a : α) (u : αˣ) : ¬ FiniteMultiplicity (u : α) a :=
  FiniteMultiplicity.not_of_isUnit_left a u.isUnit

/--
theorem `emultiplicity_eq_zero` / 定理 `emultiplicity_eq_zero`

English:
theorem emultiplicity_eq_zero
  proof: by
  by_cases hf : FiniteMultiplicity a b
  · rw [← ENat.natCast_zero, emultiplicity_eq_coe]
    simp
  · simpa [emultiplicity_eq_top.2 hf] using FiniteMultiplicity.not_iff_forall.1 hf 1

中文:
定理 emultiplicity_eq_zero
  证明: by
  by_cases hf : FiniteMultiplicity a b
  · rw [← ENat.natCast_zero, emultiplicity_eq_coe]
    simp
  · simpa [emultiplicity_eq_top.2 hf] using FiniteMultiplicity.not_iff_forall.1 hf 1

Depends on / 依赖: ENat.natCast_zero, FiniteMultiplicity, FiniteMultiplicity.not_iff_forall, emultiplicity_eq_coe, emultiplicity_eq_top, natCast_zero, not_iff_forall
-/
theorem emultiplicity_eq_zero :
    emultiplicity a b = 0 ↔ ¬a ∣ b := by
  by_cases hf : FiniteMultiplicity a b
  · rw [← ENat.natCast_zero, emultiplicity_eq_coe]
    simp
  · simpa [emultiplicity_eq_top.2 hf] using FiniteMultiplicity.not_iff_forall.1 hf 1

/--
theorem `emultiplicity_eq_zero_of_irreducible_ne` / 定理 `emultiplicity_eq_zero_of_irreducible_ne`

English:
theorem emultiplicity_eq_zero_of_irreducible_ne
  statement: {R : Type*} [CommMonoidWithZero R]
  proof: emultiplicity_eq_zero.2 ((ha.dvd_irreducible_iff_associated hb).not.2 fun ⟨u, _⟩ => by
    simp_all [Subsingleton.elim u 1])

中文:
定理 emultiplicity_eq_zero_of_irreducible_ne
  结论: {R : 类型} [CommMonoidWithZero R]
  证明: emultiplicity_eq_zero.2 ((ha.dvd_irreducible_iff_associated hb).not.2 fun ⟨u, _⟩ => by
    simp_all [Subsingleton.elim u 1])

Depends on / 依赖: Subsingleton, Subsingleton.elim, dvd_irreducible_iff_associated, emultiplicity_eq_zero, ha.dvd_irreducible_iff_associated
-/
theorem emultiplicity_eq_zero_of_irreducible_ne {R : Type*} [CommMonoidWithZero R]
    [Subsingleton Rˣ] {a b : R} (ha : Irreducible a) (hb : Irreducible b) (h : a != b) :
    emultiplicity a b = 0 :=
  emultiplicity_eq_zero.2 ((ha.dvd_irreducible_iff_associated hb).not.2 fun ⟨u, _⟩ => by
    simp_all [Subsingleton.elim u 1])

/--
theorem `multiplicity_eq_zero` / 定理 `multiplicity_eq_zero`

English:
theorem multiplicity_eq_zero
  proof: (emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one).symm.trans emultiplicity_eq_zero

中文:
定理 multiplicity_eq_zero
  证明: (emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one).symm.trans emultiplicity_eq_zero

Depends on / 依赖: emultiplicity_eq_iff_multiplicity_eq_of_ne_one, emultiplicity_eq_zero, symm.trans, zero_ne_one
-/
theorem multiplicity_eq_zero :
    multiplicity a b = 0 ↔ ¬a ∣ b :=
  (emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one).symm.trans emultiplicity_eq_zero

/--
theorem `emultiplicity_ne_zero` / 定理 `emultiplicity_ne_zero`

English:
theorem emultiplicity_ne_zero
  proof: by
  simp [emultiplicity_eq_zero]

中文:
定理 emultiplicity_ne_zero
  证明: by
  simp [emultiplicity_eq_zero]

Depends on / 依赖: emultiplicity_eq_zero
-/
theorem emultiplicity_ne_zero :
    emultiplicity a b != 0 ↔ a ∣ b := by
  simp [emultiplicity_eq_zero]

/--
theorem `multiplicity_ne_zero` / 定理 `multiplicity_ne_zero`

English:
theorem multiplicity_ne_zero
  proof: by
  simp [multiplicity_eq_zero]

中文:
定理 multiplicity_ne_zero
  证明: by
  simp [multiplicity_eq_zero]

Depends on / 依赖: multiplicity_eq_zero
-/
theorem multiplicity_ne_zero :
    multiplicity a b != 0 ↔ a ∣ b := by
  simp [multiplicity_eq_zero]

/--
theorem `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd` / 定理 `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd`

English:
theorem FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd
  given: (hfin : FiniteMultiplicity a b)
  proof: by
  obtain ⟨c, hc⟩ := pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk]; rw [← mul_assoc]; rw [← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact (hfin.multiplicity_eq_iff.1 (by simp)).2 h₁

中文:
定理 FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd
  条件: (hfin : FiniteMultiplicity a b)
  证明: by
  obtain ⟨c, hc⟩ := pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk]; rw [← mul_assoc]; rw [← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact (hfin.multiplicity_eq_iff.1 (by simp)).2 h₁

Depends on / 依赖: _root_, _root_.pow_succ, hfin.multiplicity_eq_iff, mul_assoc, multiplicity, multiplicity_eq_iff, pow_multiplicity_dvd, pow_succ
-/
theorem FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicity a b) :
    exists c : α, b = a ^ multiplicity a b * c ∧ ¬a ∣ c := by
  obtain ⟨c, hc⟩ := pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk]; rw [← mul_assoc]; rw [← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact (hfin.multiplicity_eq_iff.1 (by simp)).2 h₁

/--
theorem `emultiplicity_le_emultiplicity_iff` / 定理 `emultiplicity_le_emultiplicity_iff`

English:
theorem emultiplicity_le_emultiplicity_iff
  given: {c d : β}
  proof: by classical
  constructor
  · exact fun h n hab => pow_dvd_of_le_emultiplicity (le_trans (le_emultiplicity_of_pow_dvd hab) h)
  · intro h
    unfold emultiplicity
    -- aesop? says
    split
    next h_1 =>
      obtain ⟨w, h_1⟩ := h_1
      split
      next h_2 =>
        simp_all only [cast_le, 

中文:
定理 emultiplicity_le_emultiplicity_iff
  条件: {c d : β}
  证明: by classical
  constructor
  · exact fun h n hab => pow_dvd_of_le_emultiplicity (le_trans (le_emultiplicity_of_pow_dvd hab) h)
  · intro h
    unfold emultiplicity
    -- aesop? says
    split
    next h_1 =>
      obtain ⟨w, h_1⟩ := h_1
      split
      next h_2 =>
        simp_all only [cast_le, 

Depends on / 依赖: classical, emultiplicity, le_emultiplicity_of_pow_dvd, le_trans, pow_dvd_of_le_emultiplicity
-/
theorem emultiplicity_le_emultiplicity_iff {c d : β} :
    emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b -> c ^ n ∣ d := by classical
  constructor
  · exact fun h n hab => pow_dvd_of_le_emultiplicity (le_trans (le_emultiplicity_of_pow_dvd hab) h)
  · intro h
    unfold emultiplicity
    -- aesop? says
    split
    next h_1 =>
      obtain ⟨w, h_1⟩ := h_1
      split
      next h_2 =>
        simp_all only [cast_le, le_find_iff, lt_find_iff, Decidable.not_not, le_refl,
          not_true_eq_false, not_false_eq_true, implies_true]
      next h_2 => simp_all only [not_exists, Decidable.not_not, le_top]
    next h_1 =>
      simp_all only [not_exists, Decidable.not_not, not_true_eq_false, top_le_iff,
        dite_eq_right_iff, ENat.natCast_ne_top, imp_false, not_false_eq_true, implies_true]

/--
theorem `FiniteMultiplicity.multiplicity_le_multiplicity_iff` / 定理 `FiniteMultiplicity.multiplicity_le_multiplicity_iff`

English:
theorem FiniteMultiplicity.multiplicity_le_multiplicity_iff
  statement: {c d : β} (hab : FiniteMultiplicity a b)
  proof: by
  rw [← ENat.natCast_le_natCast]; rw [← hab.emultiplicity_eq_multiplicity]; rw [← hcd.emultiplicity_eq_multiplicity]; rw [emultiplicity_le_emultiplicity_iff]

中文:
定理 FiniteMultiplicity.multiplicity_le_multiplicity_iff
  结论: {c d : β} (hab : FiniteMultiplicity a b)
  证明: by
  rw [← ENat.natCast_le_natCast]; rw [← hab.emultiplicity_eq_multiplicity]; rw [← hcd.emultiplicity_eq_multiplicity]; rw [emultiplicity_le_emultiplicity_iff]

Depends on / 依赖: ENat.natCast_le_natCast, emultiplicity_eq_multiplicity, emultiplicity_le_emultiplicity_iff, hab.emultiplicity_eq_multiplicity, hcd.emultiplicity_eq_multiplicity, natCast_le_natCast
-/
theorem FiniteMultiplicity.multiplicity_le_multiplicity_iff {c d : β} (hab : FiniteMultiplicity a b)
    (hcd : FiniteMultiplicity c d) :
    multiplicity a b <= multiplicity c d ↔ forall n : Nat, a ^ n ∣ b -> c ^ n ∣ d := by
  rw [← ENat.natCast_le_natCast]; rw [← hab.emultiplicity_eq_multiplicity]; rw [← hcd.emultiplicity_eq_multiplicity]; rw [emultiplicity_le_emultiplicity_iff]

/--
theorem `emultiplicity_eq_emultiplicity_iff` / 定理 `emultiplicity_eq_emultiplicity_iff`

English:
theorem emultiplicity_eq_emultiplicity_iff
  given: {c d : β}
  proof: ⟨fun h n =>
    ⟨emultiplicity_le_emultiplicity_iff.1 h.le n, emultiplicity_le_emultiplicity_iff.1 h.ge n⟩,
    fun h => le_antisymm (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mp)
      (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mpr)⟩

中文:
定理 emultiplicity_eq_emultiplicity_iff
  条件: {c d : β}
  证明: ⟨fun h n =>
    ⟨emultiplicity_le_emultiplicity_iff.1 h.le n, emultiplicity_le_emultiplicity_iff.1 h.ge n⟩,
    fun h => le_antisymm (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mp)
      (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mpr)⟩

Depends on / 依赖: emultiplicity_le_emultiplicity_iff, h.ge, h.le, le_antisymm
-/
theorem emultiplicity_eq_emultiplicity_iff {c d : β} :
    emultiplicity a b = emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ↔ c ^ n ∣ d :=
  ⟨fun h n =>
    ⟨emultiplicity_le_emultiplicity_iff.1 h.le n, emultiplicity_le_emultiplicity_iff.1 h.ge n⟩,
    fun h => le_antisymm (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mp)
      (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mpr)⟩

/--
theorem `le_emultiplicity_map` / 定理 `le_emultiplicity_map`

English:
theorem le_emultiplicity_map
  statement: {F : Type*} [FunLike F α β] [MonoidHomClass F α β]
  proof: emultiplicity_le_emultiplicity_iff.2 fun n => by rw [← map_pow]; exact map_dvd f

中文:
定理 le_emultiplicity_map
  结论: {F : 类型} [FunLike F α β] [MonoidHomClass F α β]
  证明: emultiplicity_le_emultiplicity_iff.2 fun n => by rw [← map_pow]; exact map_dvd f

Depends on / 依赖: emultiplicity_le_emultiplicity_iff, map_dvd, map_pow
-/
theorem le_emultiplicity_map {F : Type*} [FunLike F α β] [MonoidHomClass F α β]
    (f : F) {a b : α} :
    emultiplicity a b <= emultiplicity (f a) (f b) :=
  emultiplicity_le_emultiplicity_iff.2 fun n => by rw [← map_pow]; exact map_dvd f

/--
theorem `emultiplicity_map_eq` / 定理 `emultiplicity_map_eq`

English:
theorem emultiplicity_map_eq
  statement: {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
  proof: by
  simp [emultiplicity_eq_emultiplicity_iff, ← map_pow, map_dvd_iff]

中文:
定理 emultiplicity_map_eq
  结论: {F : 类型} [EquivLike F α β] [MulEquivClass F α β]
  证明: by
  simp [emultiplicity_eq_emultiplicity_iff, ← map_pow, map_dvd_iff]

Depends on / 依赖: emultiplicity_eq_emultiplicity_iff, map_dvd_iff, map_pow
-/
theorem emultiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : emultiplicity (f a) (f b) = emultiplicity a b := by
  simp [emultiplicity_eq_emultiplicity_iff, ← map_pow, map_dvd_iff]

/--
theorem `multiplicity_map_eq` / 定理 `multiplicity_map_eq`

English:
theorem multiplicity_map_eq
  statement: {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
  proof: multiplicity_eq_of_emultiplicity_eq (emultiplicity_map_eq f)

中文:
定理 multiplicity_map_eq
  结论: {F : 类型} [EquivLike F α β] [MulEquivClass F α β]
  证明: multiplicity_eq_of_emultiplicity_eq (emultiplicity_map_eq f)

Depends on / 依赖: emultiplicity_map_eq, multiplicity_eq_of_emultiplicity_eq
-/
theorem multiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : multiplicity (f a) (f b) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_map_eq f)

/--
theorem `emultiplicity_le_emultiplicity_of_dvd_right` / 定理 `emultiplicity_le_emultiplicity_of_dvd_right`

English:
theorem emultiplicity_le_emultiplicity_of_dvd_right
  given: {a b c : α} (h : b ∣ c)
  proof: emultiplicity_le_emultiplicity_iff.2 fun _ hb => hb.trans h

中文:
定理 emultiplicity_le_emultiplicity_of_dvd_right
  条件: {a b c : α} (h : b ∣ c)
  证明: emultiplicity_le_emultiplicity_iff.2 fun _ hb => hb.trans h

Depends on / 依赖: emultiplicity_le_emultiplicity_iff, hb.trans
-/
theorem emultiplicity_le_emultiplicity_of_dvd_right {a b c : α} (h : b ∣ c) :
    emultiplicity a b <= emultiplicity a c :=
  emultiplicity_le_emultiplicity_iff.2 fun _ hb => hb.trans h

/--
theorem `emultiplicity_eq_of_associated_right` / 定理 `emultiplicity_eq_of_associated_right`

English:
theorem emultiplicity_eq_of_associated_right
  given: {a b c : α} (h : Associated b c)
  proof: le_antisymm (emultiplicity_le_emultiplicity_of_dvd_right h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_right h.symm.dvd)

中文:
定理 emultiplicity_eq_of_associated_right
  条件: {a b c : α} (h : Associated b c)
  证明: le_antisymm (emultiplicity_le_emultiplicity_of_dvd_right h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_right h.symm.dvd)

Depends on / 依赖: emultiplicity_le_emultiplicity_of_dvd_right, h.dvd, h.symm.dvd, le_antisymm
-/
theorem emultiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) :
    emultiplicity a b = emultiplicity a c :=
  le_antisymm (emultiplicity_le_emultiplicity_of_dvd_right h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_right h.symm.dvd)

/--
theorem `multiplicity_eq_of_associated_right` / 定理 `multiplicity_eq_of_associated_right`

English:
theorem multiplicity_eq_of_associated_right
  given: {a b c : α} (h : Associated b c)
  proof: multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_right h)

中文:
定理 multiplicity_eq_of_associated_right
  条件: {a b c : α} (h : Associated b c)
  证明: multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_right h)

Depends on / 依赖: emultiplicity_eq_of_associated_right, multiplicity_eq_of_emultiplicity_eq
-/
theorem multiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) :
    multiplicity a b = multiplicity a c :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_right h)

/--
theorem `dvd_of_emultiplicity_pos` / 定理 `dvd_of_emultiplicity_pos`

English:
theorem dvd_of_emultiplicity_pos
  given: {a b : α} (h : 0 < emultiplicity a b)
  statement: a ∣ b
  proof: pow_one a ▸ pow_dvd_of_le_emultiplicity (Order.add_one_le_of_lt h)

中文:
定理 dvd_of_emultiplicity_pos
  条件: {a b : α} (h : 0 < emultiplicity a b)
  结论: a ∣ b
  证明: pow_one a ▸ pow_dvd_of_le_emultiplicity (Order.add_one_le_of_lt h)

Depends on / 依赖: Order.add_one_le_of_lt, add_one_le_of_lt, pow_dvd_of_le_emultiplicity, pow_one
-/
theorem dvd_of_emultiplicity_pos {a b : α} (h : 0 < emultiplicity a b) : a ∣ b :=
  pow_one a ▸ pow_dvd_of_le_emultiplicity (Order.add_one_le_of_lt h)

/--
theorem `dvd_of_multiplicity_pos` / 定理 `dvd_of_multiplicity_pos`

English:
theorem dvd_of_multiplicity_pos
  given: {a b : α} (h : 0 < multiplicity a b)
  statement: a ∣ b
  proof: dvd_of_emultiplicity_pos (lt_emultiplicity_of_lt_multiplicity h)

中文:
定理 dvd_of_multiplicity_pos
  条件: {a b : α} (h : 0 < multiplicity a b)
  结论: a ∣ b
  证明: dvd_of_emultiplicity_pos (lt_emultiplicity_of_lt_multiplicity h)

Depends on / 依赖: dvd_of_emultiplicity_pos, lt_emultiplicity_of_lt_multiplicity
-/
theorem dvd_of_multiplicity_pos {a b : α} (h : 0 < multiplicity a b) : a ∣ b :=
  dvd_of_emultiplicity_pos (lt_emultiplicity_of_lt_multiplicity h)

/--
theorem `dvd_iff_multiplicity_pos` / 定理 `dvd_iff_multiplicity_pos`

English:
theorem dvd_iff_multiplicity_pos
  given: {a b : α}
  statement: 0 < multiplicity a b ↔ a ∣ b
  proof: ⟨dvd_of_multiplicity_pos, fun hdvd => Nat.pos_of_ne_zero (by simpa [multiplicity_eq_zero])⟩

中文:
定理 dvd_iff_multiplicity_pos
  条件: {a b : α}
  结论: 0 < multiplicity a b ↔ a ∣ b
  证明: ⟨dvd_of_multiplicity_pos, fun hdvd => Nat.pos_of_ne_zero (by simpa [multiplicity_eq_zero])⟩

Depends on / 依赖: Nat.pos_of_ne_zero, dvd_of_multiplicity_pos, multiplicity_eq_zero, pos_of_ne_zero
-/
theorem dvd_iff_multiplicity_pos {a b : α} : 0 < multiplicity a b ↔ a ∣ b :=
  ⟨dvd_of_multiplicity_pos, fun hdvd => Nat.pos_of_ne_zero (by simpa [multiplicity_eq_zero])⟩

/--
theorem `dvd_iff_emultiplicity_pos` / 定理 `dvd_iff_emultiplicity_pos`

English:
theorem dvd_iff_emultiplicity_pos
  given: {a b : α}
  statement: 0 < emultiplicity a b ↔ a ∣ b
  proof: emultiplicity_pos_iff.trans dvd_iff_multiplicity_pos

中文:
定理 dvd_iff_emultiplicity_pos
  条件: {a b : α}
  结论: 0 < emultiplicity a b ↔ a ∣ b
  证明: emultiplicity_pos_iff.trans dvd_iff_multiplicity_pos

Depends on / 依赖: dvd_iff_multiplicity_pos, emultiplicity_pos_iff, emultiplicity_pos_iff.trans
-/
theorem dvd_iff_emultiplicity_pos {a b : α} : 0 < emultiplicity a b ↔ a ∣ b :=
  emultiplicity_pos_iff.trans dvd_iff_multiplicity_pos

/--
theorem `Nat.finiteMultiplicity_iff` / 定理 `Nat.finiteMultiplicity_iff`

English:
theorem Nat.finiteMultiplicity_iff
  given: {a b : Nat}
  statement: FiniteMultiplicity a b ↔ a != 1 ∧ 0 < b
  proof: by
  rw [← not_iff_not]; rw [FiniteMultiplicity.not_iff_forall]; rw [not_and_or]; rw [not_ne_iff]; rw [not_lt]; rw [Nat.le_zero]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
have ha : a != 0 := fun ha => hb zero_dvd_iff.mp by rw [ha] at h; exact h 1
        Classical.by_contradiction

中文:
定理 Nat.finiteMultiplicity_iff
  条件: {a b : 自然数}
  结论: FiniteMultiplicity a b ↔ a != 1 ∧ 0 < b
  证明: by
  rw [← not_iff_not]; rw [FiniteMultiplicity.not_iff_forall]; rw [not_and_or]; rw [not_ne_iff]; rw [not_lt]; rw [Nat.le_zero]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
have ha : a != 0 := fun ha => hb zero_dvd_iff.mp by rw [ha] at h; exact h 1
        Classical.by_contradiction

Depends on / 依赖: Classical, Classical.by_contradiction, FiniteMultiplicity, FiniteMultiplicity.not_iff_forall, Nat.le_zero, Nat.pos_of_ne_zero, b.lt_pow_self, by_contradiction, ha_gt_one, le_of_dvd, le_zero, lt_of_not_ge, lt_pow_self, not_and_or, not_iff_forall, not_iff_not, not_lt, not_lt_of_ge, not_ne_iff, or_iff_not_imp_right
-/
theorem Nat.finiteMultiplicity_iff {a b : Nat} : FiniteMultiplicity a b ↔ a != 1 ∧ 0 < b := by
  rw [← not_iff_not]; rw [FiniteMultiplicity.not_iff_forall]; rw [not_and_or]; rw [not_ne_iff]; rw [not_lt]; rw [Nat.le_zero]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
have ha : a != 0 := fun ha => hb zero_dvd_iff.mp by rw [ha] at h; exact h 1
        Classical.by_contradiction fun ha1 : a != 1 =>
          have ha_gt_one : 1 < a :=
            lt_of_not_ge fun _ =>
              match a with
              | 0 => ha rfl
              | 1 => ha1 rfl
              | b+2 => by lia
          not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero hb) (h b)) (b.lt_pow_self ha_gt_one),
      fun h => by cases h <;> simp [*]⟩

alias ⟨_, Dvd.multiplicity_pos⟩ := dvd_iff_multiplicity_pos

end Monoid

section CommMonoid

variable [CommMonoid α]

/--
theorem `FiniteMultiplicity.mul_right` / 定理 `FiniteMultiplicity.mul_right`

English:
theorem FiniteMultiplicity.mul_right
  given: {a b c : α} (hf : FiniteMultiplicity a (b * c))
  proof: (mul_comm b c ▸ hf).mul_left

中文:
定理 FiniteMultiplicity.mul_right
  条件: {a b c : α} (hf : FiniteMultiplicity a (b * c))
  证明: (mul_comm b c ▸ hf).mul_left

Depends on / 依赖: mul_comm, mul_left
-/
theorem FiniteMultiplicity.mul_right {a b c : α} (hf : FiniteMultiplicity a (b * c)) :
    FiniteMultiplicity a c := (mul_comm b c ▸ hf).mul_left

/--
theorem `emultiplicity_of_isUnit_right` / 定理 `emultiplicity_of_isUnit_right`

English:
theorem emultiplicity_of_isUnit_right
  statement: {a b : α} (ha : ¬IsUnit a)
  proof: emultiplicity_eq_zero.mpr fun h => ha (isUnit_of_dvd_unit h hb)

中文:
定理 emultiplicity_of_isUnit_right
  结论: {a b : α} (ha : ¬IsUnit a)
  证明: emultiplicity_eq_zero.mpr fun h => ha (isUnit_of_dvd_unit h hb)

Depends on / 依赖: emultiplicity_eq_zero, emultiplicity_eq_zero.mpr, isUnit_of_dvd_unit
-/
theorem emultiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a)
    (hb : IsUnit b) : emultiplicity a b = 0 :=
  emultiplicity_eq_zero.mpr fun h => ha (isUnit_of_dvd_unit h hb)

/--
theorem `multiplicity_of_isUnit_right` / 定理 `multiplicity_of_isUnit_right`

English:
theorem multiplicity_of_isUnit_right
  statement: {a b : α} (ha : ¬IsUnit a)
  proof: multiplicity_eq_zero.mpr fun h => ha (isUnit_of_dvd_unit h hb)

中文:
定理 multiplicity_of_isUnit_right
  结论: {a b : α} (ha : ¬IsUnit a)
  证明: multiplicity_eq_zero.mpr fun h => ha (isUnit_of_dvd_unit h hb)

Depends on / 依赖: isUnit_of_dvd_unit, multiplicity_eq_zero, multiplicity_eq_zero.mpr
-/
theorem multiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a)
    (hb : IsUnit b) : multiplicity a b = 0 :=
  multiplicity_eq_zero.mpr fun h => ha (isUnit_of_dvd_unit h hb)

/--
theorem `emultiplicity_of_one_right` / 定理 `emultiplicity_of_one_right`

English:
theorem emultiplicity_of_one_right
  given: {a : α} (ha : ¬IsUnit a)
  statement: emultiplicity a 1 = 0
  proof: emultiplicity_of_isUnit_right ha isUnit_one

中文:
定理 emultiplicity_of_one_right
  条件: {a : α} (ha : ¬IsUnit a)
  结论: emultiplicity a 1 = 0
  证明: emultiplicity_of_isUnit_right ha isUnit_one

Depends on / 依赖: emultiplicity_of_isUnit_right, isUnit_one
-/
theorem emultiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : emultiplicity a 1 = 0 :=
  emultiplicity_of_isUnit_right ha isUnit_one

/--
theorem `multiplicity_of_one_right` / 定理 `multiplicity_of_one_right`

English:
theorem multiplicity_of_one_right
  given: {a : α} (ha : ¬IsUnit a)
  statement: multiplicity a 1 = 0
  proof: multiplicity_of_isUnit_right ha isUnit_one

中文:
定理 multiplicity_of_one_right
  条件: {a : α} (ha : ¬IsUnit a)
  结论: multiplicity a 1 = 0
  证明: multiplicity_of_isUnit_right ha isUnit_one

Depends on / 依赖: isUnit_one, multiplicity_of_isUnit_right
-/
theorem multiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0 :=
  multiplicity_of_isUnit_right ha isUnit_one

/--
theorem `emultiplicity_of_unit_right` / 定理 `emultiplicity_of_unit_right`

English:
theorem emultiplicity_of_unit_right
  given: {a : α} (ha : ¬IsUnit a) (u : αˣ)
  statement: emultiplicity a u = 0
  proof: emultiplicity_of_isUnit_right ha u.isUnit

中文:
定理 emultiplicity_of_unit_right
  条件: {a : α} (ha : ¬IsUnit a) (u : αˣ)
  结论: emultiplicity a u = 0
  证明: emultiplicity_of_isUnit_right ha u.isUnit

Depends on / 依赖: emultiplicity_of_isUnit_right, isUnit, u.isUnit
-/
theorem emultiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : emultiplicity a u = 0 :=
  emultiplicity_of_isUnit_right ha u.isUnit

/--
theorem `multiplicity_of_unit_right` / 定理 `multiplicity_of_unit_right`

English:
theorem multiplicity_of_unit_right
  given: {a : α} (ha : ¬IsUnit a) (u : αˣ)
  statement: multiplicity a u = 0
  proof: multiplicity_of_isUnit_right ha u.isUnit

中文:
定理 multiplicity_of_unit_right
  条件: {a : α} (ha : ¬IsUnit a) (u : αˣ)
  结论: multiplicity a u = 0
  证明: multiplicity_of_isUnit_right ha u.isUnit

Depends on / 依赖: isUnit, multiplicity_of_isUnit_right, u.isUnit
-/
theorem multiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicity a u = 0 :=
  multiplicity_of_isUnit_right ha u.isUnit

/--
theorem `emultiplicity_le_emultiplicity_of_dvd_left` / 定理 `emultiplicity_le_emultiplicity_of_dvd_left`

English:
theorem emultiplicity_le_emultiplicity_of_dvd_left
  given: {a b c : α} (hdvd : a ∣ b)
  proof: emultiplicity_le_emultiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h

中文:
定理 emultiplicity_le_emultiplicity_of_dvd_left
  条件: {a b c : α} (hdvd : a ∣ b)
  证明: emultiplicity_le_emultiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h

Depends on / 依赖: emultiplicity_le_emultiplicity_iff, pow_dvd_pow_of_dvd
-/
theorem emultiplicity_le_emultiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) :
    emultiplicity b c <= emultiplicity a c :=
  emultiplicity_le_emultiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h

/--
theorem `emultiplicity_eq_of_associated_left` / 定理 `emultiplicity_eq_of_associated_left`

English:
theorem emultiplicity_eq_of_associated_left
  given: {a b c : α} (h : Associated a b)
  proof: le_antisymm (emultiplicity_le_emultiplicity_of_dvd_left h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_left h.symm.dvd)

中文:
定理 emultiplicity_eq_of_associated_left
  条件: {a b c : α} (h : Associated a b)
  证明: le_antisymm (emultiplicity_le_emultiplicity_of_dvd_left h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_left h.symm.dvd)

Depends on / 依赖: emultiplicity_le_emultiplicity_of_dvd_left, h.dvd, h.symm.dvd, le_antisymm
-/
theorem emultiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) :
    emultiplicity b c = emultiplicity a c :=
  le_antisymm (emultiplicity_le_emultiplicity_of_dvd_left h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_left h.symm.dvd)

/--
theorem `multiplicity_eq_of_associated_left` / 定理 `multiplicity_eq_of_associated_left`

English:
theorem multiplicity_eq_of_associated_left
  given: {a b c : α} (h : Associated a b)
  proof: multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_left h)

中文:
定理 multiplicity_eq_of_associated_left
  条件: {a b c : α} (h : Associated a b)
  证明: multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_left h)

Depends on / 依赖: emultiplicity_eq_of_associated_left, multiplicity_eq_of_emultiplicity_eq
-/
theorem multiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) :
    multiplicity b c = multiplicity a c :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_left h)

/--
theorem `emultiplicity_mk_eq_emultiplicity` / 定理 `emultiplicity_mk_eq_emultiplicity`

English:
theorem emultiplicity_mk_eq_emultiplicity
  given: {a b : α}
  proof: by
  simp [emultiplicity_eq_emultiplicity_iff, ← Associates.mk_pow, Associates.mk_dvd_mk]

中文:
定理 emultiplicity_mk_eq_emultiplicity
  条件: {a b : α}
  证明: by
  simp [emultiplicity_eq_emultiplicity_iff, ← Associates.mk_pow, Associates.mk_dvd_mk]

Depends on / 依赖: Associates, Associates.mk_dvd_mk, Associates.mk_pow, emultiplicity_eq_emultiplicity_iff, mk_dvd_mk, mk_pow
-/
theorem emultiplicity_mk_eq_emultiplicity {a b : α} :
    emultiplicity (Associates.mk a) (Associates.mk b) = emultiplicity a b := by
  simp [emultiplicity_eq_emultiplicity_iff, ← Associates.mk_pow, Associates.mk_dvd_mk]

end CommMonoid

section MonoidWithZero

variable [MonoidWithZero α]

/--
theorem `FiniteMultiplicity.ne_zero` / 定理 `FiniteMultiplicity.ne_zero`

English:
theorem FiniteMultiplicity.ne_zero
  given: {a b : α} (h : FiniteMultiplicity a b)
  statement: b != 0
  proof: let ⟨n, hn⟩ := h
  fun hb => by simp [hb] at hn

@[simp]

中文:
定理 FiniteMultiplicity.ne_zero
  条件: {a b : α} (h : FiniteMultiplicity a b)
  结论: b != 0
  证明: let ⟨n, hn⟩ := h
  fun hb => by simp [hb] at hn

@[simp]
-/
theorem FiniteMultiplicity.ne_zero {a b : α} (h : FiniteMultiplicity a b) : b != 0 :=
  let ⟨n, hn⟩ := h
  fun hb => by simp [hb] at hn

@[simp]
/--
theorem `emultiplicity_zero` / 定理 `emultiplicity_zero`

English:
theorem emultiplicity_zero
  given: (a : α)
  statement: emultiplicity a 0 = ⊤
  proof: emultiplicity_eq_top.2 (fun v => v.ne_zero rfl)

中文:
定理 emultiplicity_zero
  条件: (a : α)
  结论: emultiplicity a 0 = ⊤
  证明: emultiplicity_eq_top.2 (fun v => v.ne_zero rfl)

Depends on / 依赖: emultiplicity_eq_top, ne_zero, v.ne_zero
-/
theorem emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤ :=
  emultiplicity_eq_top.2 (fun v => v.ne_zero rfl)

/--
theorem `multiplicity_zero` / 定理 `multiplicity_zero`

English:
theorem multiplicity_zero
  given: (a : α)
  statement: multiplicity a 0 = 1
  proof: multiplicity_eq_one_of_not_finiteMultiplicity fun h => h.ne_zero rfl

@[simp]

中文:
定理 multiplicity_zero
  条件: (a : α)
  结论: multiplicity a 0 = 1
  证明: multiplicity_eq_one_of_not_finiteMultiplicity fun h => h.ne_zero rfl

@[simp]

Depends on / 依赖: h.ne_zero, multiplicity_eq_one_of_not_finiteMultiplicity, ne_zero
-/
theorem multiplicity_zero (a : α) : multiplicity a 0 = 1 :=
  multiplicity_eq_one_of_not_finiteMultiplicity fun h => h.ne_zero rfl

@[simp]
/--
theorem `emultiplicity_zero_eq_zero_of_ne_zero` / 定理 `emultiplicity_zero_eq_zero_of_ne_zero`

English:
theorem emultiplicity_zero_eq_zero_of_ne_zero
  given: (a : α) (ha : a != 0)
  statement: emultiplicity 0 a = 0
  proof: emultiplicity_eq_zero.2 mt zero_dvd_iff.1 ha

@[simp]

中文:
定理 emultiplicity_zero_eq_zero_of_ne_zero
  条件: (a : α) (ha : a != 0)
  结论: emultiplicity 0 a = 0
  证明: emultiplicity_eq_zero.2 mt zero_dvd_iff.1 ha

@[simp]

Depends on / 依赖: emultiplicity_eq_zero, zero_dvd_iff
-/
theorem emultiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a != 0) : emultiplicity 0 a = 0 :=
emultiplicity_eq_zero.2 mt zero_dvd_iff.1 ha

@[simp]
/--
theorem `multiplicity_zero_eq_zero_of_ne_zero` / 定理 `multiplicity_zero_eq_zero_of_ne_zero`

English:
theorem multiplicity_zero_eq_zero_of_ne_zero
  given: (a : α) (ha : a != 0)
  statement: multiplicity 0 a = 0
  proof: multiplicity_eq_zero.2 mt zero_dvd_iff.1 ha

中文:
定理 multiplicity_zero_eq_zero_of_ne_zero
  条件: (a : α) (ha : a != 0)
  结论: multiplicity 0 a = 0
  证明: multiplicity_eq_zero.2 mt zero_dvd_iff.1 ha

Depends on / 依赖: multiplicity_eq_zero, zero_dvd_iff
-/
theorem multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a != 0) : multiplicity 0 a = 0 :=
multiplicity_eq_zero.2 mt zero_dvd_iff.1 ha

end MonoidWithZero

section Semiring

variable [Semiring α]

/--
theorem `FiniteMultiplicity.or_of_add` / 定理 `FiniteMultiplicity.or_of_add`

English:
theorem FiniteMultiplicity.or_of_add
  given: {p a b : α} (hf : FiniteMultiplicity p (a + b))
  proof: by
  by_contra! nh
  obtain ⟨c, hc⟩ := hf
  simp_all [dvd_add]

中文:
定理 FiniteMultiplicity.or_of_add
  条件: {p a b : α} (hf : FiniteMultiplicity p (a + b))
  证明: by
  by_contra! nh
  obtain ⟨c, hc⟩ := hf
  simp_all [dvd_add]

Depends on / 依赖: dvd_add
-/
theorem FiniteMultiplicity.or_of_add {p a b : α} (hf : FiniteMultiplicity p (a + b)) :
    FiniteMultiplicity p a ∨ FiniteMultiplicity p b := by
  by_contra! nh
  obtain ⟨c, hc⟩ := hf
  simp_all [dvd_add]

/--
theorem `min_le_emultiplicity_add` / 定理 `min_le_emultiplicity_add`

English:
theorem min_le_emultiplicity_add
  given: {p a b : α}
  proof: by
  cases hm : min (emultiplicity p a) (emultiplicity p b)
  · simp only [top_le_iff, min_eq_top, emultiplicity_eq_top] at hm ⊢
    contrapose hm
    simp only [not_and_or, not_not] at hm ⊢
    exact hm.or_of_add
  · apply le_emultiplicity_of_pow_dvd
    simp [dvd_add, pow_dvd_of_le_emultiplicity, 

中文:
定理 min_le_emultiplicity_add
  条件: {p a b : α}
  证明: by
  cases hm : min (emultiplicity p a) (emultiplicity p b)
  · simp only [top_le_iff, min_eq_top, emultiplicity_eq_top] at hm ⊢
    contrapose hm
    simp only [not_and_or, not_not] at hm ⊢
    exact hm.or_of_add
  · apply le_emultiplicity_of_pow_dvd
    simp [dvd_add, pow_dvd_of_le_emultiplicity, 

Depends on / 依赖: contrapose, dvd_add, emultiplicity, emultiplicity_eq_top, hm.or_of_add, le_emultiplicity_of_pow_dvd, min_eq_top, not_and_or, not_not, or_of_add, pow_dvd_of_le_emultiplicity, top_le_iff
-/
theorem min_le_emultiplicity_add {p a b : α} :
    min (emultiplicity p a) (emultiplicity p b) <= emultiplicity p (a + b) := by
  cases hm : min (emultiplicity p a) (emultiplicity p b)
  · simp only [top_le_iff, min_eq_top, emultiplicity_eq_top] at hm ⊢
    contrapose hm
    simp only [not_and_or, not_not] at hm ⊢
    exact hm.or_of_add
  · apply le_emultiplicity_of_pow_dvd
    simp [dvd_add, pow_dvd_of_le_emultiplicity, ← hm]

end Semiring

section Ring

variable [Ring α]

@[simp]
/--
theorem `FiniteMultiplicity.neg_iff` / 定理 `FiniteMultiplicity.neg_iff`

English:
theorem FiniteMultiplicity.neg_iff
  given: {a b : α}
  proof: by
  unfold FiniteMultiplicity
  congr! 3
  simp only [dvd_neg]

alias ⟨_, FiniteMultiplicity.neg⟩ := FiniteMultiplicity.neg_iff

@[simp]

中文:
定理 FiniteMultiplicity.neg_iff
  条件: {a b : α}
  证明: by
  unfold FiniteMultiplicity
  congr! 3
  simp only [dvd_neg]

alias ⟨_, FiniteMultiplicity.neg⟩ := FiniteMultiplicity.neg_iff

@[simp]

Depends on / 依赖: FiniteMultiplicity, dvd_neg
-/
theorem FiniteMultiplicity.neg_iff {a b : α} :
    FiniteMultiplicity a (-b) ↔ FiniteMultiplicity a b := by
  unfold FiniteMultiplicity
  congr! 3
  simp only [dvd_neg]

alias ⟨_, FiniteMultiplicity.neg⟩ := FiniteMultiplicity.neg_iff

@[simp]
/--
theorem `emultiplicity_neg` / 定理 `emultiplicity_neg`

English:
theorem emultiplicity_neg
  given: (a b : α)
  statement: emultiplicity a (-b) = emultiplicity a b
  proof: by
  rw [emultiplicity_eq_emultiplicity_iff]
  simp

@[simp]

中文:
定理 emultiplicity_neg
  条件: (a b : α)
  结论: emultiplicity a (-b) = emultiplicity a b
  证明: by
  rw [emultiplicity_eq_emultiplicity_iff]
  simp

@[simp]

Depends on / 依赖: emultiplicity_eq_emultiplicity_iff
-/
theorem emultiplicity_neg (a b : α) : emultiplicity a (-b) = emultiplicity a b := by
  rw [emultiplicity_eq_emultiplicity_iff]
  simp

@[simp]
/--
theorem `multiplicity_neg` / 定理 `multiplicity_neg`

English:
theorem multiplicity_neg
  given: (a b : α)
  statement: multiplicity a (-b) = multiplicity a b
  proof: multiplicity_eq_of_emultiplicity_eq (emultiplicity_neg a b)

中文:
定理 multiplicity_neg
  条件: (a b : α)
  结论: multiplicity a (-b) = multiplicity a b
  证明: multiplicity_eq_of_emultiplicity_eq (emultiplicity_neg a b)

Depends on / 依赖: emultiplicity_neg, multiplicity_eq_of_emultiplicity_eq
-/
theorem multiplicity_neg (a b : α) : multiplicity a (-b) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_neg a b)

/--
theorem `Int.emultiplicity_natAbs` / 定理 `Int.emultiplicity_natAbs`

English:
theorem Int.emultiplicity_natAbs
  given: (a : Nat) (b : Int)
  proof: by
  rcases Int.natAbs_eq b with h | h <;> conv_rhs => rw [h]
  · rw [Int.natCast_emultiplicity]
  · rw [emultiplicity_neg, Int.natCast_emultiplicity]

中文:
定理 Int.emultiplicity_natAbs
  条件: (a : 自然数) (b : 整数)
  证明: by
  rcases Int.natAbs_eq b with h | h <;> conv_rhs => rw [h]
  · rw [Int.natCast_emultiplicity]
  · rw [emultiplicity_neg, Int.natCast_emultiplicity]

Depends on / 依赖: Int.natAbs_eq, Int.natCast_emultiplicity, conv_rhs, emultiplicity_neg, natAbs_eq, natCast_emultiplicity
-/
theorem Int.emultiplicity_natAbs (a : Nat) (b : Int) :
    emultiplicity a b.natAbs = emultiplicity (a : Int) b := by
  rcases Int.natAbs_eq b with h | h <;> conv_rhs => rw [h]
  · rw [Int.natCast_emultiplicity]
  · rw [emultiplicity_neg, Int.natCast_emultiplicity]

/--
theorem `Int.multiplicity_natAbs` / 定理 `Int.multiplicity_natAbs`

English:
theorem Int.multiplicity_natAbs
  given: (a : Nat) (b : Int)
  proof: multiplicity_eq_of_emultiplicity_eq (Int.emultiplicity_natAbs a b)

中文:
定理 Int.multiplicity_natAbs
  条件: (a : 自然数) (b : 整数)
  证明: multiplicity_eq_of_emultiplicity_eq (Int.emultiplicity_natAbs a b)

Depends on / 依赖: Int.emultiplicity_natAbs, emultiplicity_natAbs, multiplicity_eq_of_emultiplicity_eq
-/
theorem Int.multiplicity_natAbs (a : Nat) (b : Int) :
    multiplicity a b.natAbs = multiplicity (a : Int) b :=
  multiplicity_eq_of_emultiplicity_eq (Int.emultiplicity_natAbs a b)

/--
theorem `emultiplicity_add_of_gt` / 定理 `emultiplicity_add_of_gt`

English:
theorem emultiplicity_add_of_gt
  given: {p a b : α} (h : emultiplicity p b < emultiplicity p a)
  proof: by
  have : FiniteMultiplicity p b := finiteMultiplicity_iff_emultiplicity_ne_top.2 (by simp [·] at h)
  rw [this.emultiplicity_eq_multiplicity] at *
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · apply dvd_add
    · apply pow_dvd_of_le_emultiplicity
      exact h.le
    · simp
  · rw [dvd_add_right

中文:
定理 emultiplicity_add_of_gt
  条件: {p a b : α} (h : emultiplicity p b < emultiplicity p a)
  证明: by
  have : FiniteMultiplicity p b := finiteMultiplicity_iff_emultiplicity_ne_top.2 (by simp [·] at h)
  rw [this.emultiplicity_eq_multiplicity] at *
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · apply dvd_add
    · apply pow_dvd_of_le_emultiplicity
      exact h.le
    · simp
  · rw [dvd_add_right

Depends on / 依赖: FiniteMultiplicity, Order.add_one_le_of_lt, add_one_le_of_lt, dvd_add, dvd_add_right, emultiplicity_eq_multiplicity, emultiplicity_eq_of_dvd_of_not_dvd, finiteMultiplicity_iff_emultiplicity_ne_top, h.le, not_pow_dvd_of_multiplicity_lt, pow_dvd_of_le_emultiplicity, this.emultiplicity_eq_multiplicity, this.not_pow_dvd_of_multiplicity_lt
-/
theorem emultiplicity_add_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity p a) :
    emultiplicity p (a + b) = emultiplicity p b := by
  have : FiniteMultiplicity p b := finiteMultiplicity_iff_emultiplicity_ne_top.2 (by simp [·] at h)
  rw [this.emultiplicity_eq_multiplicity] at *
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · apply dvd_add
    · apply pow_dvd_of_le_emultiplicity
      exact h.le
    · simp
  · rw [dvd_add_right]
    · apply this.not_pow_dvd_of_multiplicity_lt
      simp
    apply pow_dvd_of_le_emultiplicity
    exact Order.add_one_le_of_lt h

/--
theorem `FiniteMultiplicity.multiplicity_add_of_gt` / 定理 `FiniteMultiplicity.multiplicity_add_of_gt`

English:
theorem FiniteMultiplicity.multiplicity_add_of_gt
  statement: {p a b : α} (hf : FiniteMultiplicity p b)
  proof: multiplicity_eq_of_emultiplicity_eq emultiplicity_add_of_gt (hf.emultiplicity_eq_multiplicity ▸
      (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity)

中文:
定理 FiniteMultiplicity.multiplicity_add_of_gt
  结论: {p a b : α} (hf : FiniteMultiplicity p b)
  证明: multiplicity_eq_of_emultiplicity_eq emultiplicity_add_of_gt (hf.emultiplicity_eq_multiplicity ▸
      (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity)

Depends on / 依赖: WithTop, WithTop.coe_strictMono, coe_strictMono, emultiplicity_add_of_gt, emultiplicity_eq_multiplicity, hf.emultiplicity_eq_multiplicity, multiplicity_eq_of_emultiplicity_eq, multiplicity_le_emultiplicity, trans_le
-/
theorem FiniteMultiplicity.multiplicity_add_of_gt {p a b : α} (hf : FiniteMultiplicity p b)
    (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a + b) = multiplicity p b :=
multiplicity_eq_of_emultiplicity_eq emultiplicity_add_of_gt (hf.emultiplicity_eq_multiplicity ▸
      (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity)

/--
theorem `emultiplicity_sub_of_gt` / 定理 `emultiplicity_sub_of_gt`

English:
theorem emultiplicity_sub_of_gt
  given: {p a b : α} (h : emultiplicity p b < emultiplicity p a)
  proof: by
  rw [sub_eq_add_neg]; rw [emultiplicity_add_of_gt] <;> rw [emultiplicity_neg]; assumption

中文:
定理 emultiplicity_sub_of_gt
  条件: {p a b : α} (h : emultiplicity p b < emultiplicity p a)
  证明: by
  rw [sub_eq_add_neg]; rw [emultiplicity_add_of_gt] <;> rw [emultiplicity_neg]; assumption

Depends on / 依赖: emultiplicity_add_of_gt, emultiplicity_neg, sub_eq_add_neg
-/
theorem emultiplicity_sub_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity p a) :
    emultiplicity p (a - b) = emultiplicity p b := by
  rw [sub_eq_add_neg]; rw [emultiplicity_add_of_gt] <;> rw [emultiplicity_neg]; assumption

/--
theorem `multiplicity_sub_of_gt` / 定理 `multiplicity_sub_of_gt`

English:
theorem multiplicity_sub_of_gt
  statement: {p a b : α} (h : multiplicity p b < multiplicity p a)
  proof: by
  rw [sub_eq_add_neg]; rw [hfin.neg.multiplicity_add_of_gt] <;> rw [multiplicity_neg]; assumption

中文:
定理 multiplicity_sub_of_gt
  结论: {p a b : α} (h : multiplicity p b < multiplicity p a)
  证明: by
  rw [sub_eq_add_neg]; rw [hfin.neg.multiplicity_add_of_gt] <;> rw [multiplicity_neg]; assumption

Depends on / 依赖: hfin.neg.multiplicity_add_of_gt, multiplicity_add_of_gt, multiplicity_neg, sub_eq_add_neg
-/
theorem multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a)
    (hfin : FiniteMultiplicity p b) : multiplicity p (a - b) = multiplicity p b := by
  rw [sub_eq_add_neg]; rw [hfin.neg.multiplicity_add_of_gt] <;> rw [multiplicity_neg]; assumption

/--
theorem `emultiplicity_add_eq_min` / 定理 `emultiplicity_add_eq_min`

English:
theorem emultiplicity_add_eq_min
  statement: {p a b : α}
  proof: by
  rcases lt_trichotomy (emultiplicity p a) (emultiplicity p b) with (hab | _ | hab)
  · rw [add_comm, emultiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [emultiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

中文:
定理 emultiplicity_add_eq_min
  结论: {p a b : α}
  证明: by
  rcases lt_trichotomy (emultiplicity p a) (emultiplicity p b) with (hab | _ | hab)
  · rw [add_comm, emultiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [emultiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

Depends on / 依赖: add_comm, emultiplicity, emultiplicity_add_of_gt, le_of_lt, lt_trichotomy, min_eq_left, min_eq_right
-/
theorem emultiplicity_add_eq_min {p a b : α}
    (h : emultiplicity p a != emultiplicity p b) :
    emultiplicity p (a + b) = min (emultiplicity p a) (emultiplicity p b) := by
  rcases lt_trichotomy (emultiplicity p a) (emultiplicity p b) with (hab | _ | hab)
  · rw [add_comm, emultiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [emultiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

/--
theorem `multiplicity_add_eq_min` / 定理 `multiplicity_add_eq_min`

English:
theorem multiplicity_add_eq_min
  statement: {p a b : α} (ha : FiniteMultiplicity p a)
  proof: by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | _ | hab)
  · rw [add_comm, ha.multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [hb.multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

中文:
定理 multiplicity_add_eq_min
  结论: {p a b : α} (ha : FiniteMultiplicity p a)
  证明: by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | _ | hab)
  · rw [add_comm, ha.multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [hb.multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

Depends on / 依赖: add_comm, ha.multiplicity_add_of_gt, hb.multiplicity_add_of_gt, le_of_lt, lt_trichotomy, min_eq_left, min_eq_right, multiplicity, multiplicity_add_of_gt
-/
theorem multiplicity_add_eq_min {p a b : α} (ha : FiniteMultiplicity p a)
    (hb : FiniteMultiplicity p b) (h : multiplicity p a != multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) := by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | _ | hab)
  · rw [add_comm, ha.multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [hb.multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

end Ring

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α]

/--
theorem `finiteMultiplicity_mul_aux` / 定理 `finiteMultiplicity_mul_aux`

English:
theorem finiteMultiplicity_mul_aux
  given: {p : α} (hp : Prime p) {a b : α}
  proof: ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by simp [hx, hn0] at ha
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha (hx.symm ▸ ⟨y, mul_rig

中文:
定理 finiteMultiplicity_mul_aux
  条件: {p : α} (hp : Prime p) {a b : α}
  证明: ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by simp [hx, hn0] at ha
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha (hx.symm ▸ ⟨y, mul_rig

Depends on / 依赖: mul_comm, mul_left_comm, pow_add
-/
theorem finiteMultiplicity_mul_aux {p : α} (hp : Prime p) {a b : α} :
    forall {n m : Nat}, ¬p ^ (n + 1) ∣ a -> ¬p ^ (m + 1) ∣ b -> ¬p ^ (n + m + 1) ∣ a * b
  | n, m => fun ha hb ⟨s, hs⟩ =>
    have : p ∣ a * b := ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by simp [hx, hn0] at ha
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha (hx.symm ▸ ⟨y, mul_right_cancel₀ hp.1 <| by
            rw [tsub_add_cancel_of_le (succ_le_of_lt hn0)] at hy
            simp [hy, pow_add, mul_comm, mul_left_comm]⟩)
        have : 1 <= n + m := le_trans hn0 (Nat.le_add_right n m)
        finiteMultiplicity_mul_aux hp hpx hb
          ⟨s, mul_right_cancel₀ hp.1 (by
                rw [tsub_add_eq_add_tsub (succ_le_of_lt hn0)]; rw [tsub_add_cancel_of_le this]
                simp_all [mul_comm, mul_left_comm, pow_add])⟩)
      fun ⟨x, hx⟩ =>
        have hm0 : 0 < m :=
          Nat.pos_of_ne_zero fun hm0 => by simp [hx, hm0] at hb
        have hpx : ¬p ^ (m - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          hb
            (hx.symm ▸
              ⟨y,
mul_right_cancel₀ hp.1 by
                  rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)] at hy
                  simp [hy, pow_add, mul_comm, mul_left_comm]⟩)
        finiteMultiplicity_mul_aux hp ha hpx
        ⟨s, mul_right_cancel₀ hp.1 (by
              rw [add_assoc]; rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)]
              simp_all [mul_comm, mul_left_comm, pow_add])⟩

/--
theorem `Prime.finiteMultiplicity_mul` / 定理 `Prime.finiteMultiplicity_mul`

English:
theorem Prime.finiteMultiplicity_mul
  given: {p a b : α} (hp : Prime p)
  proof: fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finiteMultiplicity_mul_aux hp hn hm⟩

中文:
定理 Prime.finiteMultiplicity_mul
  条件: {p a b : α} (hp : Prime p)
  证明: fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finiteMultiplicity_mul_aux hp hn hm⟩

Depends on / 依赖: finiteMultiplicity_mul_aux
-/
theorem Prime.finiteMultiplicity_mul {p a b : α} (hp : Prime p) :
    FiniteMultiplicity p a -> FiniteMultiplicity p b -> FiniteMultiplicity p (a * b) :=
  fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finiteMultiplicity_mul_aux hp hn hm⟩

/--
theorem `FiniteMultiplicity.mul_iff` / 定理 `FiniteMultiplicity.mul_iff`

English:
theorem FiniteMultiplicity.mul_iff
  given: {p a b : α} (hp : Prime p)
  proof: ⟨fun h => ⟨h.mul_left, h.mul_right⟩, fun h =>
    hp.finiteMultiplicity_mul h.1 h.2⟩

中文:
定理 FiniteMultiplicity.mul_iff
  条件: {p a b : α} (hp : Prime p)
  证明: ⟨fun h => ⟨h.mul_left, h.mul_right⟩, fun h =>
    hp.finiteMultiplicity_mul h.1 h.2⟩

Depends on / 依赖: finiteMultiplicity_mul, h.mul_left, h.mul_right, hp.finiteMultiplicity_mul, mul_left, mul_right
-/
theorem FiniteMultiplicity.mul_iff {p a b : α} (hp : Prime p) :
    FiniteMultiplicity p (a * b) ↔ FiniteMultiplicity p a ∧ FiniteMultiplicity p b :=
  ⟨fun h => ⟨h.mul_left, h.mul_right⟩, fun h =>
    hp.finiteMultiplicity_mul h.1 h.2⟩

/--
theorem `FiniteMultiplicity.pow` / 定理 `FiniteMultiplicity.pow`

English:
theorem FiniteMultiplicity.pow
  statement: {p a : α} (hp : Prime p)
  proof: match k, hfin with
  | 0, _ => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [_root_.pow_succ']; exact hp.finiteMultiplicity_mul ha (ha.pow hp)

@[simp]

中文:
定理 FiniteMultiplicity.pow
  结论: {p a : α} (hp : Prime p)
  证明: match k, hfin with
  | 0, _ => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [_root_.pow_succ']; exact hp.finiteMultiplicity_mul ha (ha.pow hp)

@[simp]

Depends on / 依赖: _root_, _root_.pow_succ, finiteMultiplicity_mul, ha.pow, hp.finiteMultiplicity_mul, isUnit_iff_dvd_one, pow_succ
-/
theorem FiniteMultiplicity.pow {p a : α} (hp : Prime p)
    (hfin : FiniteMultiplicity p a) {k : Nat} : FiniteMultiplicity p (a ^ k) :=
  match k, hfin with
  | 0, _ => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [_root_.pow_succ']; exact hp.finiteMultiplicity_mul ha (ha.pow hp)

@[simp]
/--
theorem `multiplicity_self` / 定理 `multiplicity_self`

English:
theorem multiplicity_self
  given: {a : α}
  statement: multiplicity a a = 1
  proof: by
  by_cases ha : FiniteMultiplicity a a
  · rw [ha.multiplicity_eq_iff]
    simp only [pow_one, dvd_refl, reduceAdd, true_and]
    rintro ⟨v, hv⟩
    nth_rw 1 [← mul_one a] at hv
    simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
    obtain hv | rfl := hv
    · have : IsUnit a := .of_mul_eq_

中文:
定理 multiplicity_self
  条件: {a : α}
  结论: multiplicity a a = 1
  证明: by
  by_cases ha : FiniteMultiplicity a a
  · rw [ha.multiplicity_eq_iff]
    simp only [pow_one, dvd_refl, reduceAdd, true_and]
    rintro ⟨v, hv⟩
    nth_rw 1 [← mul_one a] at hv
    simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
    obtain hv | rfl := hv
    · have : IsUnit a := .of_mul_eq_

Depends on / 依赖: FiniteMultiplicity, IsUnit, dvd_refl, ha.multiplicity_eq_iff, ha.ne_zero, ha.not_isUnit, hv.symm, mul_assoc, mul_eq_mul_left_iff, mul_one, multiplicity_eq_iff, ne_zero, not_isUnit, nth_rw, of_mul_eq_one, pow_one, reduceAdd, true_and
-/
theorem multiplicity_self {a : α} : multiplicity a a = 1 := by
  by_cases ha : FiniteMultiplicity a a
  · rw [ha.multiplicity_eq_iff]
    simp only [pow_one, dvd_refl, reduceAdd, true_and]
    rintro ⟨v, hv⟩
    nth_rw 1 [← mul_one a] at hv
    simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
    obtain hv | rfl := hv
    · have : IsUnit a := .of_mul_eq_one v hv.symm
      simpa [this] using ha.not_isUnit
    · simpa using ha.ne_zero
  · simp [ha]

@[simp]
/--
theorem `FiniteMultiplicity.emultiplicity_self` / 定理 `FiniteMultiplicity.emultiplicity_self`

English:
theorem FiniteMultiplicity.emultiplicity_self
  given: {a : α} (hfin : FiniteMultiplicity a a)
  proof: by
  simp [hfin.emultiplicity_eq_multiplicity]

中文:
定理 FiniteMultiplicity.emultiplicity_self
  条件: {a : α} (hfin : FiniteMultiplicity a a)
  证明: by
  simp [hfin.emultiplicity_eq_multiplicity]

Depends on / 依赖: emultiplicity_eq_multiplicity, hfin.emultiplicity_eq_multiplicity
-/
theorem FiniteMultiplicity.emultiplicity_self {a : α} (hfin : FiniteMultiplicity a a) :
    emultiplicity a a = 1 := by
  simp [hfin.emultiplicity_eq_multiplicity]

/--
theorem `multiplicity_mul` / 定理 `multiplicity_mul`

English:
theorem multiplicity_mul
  given: {p a b : α} (hp : Prime p) (hfin : FiniteMultiplicity p (a * b))
  proof: by
  have hdiva : p ^ multiplicity p a ∣ a := pow_multiplicity_dvd ..
  have hdivb : p ^ multiplicity p b ∣ b := pow_multiplicity_dvd ..
  have hdiv : p ^ (multiplicity p a + multiplicity p b) ∣ a * b := by
    rw [pow_add]; gcongr
  have hsucc : ¬p ^ (multiplicity p a + multiplicity p b + 1) ∣ a * 

中文:
定理 multiplicity_mul
  条件: {p a b : α} (hp : Prime p) (hfin : FiniteMultiplicity p (a * b))
  证明: by
  have hdiva : p ^ multiplicity p a ∣ a := pow_multiplicity_dvd ..
  have hdivb : p ^ multiplicity p b ∣ b := pow_multiplicity_dvd ..
  have hdiv : p ^ (multiplicity p a + multiplicity p b) ∣ a * b := by
    rw [pow_add]; gcongr
  have hsucc : ¬p ^ (multiplicity p a + multiplicity p b + 1) ∣ a * 

Depends on / 依赖: _root_, _root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul, hfin.mul_left.not_pow_dvd_of_multiplicity_lt, hfin.mul_right.not_pow_dvd_of_multiplicity_lt, lt_succ_self, mul_left, mul_right, multiplicity, not_or_intro, not_pow_dvd_of_multiplicity_lt, pow_add, pow_multiplicity_dvd, succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
-/
theorem multiplicity_mul {p a b : α} (hp : Prime p) (hfin : FiniteMultiplicity p (a * b)) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b := by
  have hdiva : p ^ multiplicity p a ∣ a := pow_multiplicity_dvd ..
  have hdivb : p ^ multiplicity p b ∣ b := pow_multiplicity_dvd ..
  have hdiv : p ^ (multiplicity p a + multiplicity p b) ∣ a * b := by
    rw [pow_add]; gcongr
  have hsucc : ¬p ^ (multiplicity p a + multiplicity p b + 1) ∣ a * b :=
    fun h =>
    not_or_intro (hfin.mul_left.not_pow_dvd_of_multiplicity_lt (lt_succ_self _))
      (hfin.mul_right.not_pow_dvd_of_multiplicity_lt (lt_succ_self _))
      (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h)
  rw [hfin.multiplicity_eq_iff]
  exact ⟨hdiv, hsucc⟩

/--
theorem `emultiplicity_mul` / 定理 `emultiplicity_mul`

English:
theorem emultiplicity_mul
  given: {p a b : α} (hp : Prime p)
  proof: by
  by_cases hfin : FiniteMultiplicity p (a * b)
  · rw [hfin.emultiplicity_eq_multiplicity, hfin.mul_left.emultiplicity_eq_multiplicity,
      hfin.mul_right.emultiplicity_eq_multiplicity]
    norm_cast
    exact multiplicity_mul hp hfin
  · rw [emultiplicity_eq_top.mpr hfin, eq_comm, ENat.add_eq_

中文:
定理 emultiplicity_mul
  条件: {p a b : α} (hp : Prime p)
  证明: by
  by_cases hfin : FiniteMultiplicity p (a * b)
  · rw [hfin.emultiplicity_eq_multiplicity, hfin.mul_left.emultiplicity_eq_multiplicity,
      hfin.mul_right.emultiplicity_eq_multiplicity]
    norm_cast
    exact multiplicity_mul hp hfin
  · rw [emultiplicity_eq_top.mpr hfin, eq_comm, ENat.add_eq_

Depends on / 依赖: ENat.add_eq_top, FiniteMultiplicity, FiniteMultiplicity.mul_iff, add_eq_top, emultiplicity_eq_multiplicity, emultiplicity_eq_top, emultiplicity_eq_top.mpr, eq_comm, hfin.emultiplicity_eq_multiplicity, hfin.mul_left.emultiplicity_eq_multiplicity, hfin.mul_right.emultiplicity_eq_multiplicity, mul_iff, mul_left, mul_right, multiplicity_mul, not_and_or
-/
theorem emultiplicity_mul {p a b : α} (hp : Prime p) :
    emultiplicity p (a * b) = emultiplicity p a + emultiplicity p b := by
  by_cases hfin : FiniteMultiplicity p (a * b)
  · rw [hfin.emultiplicity_eq_multiplicity, hfin.mul_left.emultiplicity_eq_multiplicity,
      hfin.mul_right.emultiplicity_eq_multiplicity]
    norm_cast
    exact multiplicity_mul hp hfin
  · rw [emultiplicity_eq_top.mpr hfin, eq_comm, ENat.add_eq_top, emultiplicity_eq_top,
      emultiplicity_eq_top]
    simpa only [FiniteMultiplicity.mul_iff hp, not_and_or] using hfin

/--
theorem `Finset.emultiplicity_prod` / 定理 `Finset.emultiplicity_prod`

English:
theorem Finset.emultiplicity_prod
  given: {β : Type*} {p : α} (hp : Prime p) (s : Finset β) (f : β -> α)
  proof: by classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact emultiplicity_of_one_right hp.not_isUnit
  | insert a s has ih => simpa [has, ← ih] using emultiplicity_mul hp

中文:
定理 Finset.emultiplicity_prod
  条件: {β : 类型} {p : α} (hp : Prime p) (s : Finset β) (f : β -> α)
  证明: by classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact emultiplicity_of_one_right hp.not_isUnit
  | insert a s has ih => simpa [has, ← ih] using emultiplicity_mul hp

Depends on / 依赖: Finset, Finset.induction, Finset.prod_empty, Finset.sum_empty, classical, emultiplicity_mul, emultiplicity_of_one_right, hp.not_isUnit, insert, not_isUnit, prod_empty, sum_empty
-/
theorem Finset.emultiplicity_prod {β : Type*} {p : α} (hp : Prime p) (s : Finset β) (f : β -> α) :
    emultiplicity p (∏ x in s, f x) = ∑ x in s, emultiplicity p (f x) := by classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact emultiplicity_of_one_right hp.not_isUnit
  | insert a s has ih => simpa [has, ← ih] using emultiplicity_mul hp

/--
theorem `emultiplicity_pow` / 定理 `emultiplicity_pow`

English:
theorem emultiplicity_pow
  given: {p a : α} (hp : Prime p) {k : Nat}
  proof: by
  induction k with
  | zero => simp [emultiplicity_of_one_right hp.not_isUnit]
  | succ k hk => simp [pow_succ, emultiplicity_mul hp, hk, add_mul]

中文:
定理 emultiplicity_pow
  条件: {p a : α} (hp : Prime p) {k : 自然数}
  证明: by
  induction k with
  | zero => simp [emultiplicity_of_one_right hp.not_isUnit]
  | succ k hk => simp [pow_succ, emultiplicity_mul hp, hk, add_mul]

Depends on / 依赖: add_mul, emultiplicity_mul, emultiplicity_of_one_right, hp.not_isUnit, not_isUnit, pow_succ
-/
theorem emultiplicity_pow {p a : α} (hp : Prime p) {k : Nat} :
    emultiplicity p (a ^ k) = k * emultiplicity p a := by
  induction k with
  | zero => simp [emultiplicity_of_one_right hp.not_isUnit]
  | succ k hk => simp [pow_succ, emultiplicity_mul hp, hk, add_mul]

/--
theorem `FiniteMultiplicity.multiplicity_pow` / 定理 `FiniteMultiplicity.multiplicity_pow`

English:
theorem FiniteMultiplicity.multiplicity_pow
  statement: {p a : α} (hp : Prime p)
  proof: by
  exact_mod_cast (ha.pow hp).emultiplicity_eq_multiplicity ▸
    ha.emultiplicity_eq_multiplicity ▸ emultiplicity_pow hp

中文:
定理 FiniteMultiplicity.multiplicity_pow
  结论: {p a : α} (hp : Prime p)
  证明: by
  exact_mod_cast (ha.pow hp).emultiplicity_eq_multiplicity ▸
    ha.emultiplicity_eq_multiplicity ▸ emultiplicity_pow hp
-/
protected theorem FiniteMultiplicity.multiplicity_pow {p a : α} (hp : Prime p)
    (ha : FiniteMultiplicity p a) {k : Nat} : multiplicity p (a ^ k) = k * multiplicity p a := by
  exact_mod_cast (ha.pow hp).emultiplicity_eq_multiplicity ▸
    ha.emultiplicity_eq_multiplicity ▸ emultiplicity_pow hp

/--
theorem `emultiplicity_pow_self` / 定理 `emultiplicity_pow_self`

English:
theorem emultiplicity_pow_self
  given: {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : Nat)
  proof: by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · rfl
  · rw [pow_dvd_pow_iff h0 hu]
    apply Nat.not_succ_le_self

中文:
定理 emultiplicity_pow_self
  条件: {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : 自然数)
  证明: by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · rfl
  · rw [pow_dvd_pow_iff h0 hu]
    apply Nat.not_succ_le_self

Depends on / 依赖: Nat.not_succ_le_self, emultiplicity_eq_of_dvd_of_not_dvd, not_succ_le_self, pow_dvd_pow_iff
-/
theorem emultiplicity_pow_self {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : Nat) :
    emultiplicity p (p ^ n) = n := by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · rfl
  · rw [pow_dvd_pow_iff h0 hu]
    apply Nat.not_succ_le_self

/--
theorem `multiplicity_pow_self` / 定理 `multiplicity_pow_self`

English:
theorem multiplicity_pow_self
  given: {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : Nat)
  proof: multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_pow_self h0 hu n)

中文:
定理 multiplicity_pow_self
  条件: {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : 自然数)
  证明: multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_pow_self h0 hu n)

Depends on / 依赖: emultiplicity_pow_self, multiplicity_eq_of_emultiplicity_eq_some
-/
theorem multiplicity_pow_self {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : Nat) :
    multiplicity p (p ^ n) = n :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_pow_self h0 hu n)

/--
theorem `emultiplicity_pow_self_of_prime` / 定理 `emultiplicity_pow_self_of_prime`

English:
theorem emultiplicity_pow_self_of_prime
  given: {p : α} (hp : Prime p) (n : Nat)
  proof: emultiplicity_pow_self hp.ne_zero hp.not_isUnit n

中文:
定理 emultiplicity_pow_self_of_prime
  条件: {p : α} (hp : Prime p) (n : 自然数)
  证明: emultiplicity_pow_self hp.ne_zero hp.not_isUnit n

Depends on / 依赖: emultiplicity_pow_self, hp.ne_zero, hp.not_isUnit, ne_zero, not_isUnit
-/
theorem emultiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : Nat) :
    emultiplicity p (p ^ n) = n :=
  emultiplicity_pow_self hp.ne_zero hp.not_isUnit n

/--
theorem `multiplicity_pow_self_of_prime` / 定理 `multiplicity_pow_self_of_prime`

English:
theorem multiplicity_pow_self_of_prime
  given: {p : α} (hp : Prime p) (n : Nat)
  proof: multiplicity_pow_self hp.ne_zero hp.not_isUnit n

中文:
定理 multiplicity_pow_self_of_prime
  条件: {p : α} (hp : Prime p) (n : 自然数)
  证明: multiplicity_pow_self hp.ne_zero hp.not_isUnit n

Depends on / 依赖: hp.ne_zero, hp.not_isUnit, multiplicity_pow_self, ne_zero, not_isUnit
-/
theorem multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : Nat) :
    multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.ne_zero hp.not_isUnit n

end CancelCommMonoidWithZero

section Nat

/--
theorem `multiplicity_eq_zero_of_coprime` / 定理 `multiplicity_eq_zero_of_coprime`

English:
theorem multiplicity_eq_zero_of_coprime
  statement: {p a b : Nat} (hp : p != 1)
  proof: by
  apply Nat.eq_zero_of_not_pos
  intro nh
  have da : p ∣ a := by simpa [multiplicity_eq_zero] using nh.ne.symm
  have db : p ∣ b := by simpa [multiplicity_eq_zero] using (nh.trans_le hle).ne.symm
  have := Nat.dvd_gcd da db
  rw [Coprime.gcd_eq_one hab]; rw [Nat.dvd_one] at this
  exact hp this

中文:
定理 multiplicity_eq_zero_of_coprime
  结论: {p a b : 自然数} (hp : p != 1)
  证明: by
  apply Nat.eq_zero_of_not_pos
  intro nh
  have da : p ∣ a := by simpa [multiplicity_eq_zero] using nh.ne.symm
  have db : p ∣ b := by simpa [multiplicity_eq_zero] using (nh.trans_le hle).ne.symm
  have := Nat.dvd_gcd da db
  rw [Coprime.gcd_eq_one hab]; rw [Nat.dvd_one] at this
  exact hp this

Depends on / 依赖: Coprime, Coprime.gcd_eq_one, Nat.dvd_gcd, Nat.dvd_one, Nat.eq_zero_of_not_pos, dvd_gcd, dvd_one, eq_zero_of_not_pos, gcd_eq_one, multiplicity_eq_zero, ne.symm, nh.ne.symm, nh.trans_le, trans_le
-/
theorem multiplicity_eq_zero_of_coprime {p a b : Nat} (hp : p != 1)
    (hle : multiplicity p a <= multiplicity p b) (hab : Nat.Coprime a b) : multiplicity p a = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro nh
  have da : p ∣ a := by simpa [multiplicity_eq_zero] using nh.ne.symm
  have db : p ∣ b := by simpa [multiplicity_eq_zero] using (nh.trans_le hle).ne.symm
  have := Nat.dvd_gcd da db
  rw [Coprime.gcd_eq_one hab]; rw [Nat.dvd_one] at this
  exact hp this

end Nat

/--
theorem `Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs` / 定理 `Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs`

English:
theorem Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs
  given: {a b : Int}
  proof: by
  simp only [FiniteMultiplicity.def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]

中文:
定理 Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs
  条件: {a b : 整数}
  证明: by
  simp only [FiniteMultiplicity.def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.def, Int.natAbs_dvd_natAbs, Int.natAbs_pow, natAbs_dvd_natAbs, natAbs_pow
-/
theorem Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs {a b : Int} :
    FiniteMultiplicity a b ↔ FiniteMultiplicity a.natAbs b.natAbs := by
  simp only [FiniteMultiplicity.def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]

/--
theorem `Int.finiteMultiplicity_iff` / 定理 `Int.finiteMultiplicity_iff`

English:
theorem Int.finiteMultiplicity_iff
  given: {a b : Int}
  statement: FiniteMultiplicity a b ↔ a.natAbs != 1 ∧ b != 0
  proof: by
  rw [finiteMultiplicity_iff_finiteMultiplicity_natAbs]; rw [Nat.finiteMultiplicity_iff]; rw [pos_iff_ne_zero]; rw [Int.natAbs_ne_zero]

中文:
定理 Int.finiteMultiplicity_iff
  条件: {a b : 整数}
  结论: FiniteMultiplicity a b ↔ a.natAbs != 1 ∧ b != 0
  证明: by
  rw [finiteMultiplicity_iff_finiteMultiplicity_natAbs]; rw [Nat.finiteMultiplicity_iff]; rw [pos_iff_ne_zero]; rw [Int.natAbs_ne_zero]

Depends on / 依赖: Int.natAbs_ne_zero, Nat.finiteMultiplicity_iff, finiteMultiplicity_iff, finiteMultiplicity_iff_finiteMultiplicity_natAbs, natAbs_ne_zero, pos_iff_ne_zero
-/
theorem Int.finiteMultiplicity_iff {a b : Int} : FiniteMultiplicity a b ↔ a.natAbs != 1 ∧ b != 0 := by
  rw [finiteMultiplicity_iff_finiteMultiplicity_natAbs]; rw [Nat.finiteMultiplicity_iff]; rw [pos_iff_ne_zero]; rw [Int.natAbs_ne_zero]

/--
Instance `Nat.decidableFiniteMultiplicity` / 实例 `Nat.decidableFiniteMultiplicity`

English:
instance Nat.decidableFiniteMultiplicity
  signature: : DecidableRel fun a b : Nat => FiniteMultiplicity a b
  body: fun _ _ => decidable_of_iff' _ Nat.finiteMultiplicity_iff

中文:
实例 Nat.decidableFiniteMultiplicity
  签名: : DecidableRel fun a b : 自然数 => FiniteMultiplicity a b
  定义体: fun _ _ => decidable_of_iff' _ Nat.finiteMultiplicity_iff

Depends on / 依赖: Nat.finiteMultiplicity_iff, decidable_of_iff, finiteMultiplicity_iff
-/
instance Nat.decidableFiniteMultiplicity : DecidableRel fun a b : Nat => FiniteMultiplicity a b :=
  fun _ _ => decidable_of_iff' _ Nat.finiteMultiplicity_iff

/--
Instance `Int.decidableMultiplicityFinite` / 实例 `Int.decidableMultiplicityFinite`

English:
instance Int.decidableMultiplicityFinite
  signature: : DecidableRel fun a b : Int => FiniteMultiplicity a b
  body: fun _ _ => decidable_of_iff' _ Int.finiteMultiplicity_iff

中文:
实例 Int.decidableMultiplicityFinite
  签名: : DecidableRel fun a b : 整数 => FiniteMultiplicity a b
  定义体: fun _ _ => decidable_of_iff' _ Int.finiteMultiplicity_iff

Depends on / 依赖: Int.finiteMultiplicity_iff, decidable_of_iff, finiteMultiplicity_iff
-/
instance Int.decidableMultiplicityFinite : DecidableRel fun a b : Int => FiniteMultiplicity a b :=
  fun _ _ => decidable_of_iff' _ Int.finiteMultiplicity_iff
