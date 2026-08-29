/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# The lattice of ideals in a ring

Some basic results on lattice operations on ideals: `⊥`, `⊤`, `⊔`, `⊓`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

instance (priority := low) : IsTwoSided (⊥ : Ideal α) :=
  ⟨fun _ h => by rw [h, zero_mul]; exact zero_mem _⟩

instance (priority := low) : IsTwoSided (⊤ : Ideal α) := ⟨fun _ _ => trivial⟩

instance (priority := low) {ι} (I : ι -> Ideal α) [forall i, (I i).IsTwoSided] : (⨅ i, I i).IsTwoSided :=
  ⟨fun _ h => (Submodule.mem_iInf _).mpr (mul_mem_right _ _ <| (Submodule.mem_iInf _).mp h ·)⟩

/--
theorem `eq_top_of_unit_mem` / 定理 `eq_top_of_unit_mem`

English:
theorem eq_top_of_unit_mem
  given: (x y : α) (hx : x in I) (h : y * x = 1)
  statement: I = ⊤
  proof: eq_top_iff.2 fun z _ =>
    calc
      z * y * x in I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]

中文:
定理 eq_top_of_unit_mem
  条件: (x y : α) (hx : x in I) (h : y * x = 1)
  结论: I = ⊤
  证明: eq_top_iff.2 fun z _ =>
    calc
      z * y * x in I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]

Depends on / 依赖: I.mul_mem_left, eq_top_iff, mul_assoc, mul_mem_left, mul_one
-/
theorem eq_top_of_unit_mem (x y : α) (hx : x in I) (h : y * x = 1) : I = ⊤ :=
  eq_top_iff.2 fun z _ =>
    calc
      z * y * x in I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]

/--
theorem `eq_top_of_isUnit_mem` / 定理 `eq_top_of_isUnit_mem`

English:
theorem eq_top_of_isUnit_mem
  given: {x} (hx : x in I) (h : IsUnit x)
  statement: I = ⊤
  proof: let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy

中文:
定理 eq_top_of_isUnit_mem
  条件: {x} (hx : x in I) (h : 是单位 x)
  结论: I = ⊤
  证明: let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy

Depends on / 依赖: eq_top_of_unit_mem, exists_left_inv, h.exists_left_inv
-/
theorem eq_top_of_isUnit_mem {x} (hx : x in I) (h : IsUnit x) : I = ⊤ :=
  let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy

/--
theorem `eq_top_iff_one` / 定理 `eq_top_iff_one`

English:
theorem eq_top_iff_one
  statement: I = ⊤ ↔ (1 : α) in I
  proof: ⟨by rintro rfl; trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩

中文:
定理 eq_top_iff_one
  结论: I = ⊤ ↔ (1 : α) in I
  证明: ⟨by rintro rfl; trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩

Depends on / 依赖: eq_top_of_unit_mem
-/
theorem eq_top_iff_one : I = ⊤ ↔ (1 : α) in I :=
  ⟨by rintro rfl; trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩

/--
theorem `ne_top_iff_one` / 定理 `ne_top_iff_one`

English:
theorem ne_top_iff_one
  statement: I != ⊤ ↔ (1 : α) ∉ I
  proof: not_congr I.eq_top_iff_one

中文:
定理 ne_top_iff_one
  结论: I != ⊤ ↔ (1 : α) ∉ I
  证明: not_congr I.eq_top_iff_one

Depends on / 依赖: I.eq_top_iff_one, eq_top_iff_one, not_congr
-/
theorem ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I :=
  not_congr I.eq_top_iff_one

section Lattice

variable {R : Type u} [Semiring R]

/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {S T : Ideal R}
  statement: forall {x : R}, x in S -> x in S ⊔ T
  proof: @le_sup_left _ _ S T

中文:
定理 mem_sup_left
  条件: {S T : 理想 R}
  结论: 对任意 {x : R}, x in S -> x in S ⊔ T
  证明: @le_sup_left _ _ S T

Depends on / 依赖: le_sup_left
-/
theorem mem_sup_left {S T : Ideal R} : forall {x : R}, x in S -> x in S ⊔ T :=
  @le_sup_left _ _ S T

/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {S T : Ideal R}
  statement: forall {x : R}, x in T -> x in S ⊔ T
  proof: @le_sup_right _ _ S T

中文:
定理 mem_sup_right
  条件: {S T : 理想 R}
  结论: 对任意 {x : R}, x in T -> x in S ⊔ T
  证明: @le_sup_right _ _ S T

Depends on / 依赖: le_sup_right
-/
theorem mem_sup_right {S T : Ideal R} : forall {x : R}, x in T -> x in S ⊔ T :=
  @le_sup_right _ _ S T

/--
theorem `mem_iSup_of_mem` / 定理 `mem_iSup_of_mem`

English:
theorem mem_iSup_of_mem
  given: {ι : Sort*} {S : ι -> Ideal R} (i : ι)
  statement: forall {x : R}, x in S i -> x in iSup S
  proof: @le_iSup _ _ _ S _

中文:
定理 mem_iSup_of_mem
  条件: {ι : 类型层*} {S : ι -> 理想 R} (i : ι)
  结论: 对任意 {x : R}, x in S i -> x in iSup S
  证明: @le_iSup _ _ _ S _

Depends on / 依赖: le_iSup
-/
theorem mem_iSup_of_mem {ι : Sort*} {S : ι -> Ideal R} (i : ι) : forall {x : R}, x in S i -> x in iSup S :=
  @le_iSup _ _ _ S _

/--
theorem `mem_sSup_of_mem` / 定理 `mem_sSup_of_mem`

English:
theorem mem_sSup_of_mem
  given: {S : Set (Ideal R)} {s : Ideal R} (hs : s in S)
  proof: @le_sSup _ _ _ _ hs

中文:
定理 mem_sSup_of_mem
  条件: {S : 集合 (理想 R)} {s : 理想 R} (hs : s in S)
  证明: @le_sSup _ _ _ _ hs

Depends on / 依赖: le_sSup
-/
theorem mem_sSup_of_mem {S : Set (Ideal R)} {s : Ideal R} (hs : s in S) :
    forall {x : R}, x in s -> x in sSup S :=
  @le_sSup _ _ _ _ hs

/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {s : Set (Ideal R)} {x : R}
  statement: x in sInf s ↔ forall ⦃I⦄, I in s -> x in I
  proof: ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H _I ⟨_J, hij⟩ => hij ▸ fun _S ⟨hj, hS⟩ => hS ▸ H hj⟩

中文:
定理 mem_sInf
  条件: {s : 集合 (理想 R)} {x : R}
  结论: x in sInf s ↔ 对任意 ⦃I⦄, I in s -> x in I
  证明: ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H _I ⟨_J, hij⟩ => hij ▸ fun _S ⟨hj, hS⟩ => hS ▸ H hj⟩

Depends on / 依赖: iInf_pos
-/
theorem mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ forall ⦃I⦄, I in s -> x in I :=
  ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H _I ⟨_J, hij⟩ => hij ▸ fun _S ⟨hj, hS⟩ => hS ▸ H hj⟩

/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {I J : Ideal R} {x : R}
  statement: x in I ⊓ J ↔ x in I ∧ x in J
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {I J : 理想 R} {x : R}
  结论: x in I ⊓ J ↔ x in I ∧ x in J
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {I J : Ideal R} {x : R} : x in I ⊓ J ↔ x in I ∧ x in J :=
  Iff.rfl

/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {I : ι -> Ideal R} {x : R}
  statement: x in iInf I ↔ forall i, x in I i
  proof: Submodule.mem_iInf _

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {I : ι -> 理想 R} {x : R}
  结论: x in iInf I ↔ 对任意 i, x in I i
  证明: Submodule.mem_iInf _

Depends on / 依赖: Submodule, Submodule.mem_iInf, mem_iInf
-/
theorem mem_iInf {ι : Sort*} {I : ι -> Ideal R} {x : R} : x in iInf I ↔ forall i, x in I i :=
  Submodule.mem_iInf _

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : R}
  statement: x in (⊥ : Ideal R) ↔ x = 0
  proof: Submodule.mem_bot _

中文:
定理 mem_bot
  条件: {x : R}
  结论: x in (⊥ : 理想 R) ↔ x = 0
  证明: Submodule.mem_bot _

Depends on / 依赖: Submodule, Submodule.mem_bot, mem_bot
-/
theorem mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0 :=
  Submodule.mem_bot _

end Lattice

end Ideal

end Semiring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/--
theorem `eq_bot_or_top` / 定理 `eq_bot_or_top`

English:
theorem eq_bot_or_top
  statement: I = ⊥ ∨ I = ⊤
  proof: by
  rw [or_iff_not_imp_right]
  change _ != _ -> _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr

中文:
定理 eq_bot_or_top
  结论: I = ⊥ ∨ I = ⊤
  证明: by
  rw [or_iff_not_imp_right]
  change _ != _ -> _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr

Depends on / 依赖: I.mul_mem_left, Ideal.ne_top_iff_one, eq_bot_iff, mul_mem_left, ne_top_iff_one, or_iff_not_imp_right
-/
theorem eq_bot_or_top : I = ⊥ ∨ I = ⊤ := by
  rw [or_iff_not_imp_right]
  change _ != _ -> _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr

end Ideal

end DivisionSemiring
