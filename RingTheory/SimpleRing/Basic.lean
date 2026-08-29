/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-! # Basic Properties of Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main results

- `IsSimpleRing.instNontrivial`: simple rings are non-trivial.
- `DivisionRing.isSimpleRing`: division rings are simple.
- `RingHom.injective`: every ring homomorphism from a simple ring to a nontrivial ring is injective.
- `IsSimpleRing.iff_injective_ringHom`: a ring is simple iff every ring homomorphism to a nontrivial
  ring is injective.

-/

public section

variable (R : Type*) [NonUnitalNonAssocRing R]

namespace IsSimpleRing

variable {R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSimpleRing
  signature: R] : Nontrivial R
  body: by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (bot_lt_top : (⊥ : TwoSidedIdeal R) < ⊤)
  use x, 0, hx

中文:
实例 [IsSimpleRing
  签名: R] : Nontrivial R
  定义体: by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (bot_lt_top : (⊥ : TwoSidedIdeal R) < ⊤)
  use x, 0, hx

Depends on / 依赖: SetLike, SetLike.exists_of_lt, TwoSidedIdeal, bot_lt_top, exists_of_lt
-/
instance [IsSimpleRing R] : Nontrivial R := by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (bot_lt_top : (⊥ : TwoSidedIdeal R) < ⊤)
  use x, 0, hx

attribute [instance 200] IsSimpleRing.instNontrivial

/--
lemma `one_mem_of_ne_bot` / 引理 `one_mem_of_ne_bot`

English:
lemma one_mem_of_ne_bot
  statement: {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
  proof: (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩

中文:
引理 one_mem_of_ne_bot
  结论: {A : 类型} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
  证明: (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩

Depends on / 依赖: eq_bot_or_eq_top, resolve_left
-/
lemma one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    (hI : I != ⊥) : (1 : A) in I :=
  (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩

/--
lemma `one_mem_of_ne_zero_mem` / 引理 `one_mem_of_ne_zero_mem`

English:
lemma one_mem_of_ne_zero_mem
  statement: {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
  proof: one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)

中文:
引理 one_mem_of_ne_zero_mem
  结论: {A : 类型} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
  证明: one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)

Depends on / 依赖: one_mem_of_ne_bot
-/
lemma one_mem_of_ne_zero_mem {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    {x : A} (hx : x != 0) (hxI : x in I) : (1 : A) in I :=
  one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)

/--
lemma `of_eq_bot_or_eq_top` / 引理 `of_eq_bot_or_eq_top`

English:
lemma of_eq_bot_or_eq_top
  given: [Nontrivial R] (h : forall I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤)
  proof: h

中文:
引理 of_eq_bot_or_eq_top
  条件: [Nontrivial R] (h : 对任意 I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤)
  证明: h
-/
lemma of_eq_bot_or_eq_top [Nontrivial R] (h : forall I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤) :
    IsSimpleRing R where
  simple.eq_bot_or_eq_top := h

/--
Instance `_root_.DivisionRing.isSimpleRing` / 实例 `_root_.DivisionRing.isSimpleRing`

English:
instance _root_.DivisionRing.isSimpleRing
  signature: (A : Type*) [DivisionRing A]
  body: .of_eq_bot_or_eq_top fun I => by
    rw [or_iff_not_imp_left]; rw [← I.one_mem_iff]
    intro H
    obtain ⟨x, hx1, hx2 : x != 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr H : ⊥ < I)
    simpa [inv_mul_cancel₀ hx2] using I.mul_mem_left x⁻¹ _ hx1

中文:
实例 _root_.DivisionRing.isSimpleRing
  签名: (A : 类型) [DivisionRing A]
  定义体: .of_eq_bot_or_eq_top fun I => by
    rw [or_iff_not_imp_left]; rw [← I.one_mem_iff]
    intro H
    obtain ⟨x, hx1, hx2 : x != 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr H : ⊥ < I)
    simpa [inv_mul_cancel₀ hx2] using I.mul_mem_left x⁻¹ _ hx1

Depends on / 依赖: I.mul_mem_left, I.one_mem_iff, SetLike, SetLike.exists_of_lt, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, exists_of_lt, mul_mem_left, of_eq_bot_or_eq_top, one_mem_iff, or_iff_not_imp_left
-/
instance _root_.DivisionRing.isSimpleRing (A : Type*) [DivisionRing A] : IsSimpleRing A :=
.of_eq_bot_or_eq_top fun I => by
    rw [or_iff_not_imp_left]; rw [← I.one_mem_iff]
    intro H
    obtain ⟨x, hx1, hx2 : x != 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr H : ⊥ < I)
    simpa [inv_mul_cancel₀ hx2] using I.mul_mem_left x⁻¹ _ hx1

/--
lemma `injective_ringHom_or_subsingleton_codomain` / 引理 `injective_ringHom_or_subsingleton_codomain`

English:
lemma injective_ringHom_or_subsingleton_codomain
  proof: .imp (TwoSidedIdeal.ker_eq_bot _ |>.1) simple.eq_bot_or_eq_top (TwoSidedIdeal.ker f)
    (fun h => subsingleton_iff_zero_eq_one.1 <| by
      have mem : 1 in TwoSidedIdeal.ker f := h.symm ▸ TwoSidedIdeal.mem_top _
      rwa [TwoSidedIdeal.mem_ker, map_one, eq_comm] at mem)

中文:
引理 injective_ringHom_or_subsingleton_codomain
  证明: .imp (TwoSidedIdeal.ker_eq_bot _ |>.1) simple.eq_bot_or_eq_top (TwoSidedIdeal.ker f)
    (fun h => subsingleton_iff_zero_eq_one.1 <| by
      have mem : 1 in TwoSidedIdeal.ker f := h.symm ▸ TwoSidedIdeal.mem_top _
      rwa [TwoSidedIdeal.mem_ker, map_one, eq_comm] at mem)

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.ker, TwoSidedIdeal.ker_eq_bot, TwoSidedIdeal.mem_ker, TwoSidedIdeal.mem_top, eq_bot_or_eq_top, eq_comm, h.symm, ker_eq_bot, map_one, mem_ker, mem_top, simple, simple.eq_bot_or_eq_top, subsingleton_iff_zero_eq_one
-/
lemma injective_ringHom_or_subsingleton_codomain
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S]
    (f : R ->+* S) : Function.Injective f ∨ Subsingleton S :=
.imp (TwoSidedIdeal.ker_eq_bot _ |>.1) simple.eq_bot_or_eq_top (TwoSidedIdeal.ker f)
    (fun h => subsingleton_iff_zero_eq_one.1 <| by
      have mem : 1 in TwoSidedIdeal.ker f := h.symm ▸ TwoSidedIdeal.mem_top _
      rwa [TwoSidedIdeal.mem_ker, map_one, eq_comm] at mem)

/--
theorem `_root_.RingHom.injective` / 定理 `_root_.RingHom.injective`

English:
theorem _root_.RingHom.injective
  proof: .resolve_right fun r => not_subsingleton _ r injective_ringHom_or_subsingleton_codomain f

universe u in

中文:
定理 _root_.RingHom.injective
  证明: .resolve_right fun r => not_subsingleton _ r injective_ringHom_or_subsingleton_codomain f

universe u in
-/
protected theorem _root_.RingHom.injective
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S] [Nontrivial S]
    (f : R ->+* S) : Function.Injective f :=
.resolve_right fun r => not_subsingleton _ r injective_ringHom_or_subsingleton_codomain f

universe u in
/--
lemma `iff_injective_ringHom_or_subsingleton_codomain` / 引理 `iff_injective_ringHom_or_subsingleton_codomain`

English:
lemma iff_injective_ringHom_or_subsingleton_codomain
  given: (R : Type u) [NonAssocRing R] [Nontrivial R]
  proof: injective_ringHom_or_subsingleton_codomain
.imp mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk'
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.

中文:
引理 iff_injective_ringHom_or_subsingleton_codomain
  条件: (R : 类型u) [NonAssocRing R] [Nontrivial R]
  证明: injective_ringHom_or_subsingleton_codomain
.imp mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk'
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.

Depends on / 依赖: injective_ringHom_or_subsingleton_codomain
-/
lemma iff_injective_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    forall {S : Type u} [NonAssocSemiring S] (f : R ->+* S), Function.Injective f ∨ Subsingleton S where
  mp _ _ _ := injective_ringHom_or_subsingleton_codomain
.imp mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk'
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.elim x 0)))

universe u in
/--
lemma `iff_injective_ringHom` / 引理 `iff_injective_ringHom`

English:
lemma iff_injective_ringHom
  given: (R : Type u) [NonAssocRing R] [Nontrivial R]
  proof: .trans iff_injective_ringHom_or_subsingleton_codomain R
.resolve_right (by simpa [not_subsingleton_iff_nontrivial]), ⟨fun H _ _ _ f => H f
.recOn Or.inr fun _ => Or.inl H f⟩ fun H S _ f => subsingleton_or_nontrivial S

中文:
引理 iff_injective_ringHom
  条件: (R : 类型u) [NonAssocRing R] [Nontrivial R]
  证明: .trans iff_injective_ringHom_or_subsingleton_codomain R
.resolve_right (by simpa [not_subsingleton_iff_nontrivial]), ⟨fun H _ _ _ f => H f
.recOn Or.inr fun _ => Or.inl H f⟩ fun H S _ f => subsingleton_or_nontrivial S

Depends on / 依赖: Or.inl, Or.inr, iff_injective_ringHom_or_subsingleton_codomain, not_subsingleton_iff_nontrivial, resolve_right, subsingleton_or_nontrivial
-/
lemma iff_injective_ringHom (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    forall {S : Type u} [NonAssocSemiring S] [Nontrivial S] (f : R ->+* S), Function.Injective f :=
.trans iff_injective_ringHom_or_subsingleton_codomain R
.resolve_right (by simpa [not_subsingleton_iff_nontrivial]), ⟨fun H _ _ _ f => H f
.recOn Or.inr fun _ => Or.inl H f⟩ fun H S _ f => subsingleton_or_nontrivial S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSimpleRing
  signature: R] : IsSimpleRing Rᵐᵒᵖ
  body: ⟨TwoSidedIdeal.opOrderIso.symm.isSimpleOrder⟩

中文:
实例 [IsSimpleRing
  签名: R] : IsSimpleRing Rᵐᵒᵖ
  定义体: ⟨TwoSidedIdeal.opOrderIso.symm.isSimpleOrder⟩

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.opOrderIso.symm.isSimpleOrder, isSimpleOrder, opOrderIso
-/
instance [IsSimpleRing R] : IsSimpleRing Rᵐᵒᵖ := ⟨TwoSidedIdeal.opOrderIso.symm.isSimpleOrder⟩

end IsSimpleRing
