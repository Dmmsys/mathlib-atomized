/-
Copyright (c) 2024 Jujian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Kernel of a ring homomorphism as a two-sided ideal

In this file we define the kernel of a ring homomorphism `f : R → S` as a two-sided ideal of `R`.

We put this in a separate file so that we could import it in
`Mathlib/RingTheory/SimpleRing/Basic.lean` without importing any finiteness result.
-/

@[expose] public section

namespace TwoSidedIdeal

section ker

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
variable (f : F)

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : TwoSidedIdeal R
  body: .ofRingCon
  -- TODO: use `RingCon.ker`
  { r := fun x y => f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all
    add' := by intro; simp_all }

@[simp]

中文:
定义 ker
  签名: : TwoSided理想 R
  定义体: .ofRingCon
  -- TODO: use `RingCon.ker`
  { r := fun x y => f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all
    add' := by intro; simp_all }

@[simp]

Depends on / 依赖: ofRingCon
-/
def ker : TwoSidedIdeal R :=
  .ofRingCon
  -- TODO: use `RingCon.ker`
  { r := fun x y => f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all
    add' := by intro; simp_all }

@[simp]
/--
lemma `ker_ringCon` / 引理 `ker_ringCon`

English:
lemma ker_ringCon
  given: {x y : R}
  statement: (ker f).ringCon x y ↔ f x = f y
  proof: Iff.rfl

中文:
引理 ker_ringCon
  条件: {x y : R}
  结论: (ker f).ringCon x y ↔ f x = f y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ker_ringCon {x y : R} : (ker f).ringCon x y ↔ f x = f y := Iff.rfl

/--
lemma `mem_ker` / 引理 `mem_ker`

English:
lemma mem_ker
  given: {x : R}
  statement: x in ker f ↔ f x = 0
  proof: by
  rw [mem_iff]; rw [ker_ringCon]; rw [map_zero]

中文:
引理 mem_ker
  条件: {x : R}
  结论: x in ker f ↔ f x = 0
  证明: by
  rw [mem_iff]; rw [ker_ringCon]; rw [map_zero]

Depends on / 依赖: ker_ringCon, map_zero, mem_iff
-/
lemma mem_ker {x : R} : x in ker f ↔ f x = 0 := by
  rw [mem_iff]; rw [ker_ringCon]; rw [map_zero]

/--
lemma `ker_eq_bot` / 引理 `ker_eq_bot`

English:
lemma ker_eq_bot
  statement: ker f = ⊥ ↔ Function.Injective f
  proof: by
  fconstructor
  · intro h x y hxy
    simpa [h, rel_iff, mem_bot, sub_eq_zero] using show (ker f).ringCon x y from hxy
  · exact fun h => eq_bot_iff.2 fun x hx => h hx

中文:
引理 ker_eq_bot
  结论: ker f = ⊥ ↔ 函数.单射 f
  证明: by
  fconstructor
  · intro h x y hxy
    simpa [h, rel_iff, mem_bot, sub_eq_zero] using show (ker f).ringCon x y from hxy
  · exact fun h => eq_bot_iff.2 fun x hx => h hx

Depends on / 依赖: eq_bot_iff, fconstructor, mem_bot, rel_iff, ringCon, sub_eq_zero
-/
lemma ker_eq_bot : ker f = ⊥ ↔ Function.Injective f := by
  fconstructor
  · intro h x y hxy
    simpa [h, rel_iff, mem_bot, sub_eq_zero] using show (ker f).ringCon x y from hxy
  · exact fun h => eq_bot_iff.2 fun x hx => h hx

section NonAssocRing

variable {R : Type*} [NonAssocRing R]

/--
The kernel of the ring homomorphism `R → R⧸I` is `I`.
-/
@[simp]
/--
lemma `ker_ringCon_mk'` / 引理 `ker_ringCon_mk'`

English:
lemma ker_ringCon_mk'
  given: (I : TwoSidedIdeal R)
  statement: ker I.ringCon.mk' = I
  proof: le_antisymm
    (fun _ h => by simpa using I.rel_iff _ _ |>.1 (Quotient.eq'.1 h))
    (fun _ h => Quotient.sound' <| I.rel_iff _ _ |>.2 (by simpa using h))

中文:
引理 ker_ringCon_mk'
  条件: (I : TwoSided理想 R)
  结论: ker I.ringCon.mk' = I
  证明: le_antisymm
    (fun _ h => by simpa using I.rel_iff _ _ |>.1 (Quotient.eq'.1 h))
    (fun _ h => Quotient.sound' <| I.rel_iff _ _ |>.2 (by simpa using h))

Depends on / 依赖: I.rel_iff, Quotient, Quotient.eq, Quotient.sound, le_antisymm, rel_iff
-/
lemma ker_ringCon_mk' (I : TwoSidedIdeal R) : ker I.ringCon.mk' = I :=
  le_antisymm
    (fun _ h => by simpa using I.rel_iff _ _ |>.1 (Quotient.eq'.1 h))
    (fun _ h => Quotient.sound' <| I.rel_iff _ _ |>.2 (by simpa using h))

end NonAssocRing

end ker

end TwoSidedIdeal
