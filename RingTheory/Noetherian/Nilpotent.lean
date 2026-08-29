/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Nilpotent ideals in Noetherian rings


## Main results

* `IsNoetherianRing.isNilpotent_nilradical`
-/

public section

open IsNoetherian

/--
theorem `IsNoetherianRing.isNilpotent_nilradical` / 定理 `IsNoetherianRing.isNilpotent_nilradical`

English:
theorem IsNoetherianRing.isNilpotent_nilradical
  given: (R : Type*) [CommSemiring R] [IsNoetherianRing R]
  proof: by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩

中文:
定理 IsNoetherianRing.isNilpotent_nilradical
  条件: (R : 类型) [CommSemiring R] [IsNoetherianRing R]
  证明: by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩

Depends on / 依赖: Ideal.exists_radical_pow_le_of_fg, IsNoetherian, IsNoetherian.noetherian, eq_bot_iff, eq_bot_iff.mpr, exists_radical_pow_le_of_fg, noetherian
-/
theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommSemiring R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) := by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩

/--
lemma `Ideal.FG.isNilpotent_iff_le_nilradical` / 引理 `Ideal.FG.isNilpotent_iff_le_nilradical`

English:
lemma Ideal.FG.isNilpotent_iff_le_nilradical
  statement: {R : Type*} [CommSemiring R] {I : Ideal R}
  proof: ⟨fun ⟨n, hn⟩ _ hx => ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
    fun h => let ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI; ⟨n, le_bot_iff.mp hn⟩⟩

中文:
引理 Ideal.FG.isNilpotent_iff_le_nilradical
  结论: {R : 类型} [CommSemiring R] {I : Ideal R}
  证明: ⟨fun ⟨n, hn⟩ _ hx => ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
    fun h => let ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI; ⟨n, le_bot_iff.mp hn⟩⟩

Depends on / 依赖: Ideal.pow_mem_pow, exists_pow_le_of_le_radical_of_fg, le_bot_iff, le_bot_iff.mp, pow_mem_pow
-/
lemma Ideal.FG.isNilpotent_iff_le_nilradical {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : I.FG) : IsNilpotent I ↔ I <= nilradical R :=
  ⟨fun ⟨n, hn⟩ _ hx => ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
    fun h => let ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI; ⟨n, le_bot_iff.mp hn⟩⟩
