/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda,
  Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser
-/
module

public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
public import Mathlib.Algebra.Ring.Divisibility.Lemmas

/-!
# Fermat Last Theorem in the case `n = 3`

The goal of this file is to prove Fermat's Last Theorem in the case `n = 3`.

## Main results
* `fermatLastTheoremThree`: Fermat's Last Theorem for `n = 3`: if `a b c : ℕ` are all non-zero then
  `a ^ 3 + b ^ 3 ≠ c ^ 3`.

## Implementation details
We follow the proof in <https://webusers.imj-prg.fr/~marc.hindry/Cours-arith.pdf>, page 43.

The strategy is the following:
* The so-called "Case 1", when `3 ∣ a * b * c` is completely elementary and is proved using
  congruences modulo `9`.
* To prove case 2, we consider the generalized equation `a ^ 3 + b ^ 3 = u * c ^ 3`, where `a`, `b`,
  and `c` are in the cyclotomic ring `ℤ[ζ₃]` (where `ζ₃` is a primitive cube root of unity) and `u`
  is a unit of `ℤ[ζ₃]`. `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` (whose proof is
  rather elementary on paper) says that to prove Fermat's last theorem for exponent `3`, it is
  enough to prove that this equation has no solutions such that `c ≠ 0`, `¬ λ ∣ a`, `¬ λ ∣ b`,
  `λ ∣ c` and `IsCoprime a b` (where we set `λ := ζ₃ - 1`). We call such a tuple a `Solution'`.
  A `Solution` is the same as a `Solution'` with the additional assumption that `λ ^ 2 ∣ a + b`.
  We then prove that, given `S' : Solution'`, there is `S : Solution` such that the multiplicity of
  `λ = ζ₃ - 1` in `c` is the same in `S'` and `S` (see `exists_Solution_of_Solution'`).
  In particular it is enough to prove that no `Solution` exists. The key point is a descent argument
  on the multiplicity of `λ` in `c`: starting with `S : Solution` we can find `S₁ : Solution` with
  multiplicity strictly smaller (see `exists_Solution_multiplicity_lt`) and this finishes the proof.
  To construct `S₁` we go through a `Solution'` and then back to a `Solution`. More importantly, we
  cannot control the unit `u`, and this is the reason why we need to consider the generalized
  equation `a ^ 3 + b ^ 3 = u * c ^ 3`. The construction is completely explicit, but it depends
  crucially on `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`, a special
  case of Kummer's lemma.
* Note that we don't prove Case 1 for the generalized equation (in particular we don't prove that
  the generalized equation has no nontrivial solutions). This is because the proof, even if
  elementary on paper, would be quite annoying to formalize: indeed it involves a lot of explicit
  computations in `ℤ[ζ₃] / (λ)`: this ring is isomorphic to `ℤ / 9ℤ`, but of course, even if we
  construct such an isomorphism, tactics like `decide` would not work.

-/

section case1

open ZMod

/--
lemma `cube_of_castHom_ne_zero` / 引理 `cube_of_castHom_ne_zero`

English:
lemma cube_of_castHom_ne_zero
  given: {n : ZMod 9}
  proof: by
  revert n; decide

中文:
引理 cube_of_castHom_ne_zero
  条件: {n : ZMod 9}
  证明: by
  revert n; decide

Depends on / 依赖: revert
-/
lemma cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by simp) (ZMod 3) n != 0 -> n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  revert n; decide

/--
lemma `cube_of_not_dvd` / 引理 `cube_of_not_dvd`

English:
lemma cube_of_not_dvd
  given: {n : Int} (h : ¬ 3 ∣ n)
  proof: by
  apply cube_of_castHom_ne_zero
  rwa [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

中文:
引理 cube_of_not_dvd
  条件: {n : 整数} (h : ¬ 3 ∣ n)
  证明: by
  apply cube_of_castHom_ne_zero
  rwa [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

Depends on / 依赖: ZMod.intCast_zmod_eq_zero_iff_dvd, cube_of_castHom_ne_zero, intCast_zmod_eq_zero_iff_dvd, map_intCast
-/
lemma cube_of_not_dvd {n : Int} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rwa [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/--
theorem `fermatLastTheoremThree_case_1` / 定理 `fermatLastTheoremThree_case_1`

English:
theorem fermatLastTheoremThree_case_1
  given: {a b c : Int} (hdvd : ¬ 3 ∣ a * b * c)
  proof: by
  simp_rw [Int.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Int.cast : Int -> ZMod 9))
  simp_rw [Int.cast_add, Int.cast_pow]
  rcases cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [

中文:
定理 fermatLastTheoremThree_case_1
  条件: {a b c : 整数} (hdvd : ¬ 3 ∣ a * b * c)
  证明: by
  simp_rw [Int.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Int.cast : Int -> ZMod 9))
  simp_rw [Int.cast_add, Int.cast_pow]
  rcases cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [

Depends on / 依赖: Int.cast, Int.cast_add, Int.cast_pow, Int.prime_three.dvd_mul, cast_add, cast_pow, cube_of_not_dvd, dvd_mul, not_or, prime_three, simp_rw
-/
theorem fermatLastTheoremThree_case_1 {a b c : Int} (hdvd : ¬ 3 ∣ a * b * c) :
    a ^ 3 + b ^ 3 != c ^ 3 := by
  simp_rw [Int.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Int.cast : Int -> ZMod 9))
  simp_rw [Int.cast_add, Int.cast_pow]
  rcases cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [ha]; rw [hb]; rw [hc] <;> decide

end case1

section case2

/--
lemma `three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2` / 引理 `three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2`

English:
lemma three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2
  statement: {a b c : Int} (ha : a != 0)
  proof: by
  have hbc : IsCoprime (-b) (-c) := by
    refine IsCoprime.neg_neg ?_
    rw [add_comm (a ^ 3)]; rw [add_assoc]; rw [add_comm (a ^ 3)]; rw [← add_assoc] at HF
    refine isCoprime_of_gcd_eq_one_of_FLT ?_ HF
    convert! Hgcd using 2
    rw [Finset.pair_comm]; rw [Finset.insert_comm]
  by_contra!

中文:
引理 three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2
  结论: {a b c : 整数} (ha : a != 0)
  证明: by
  have hbc : IsCoprime (-b) (-c) := by
    refine IsCoprime.neg_neg ?_
    rw [add_comm (a ^ 3)]; rw [add_assoc]; rw [add_comm (a ^ 3)]; rw [← add_assoc] at HF
    refine isCoprime_of_gcd_eq_one_of_FLT ?_ HF
    convert! Hgcd using 2
    rw [Finset.pair_comm]; rw [Finset.insert_comm]
  by_contra!

Depends on / 依赖: Finset, Finset.insert_comm, Finset.pair_comm, Int.prime_three, IsCoprime, IsCoprime.neg_neg, add_assoc, add_comm, convert, dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT, insert_comm, isCoprime_of_gcd_eq_one_of_FLT, neg_neg, pair_comm, prime_three
-/
lemma three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : Int} (ha : a != 0)
    (Hgcd : Finset.gcd {a, b, c} id = 1) (h3a : 3 ∣ a) (HF : a ^ 3 + b ^ 3 + c ^ 3 = 0)
    (H : forall a b c : Int, c != 0 -> ¬ 3 ∣ a -> ¬ 3 ∣ b -> 3 ∣ c -> IsCoprime a b -> a ^ 3 + b ^ 3 != c ^ 3) :
    3 ∣ b := by
  have hbc : IsCoprime (-b) (-c) := by
    refine IsCoprime.neg_neg ?_
    rw [add_comm (a ^ 3)]; rw [add_assoc]; rw [add_comm (a ^ 3)]; rw [← add_assoc] at HF
    refine isCoprime_of_gcd_eq_one_of_FLT ?_ HF
    convert! Hgcd using 2
    rw [Finset.pair_comm]; rw [Finset.insert_comm]
  by_contra! h3b
  by_cases h3c : 3 ∣ c
  · apply h3b
    rw [add_assoc]; rw [add_comm (b ^ 3)]; rw [← add_assoc] at HF
    exact dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3c HF
  · refine H (-b) (-c) a ha (by simp [h3b]) (by simp [h3c]) h3a hbc ?_
    rw [add_eq_zero_iff_eq_neg]; rw [← (show Odd 3 by decide).neg_pow] at HF
    rw [← HF]
    ring

open Finset in
/--
lemma `fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2` / 引理 `fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2`

English:
lemma fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2
  statement: {a b c : Int} (ha : a != 0)
  proof: by
  intro HF
  apply (show ¬(3 ∣ (1 : Int)) by decide)
  rw [← Hgcd]
  refine dvd_gcd (fun x hx => ?_)
  simp only [mem_insert, mem_singleton] at hx
  have h3b : 3 ∣ b := by
    refine three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 ha ?_ h3a HF H
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq

中文:
引理 fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2
  结论: {a b c : 整数} (ha : a != 0)
  证明: by
  intro HF
  apply (show ¬(3 ∣ (1 : Int)) by decide)
  rw [← Hgcd]
  refine dvd_gcd (fun x hx => ?_)
  simp only [mem_insert, mem_singleton] at hx
  have h3b : 3 ∣ b := by
    refine three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 ha ?_ h3a HF H
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq

Depends on / 依赖: Int.abs_eq_normalize, Int.prime_three, abs_eq_normalize, dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT, dvd_gcd, gcd_insert, gcd_singleton, id_eq, mem_insert, mem_singleton, prime_three, three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2
-/
lemma fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : Int} (ha : a != 0)
    (h3a : 3 ∣ a) (Hgcd : Finset.gcd {a, b, c} id = 1)
    (H : forall a b c : Int, c != 0 -> ¬ 3 ∣ a -> ¬ 3 ∣ b -> 3 ∣ c -> IsCoprime a b -> a ^ 3 + b ^ 3 != c ^ 3) :
    a ^ 3 + b ^ 3 + c ^ 3 != 0 := by
  intro HF
  apply (show ¬(3 ∣ (1 : Int)) by decide)
  rw [← Hgcd]
  refine dvd_gcd (fun x hx => ?_)
  simp only [mem_insert, mem_singleton] at hx
  have h3b : 3 ∣ b := by
    refine three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 ha ?_ h3a HF H
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← Int.abs_eq_normalize]
  rcases hx with hx | hx | hx
  · exact hx ▸ h3a
  · exact hx ▸ h3b
  · simpa [hx] using dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3b HF

open Finset Int in
/--
theorem `fermatLastTheoremThree_of_three_dvd_only_c` / 定理 `fermatLastTheoremThree_of_three_dvd_only_c`

English:
theorem fermatLastTheoremThree_of_three_dvd_only_c
  proof: by
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF => ?_)
  by_cases h1 : 3 ∣ a * b * c
  swap
  · exact fermatLastTheoremThree_case_1 h1 hF
  rw [prime_three.dvd_mul]; rw [prime_three.dvd_mul] at h1
  rw [← sub_eq_zero]

中文:
定理 fermatLastTheoremThree_of_three_dvd_only_c
  证明: by
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF => ?_)
  by_cases h1 : 3 ∣ a * b * c
  swap
  · exact fermatLastTheoremThree_case_1 h1 hF
  rw [prime_three.dvd_mul]; rw [prime_three.dvd_mul] at h1
  rw [← sub_eq_zero]

Depends on / 依赖: dvd_mul, fermatLastTheoremFor_iff_int, fermatLastTheoremThree_case_1, fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2, fermatLastTheoremWith_of_fermatLastTheoremWith_coprime, gcd_, gcd_insert, neg_pow, prime_three, prime_three.dvd_mul, sub_eq_add_neg, sub_eq_zero
-/
theorem fermatLastTheoremThree_of_three_dvd_only_c
    (H : forall a b c : Int, c != 0 -> ¬ 3 ∣ a -> ¬ 3 ∣ b -> 3 ∣ c -> IsCoprime a b -> a ^ 3 + b ^ 3 != c ^ 3) :
    FermatLastTheoremFor 3 := by
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF => ?_)
  by_cases h1 : 3 ∣ a * b * c
  swap
  · exact fermatLastTheoremThree_case_1 h1 hF
  rw [prime_three.dvd_mul]; rw [prime_three.dvd_mul] at h1
  rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [← (show Odd 3 by decide).neg_pow] at hF
  rcases h1 with (h3a | h3b) | h3c
  · refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 ha h3a ?_ H hF
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm (a ^ 3)] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 hb h3b ?_ H hF
    simp only [← Hgcd, insert_comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm _ ((-c) ^ 3), ← add_assoc] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 (neg_ne_zero.2 hc) (by simp [h3c])
      ?_ H hF
    rw [Finset.insert_comm (-c)]; rw [Finset.pair_comm (-c) b]
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]

section eisenstein

open NumberField IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "fun" => hζ.toInteger - 1

/--
Definition of `FermatLastTheoremForThreeGen` / `FermatLastTheoremForThreeGen` 的定义

English:
definition FermatLastTheoremForThreeGen
  signature: : Prop
  body: forall a b c : 𝓞 K, forall u : (𝓞 K)ˣ, c != 0 -> ¬ fun ∣ a -> ¬ fun ∣ b -> fun ∣ c -> IsCoprime a b ->
    a ^ 3 + b ^ 3 != u * c ^ 3

中文:
定义 FermatLastTheoremForThreeGen
  签名: : 命题
  定义体: forall a b c : 𝓞 K, forall u : (𝓞 K)ˣ, c != 0 -> ¬ fun ∣ a -> ¬ fun ∣ b -> fun ∣ c -> IsCoprime a b ->
    a ^ 3 + b ^ 3 != u * c ^ 3

Depends on / 依赖: IsCoprime
-/
def FermatLastTheoremForThreeGen : Prop :=
  forall a b c : 𝓞 K, forall u : (𝓞 K)ˣ, c != 0 -> ¬ fun ∣ a -> ¬ fun ∣ b -> fun ∣ c -> IsCoprime a b ->
    a ^ 3 + b ^ 3 != u * c ^ 3

/--
lemma `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` / 引理 `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen`

English:
lemma FermatLastTheoremForThree_of_FermatLastTheoremThreeGen
  proof: by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h => ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd => ha ?_) (fun hdvd => hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.nor

中文:
引理 FermatLastTheoremForThree_of_FermatLastTheoremThreeGen
  证明: by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h => ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd => ha ?_) (fun hdvd => hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.nor

Depends on / 依赖: Ideal.norm_dvd_iff, fermatLastTheoremThree_of_three_dvd_only_c, hcoprime, norm_dvd_iff, norm_toInteger_sub_one_of_prime_ne_two, prime_norm_toInteger_sub_one_of_prime_ne_two
-/
lemma FermatLastTheoremForThree_of_FermatLastTheoremThreeGen
    [NumberField K] [IsCyclotomicExtension {3} Rat K] :
    FermatLastTheoremForThreeGen hζ -> FermatLastTheoremFor 3 := by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h => ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd => ha ?_) (fun hdvd => hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · exact dvd_trans hζ.toInteger_sub_one_dvd_prime' ⟨x, by simp [hx]⟩
  · exact IsCoprime.intCast hcoprime
  · simpa using mod_cast h

namespace FermatLastTheoremForThreeGen

/--
Definition of `Solution'` / `Solution'` 的定义

English:
structure Solution'
  parameters: where
  axioms and operations (10):
    - a : 𝓞 K
    - b : 𝓞 K
    - c : 𝓞 K
    - u : (𝓞 K)ˣ
    - ha : ¬ fun ∣ a
    - hb : ¬ fun ∣ b
    - hc : c != 0
    - coprime : IsCoprime a b
    - hcdvd : fun ∣ c
    - H : a ^ 3 + b ^ 3 = u * c ^ 3

中文:
结构 Solution'
  参数: where
  公理与运算 (10 个):
    - a : 𝓞 K
    - b : 𝓞 K
    - c : 𝓞 K
    - u : (𝓞 K)ˣ
    - ha : ¬ fun ∣ a
    - hb : ¬ fun ∣ b
    - hc : c != 0
    - coprime : IsCoprime a b
    - hcdvd : fun ∣ c
    - H : a ^ 3 + b ^ 3 = u * c ^ 3
-/
structure Solution' where
  a : 𝓞 K
  b : 𝓞 K
  c : 𝓞 K
  u : (𝓞 K)ˣ
  ha : ¬ fun ∣ a
  hb : ¬ fun ∣ b
  hc : c != 0
  coprime : IsCoprime a b
  hcdvd : fun ∣ c
  H : a ^ 3 + b ^ 3 = u * c ^ 3
attribute [nolint docBlame] Solution'.a
attribute [nolint docBlame] Solution'.b
attribute [nolint docBlame] Solution'.c
attribute [nolint docBlame] Solution'.u

/--
Definition of `Solution` / `Solution` 的定义

English:
structure Solution
  parameters: extends Solution' hζ
  extends: Solution' hζ
  axioms and operations (1):
    - hab : fun ^ 2 ∣ a + b

中文:
结构 Solution
  参数: extends Solution' hζ
  继承: Solution' hζ
  公理与运算 (1 个):
    - hab : fun ^ 2 ∣ a + b
-/
structure Solution extends Solution' hζ where
  hab : fun ^ 2 ∣ a + b

variable {hζ}
variable (S : Solution hζ) (S' : Solution' hζ)

section IsCyclotomicExtension

variable [NumberField K] [IsCyclotomicExtension {3} Rat K]

/--
lemma `Solution'.multiplicity_lambda_c_finite` / 引理 `Solution'.multiplicity_lambda_c_finite`

English:
lemma Solution'.multiplicity_lambda_c_finite
  proof: .of_not_isUnit hζ.zeta_sub_one_prime'.not_isUnit S'.hc

中文:
引理 Solution'.multiplicity_lambda_c_finite
  证明: .of_not_isUnit hζ.zeta_sub_one_prime'.not_isUnit S'.hc

Depends on / 依赖: not_isUnit, of_not_isUnit, zeta_sub_one_prime
-/
lemma Solution'.multiplicity_lambda_c_finite :
    FiniteMultiplicity (hζ.toInteger - 1) S'.c :=
  .of_not_isUnit hζ.zeta_sub_one_prime'.not_isUnit S'.hc

/--
Definition of `Solution'.multiplicity` / `Solution'.multiplicity` 的定义

English:
definition Solution'.multiplicity
  body: _root_.multiplicity (hζ.toInteger - 1) S'.c

中文:
定义 Solution'.multiplicity
  定义体: _root_.multiplicity (hζ.toInteger - 1) S'.c
-/
noncomputable def Solution'.multiplicity :=
  _root_.multiplicity (hζ.toInteger - 1) S'.c

/--
Definition of `Solution.multiplicity` / `Solution.multiplicity` 的定义

English:
definition Solution.multiplicity
  body: S.toSolution'.multiplicity

中文:
定义 Solution.multiplicity
  定义体: S.toSolution'.multiplicity

Depends on / 依赖: S.toSolution, multiplicity, toSolution
-/
noncomputable def Solution.multiplicity := S.toSolution'.multiplicity

/--
Definition of `Solution.isMinimal` / `Solution.isMinimal` 的定义

English:
definition Solution.isMinimal
  signature: : Prop
  body: forall (S₁ : Solution hζ), S.multiplicity <= S₁.multiplicity

omit [NumberField K] [IsCyclotomicExtension {3} Rat K] in
include S in

中文:
定义 Solution.isMinimal
  签名: : 命题
  定义体: forall (S₁ : Solution hζ), S.multiplicity <= S₁.multiplicity

omit [NumberField K] [IsCyclotomicExtension {3} Rat K] in
include S in

Depends on / 依赖: S.multiplicity, Solution, multiplicity
-/
def Solution.isMinimal : Prop := forall (S₁ : Solution hζ), S.multiplicity <= S₁.multiplicity

omit [NumberField K] [IsCyclotomicExtension {3} Rat K] in
include S in
/--
lemma `Solution.exists_minimal` / 引理 `Solution.exists_minimal`

English:
lemma Solution.exists_minimal
  statement: exists (S₁ : Solution hζ), S₁.isMinimal
  proof: by
  classical
  let T := {n | exists (S' : Solution hζ), S'.multiplicity = n}
  rcases Nat.find_spec (⟨S.multiplicity, ⟨S, rfl⟩⟩ : T.Nonempty) with ⟨S₁, hS₁⟩
  exact ⟨S₁, fun S'' => hS₁ ▸ Nat.find_min' _ ⟨S'', rfl⟩⟩

中文:
引理 Solution.exists_minimal
  结论: 存在 (S₁ : Solution hζ), S₁.isMinimal
  证明: by
  classical
  let T := {n | exists (S' : Solution hζ), S'.multiplicity = n}
  rcases Nat.find_spec (⟨S.multiplicity, ⟨S, rfl⟩⟩ : T.Nonempty) with ⟨S₁, hS₁⟩
  exact ⟨S₁, fun S'' => hS₁ ▸ Nat.find_min' _ ⟨S'', rfl⟩⟩

Depends on / 依赖: Nat.find_min, Nat.find_spec, Nonempty, S.multiplicity, Solution, T.Nonempty, classical, find_min, find_spec, multiplicity
-/
lemma Solution.exists_minimal : exists (S₁ : Solution hζ), S₁.isMinimal := by
  classical
  let T := {n | exists (S' : Solution hζ), S'.multiplicity = n}
  rcases Nat.find_spec (⟨S.multiplicity, ⟨S, rfl⟩⟩ : T.Nonempty) with ⟨S₁, hS₁⟩
  exact ⟨S₁, fun S'' => hS₁ ▸ Nat.find_min' _ ⟨S'', rfl⟩⟩

/--
lemma `a_cube_b_cube_congr_one_or_neg_one` / 引理 `a_cube_b_cube_congr_one_or_neg_one`

English:
lemma a_cube_b_cube_congr_one_or_neg_one
  proof: by
  obtain ⟨z, hz⟩ := S'.hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.ha with
    ⟨x, hx⟩ | ⟨x, hx⟩ <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.hb with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · exfalso
    replace hζ : IsPrimitiveRoot ζ (3 

中文:
引理 a_cube_b_cube_congr_one_or_neg_one
  证明: by
  obtain ⟨z, hz⟩ := S'.hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.ha with
    ⟨x, hx⟩ | ⟨x, hx⟩ <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.hb with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · exfalso
    replace hζ : IsPrimitiveRoot ζ (3 

Depends on / 依赖: IsPrimitiveRoot, lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd, pow_one, replace, toInteger_sub_one_not_dvd_two
-/
lemma a_cube_b_cube_congr_one_or_neg_one :
    fun ^ 4 ∣ S'.a ^ 3 - 1 ∧ fun ^ 4 ∣ S'.b ^ 3 + 1 ∨ fun ^ 4 ∣ S'.a ^ 3 + 1 ∧ fun ^ 4 ∣ S'.b ^ 3 - 1 := by
  obtain ⟨z, hz⟩ := S'.hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.ha with
    ⟨x, hx⟩ | ⟨x, hx⟩ <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.hb with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · exfalso
    replace hζ : IsPrimitiveRoot ζ (3 ^ 1) := by rwa [pow_one]
    refine hζ.toInteger_sub_one_not_dvd_two (by decide) ⟨S'.u * fun ^ 2 * z ^ 3 - fun ^ 3 * (x + y), ?_⟩
    symm
    calc _ = S'.u * (fun * z) ^ 3 - fun ^ 4 * x - fun ^ 4 * y := by ring
    _ = (S'.a ^ 3 + S'.b ^ 3) - (S'.a ^ 3 - 1) - (S'.b ^ 3 - 1) := by rw [← hx, ← hy, ← hz, ← S'.H]
    _ = 2 := by ring
  · left
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · right
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exfalso
    replace hζ : IsPrimitiveRoot ζ (3 ^ 1) := by rwa [pow_one]
    refine hζ.toInteger_sub_one_not_dvd_two (by decide) ⟨fun ^ 3 * (x + y) - S'.u * fun ^ 2 * z ^ 3, ?_⟩
    symm
    calc _ = fun ^ 4 * x + fun ^ 4 * y - S'.u * (fun * z) ^ 3 := by ring
    _ = (S'.a ^ 3 + 1) + (S'.b ^ 3 + 1) - (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy, ← hz, ← S'.H]
    _ = 2 := by ring

/--
lemma `lambda_pow_four_dvd_c_cube` / 引理 `lambda_pow_four_dvd_c_cube`

English:
lemma lambda_pow_four_dvd_c_cube
  statement: fun ^ 4 ∣ S'.c ^ 3
  proof: by
  rcases a_cube_b_cube_congr_one_or_neg_one S' with
    ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ <;>
  · refine ⟨S'.u⁻¹ * (x + y), ?_⟩
    symm
    calc _ = S'.u⁻¹ * (fun ^ 4 * x + fun ^ 4 * y) := by ring
    _ = S'.u⁻¹ * (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy]; ring
    _ = S'.u⁻¹ * (S'.u * S

中文:
引理 lambda_pow_four_dvd_c_cube
  结论: fun ^ 4 ∣ S'.c ^ 3
  证明: by
  rcases a_cube_b_cube_congr_one_or_neg_one S' with
    ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ <;>
  · refine ⟨S'.u⁻¹ * (x + y), ?_⟩
    symm
    calc _ = S'.u⁻¹ * (fun ^ 4 * x + fun ^ 4 * y) := by ring
    _ = S'.u⁻¹ * (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy]; ring
    _ = S'.u⁻¹ * (S'.u * S

Depends on / 依赖: a_cube_b_cube_congr_one_or_neg_one
-/
lemma lambda_pow_four_dvd_c_cube : fun ^ 4 ∣ S'.c ^ 3 := by
  rcases a_cube_b_cube_congr_one_or_neg_one S' with
    ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ <;>
  · refine ⟨S'.u⁻¹ * (x + y), ?_⟩
    symm
    calc _ = S'.u⁻¹ * (fun ^ 4 * x + fun ^ 4 * y) := by ring
    _ = S'.u⁻¹ * (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy]; ring
    _ = S'.u⁻¹ * (S'.u * S'.c ^ 3) := by rw [S'.H]
    _ = S'.c ^ 3 := by simp

/--
lemma `lambda_sq_dvd_c` / 引理 `lambda_sq_dvd_c`

English:
lemma lambda_sq_dvd_c
  statement: fun ^ 2 ∣ S'.c
  proof: by
  have hm := S'.multiplicity_lambda_c_finite
  have := lambda_pow_four_dvd_c_cube S'
  rw [pow_dvd_iff_le_emultiplicity]; rw [emultiplicity_pow hζ.zeta_sub_one_prime']; rw [hm.emultiplicity_eq_multiplicity] at this
  norm_cast at this
  exact (FiniteMultiplicity.pow_dvd_iff_le_multiplicity hm).mp

中文:
引理 lambda_sq_dvd_c
  结论: fun ^ 2 ∣ S'.c
  证明: by
  have hm := S'.multiplicity_lambda_c_finite
  have := lambda_pow_four_dvd_c_cube S'
  rw [pow_dvd_iff_le_emultiplicity]; rw [emultiplicity_pow hζ.zeta_sub_one_prime']; rw [hm.emultiplicity_eq_multiplicity] at this
  norm_cast at this
  exact (FiniteMultiplicity.pow_dvd_iff_le_multiplicity hm).mp

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.pow_dvd_iff_le_multiplicity, emultiplicity_eq_multiplicity, emultiplicity_pow, hm.emultiplicity_eq_multiplicity, lambda_pow_four_dvd_c_cube, multiplicity_lambda_c_finite, pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_multiplicity, zeta_sub_one_prime
-/
lemma lambda_sq_dvd_c : fun ^ 2 ∣ S'.c := by
  have hm := S'.multiplicity_lambda_c_finite
  have := lambda_pow_four_dvd_c_cube S'
  rw [pow_dvd_iff_le_emultiplicity]; rw [emultiplicity_pow hζ.zeta_sub_one_prime']; rw [hm.emultiplicity_eq_multiplicity] at this
  norm_cast at this
  exact (FiniteMultiplicity.pow_dvd_iff_le_multiplicity hm).mpr (by lia)

/--
lemma `Solution'.two_le_multiplicity` / 引理 `Solution'.two_le_multiplicity`

English:
lemma Solution'.two_le_multiplicity
  statement: 2 <= S'.multiplicity
  proof: by
  simpa [Solution'.multiplicity] using
    S'.multiplicity_lambda_c_finite.le_multiplicity_of_pow_dvd (lambda_sq_dvd_c S')

中文:
引理 Solution'.two_le_multiplicity
  结论: 2 <= S'.multiplicity
  证明: by
  simpa [Solution'.multiplicity] using
    S'.multiplicity_lambda_c_finite.le_multiplicity_of_pow_dvd (lambda_sq_dvd_c S')
-/
lemma Solution'.two_le_multiplicity : 2 <= S'.multiplicity := by
  simpa [Solution'.multiplicity] using
    S'.multiplicity_lambda_c_finite.le_multiplicity_of_pow_dvd (lambda_sq_dvd_c S')

/--
lemma `Solution.two_le_multiplicity` / 引理 `Solution.two_le_multiplicity`

English:
lemma Solution.two_le_multiplicity
  statement: 2 <= S.multiplicity
  proof: S.toSolution'.two_le_multiplicity

中文:
引理 Solution.two_le_multiplicity
  结论: 2 <= S.multiplicity
  证明: S.toSolution'.two_le_multiplicity

Depends on / 依赖: S.toSolution, toSolution, two_le_multiplicity
-/
lemma Solution.two_le_multiplicity : 2 <= S.multiplicity :=
  S.toSolution'.two_le_multiplicity

end IsCyclotomicExtension

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
/--
lemma `a_cube_add_b_cube_eq_mul` / 引理 `a_cube_add_b_cube_eq_mul`

English:
lemma a_cube_add_b_cube_eq_mul
  proof: by
  symm
  calc _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+η^3)+η^3*S'.b^3 := by ring
  _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+1)+S'.b^3 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = S'.a ^ 3 + S'.b ^ 3 := by rw [eta_sq]; ring

中文:
引理 a_cube_add_b_cube_eq_mul
  证明: by
  symm
  calc _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+η^3)+η^3*S'.b^3 := by ring
  _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+1)+S'.b^3 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = S'.a ^ 3 + S'.b ^ 3 := by rw [eta_sq]; ring

Depends on / 依赖: eta_sq, toInteger_cube_eq_one
-/
lemma a_cube_add_b_cube_eq_mul :
    S'.a ^ 3 + S'.b ^ 3 = (S'.a + S'.b) * (S'.a + η * S'.b) * (S'.a + η ^ 2 * S'.b) := by
  symm
  calc _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+η^3)+η^3*S'.b^3 := by ring
  _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+1)+S'.b^3 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = S'.a ^ 3 + S'.b ^ 3 := by rw [eta_sq]; ring

section IsCyclotomicExtension
variable [NumberField K] [IsCyclotomicExtension {3} Rat K]

/--
lemma `lambda_sq_dvd_or_dvd_or_dvd` / 引理 `lambda_sq_dvd_or_dvd_or_dvd`

English:
lemma lambda_sq_dvd_or_dvd_or_dvd
  proof: by
  by_contra! ⟨h1, h2, h3⟩
  rw [← emultiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + S'.b) :=
    finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht => by simp [ht] at h1)
  have h2' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + η * S'.b) := 

中文:
引理 lambda_sq_dvd_or_dvd_or_dvd
  证明: by
  by_contra! ⟨h1, h2, h3⟩
  rw [← emultiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + S'.b) :=
    finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht => by simp [ht] at h1)
  have h2' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + η * S'.b) := 

Depends on / 依赖: FiniteMultiplicity, coe_eta, emultiplicity_lt_iff_not_dvd, finiteMultiplicity_iff, finiteMultiplicity_iff_emultiplicity_ne_top, toInteger
-/
lemma lambda_sq_dvd_or_dvd_or_dvd :
    fun ^ 2 ∣ S'.a + S'.b ∨ fun ^ 2 ∣ S'.a + η * S'.b ∨ fun ^ 2 ∣ S'.a + η ^ 2 * S'.b := by
  by_contra! ⟨h1, h2, h3⟩
  rw [← emultiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + S'.b) :=
    finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht => by simp [ht] at h1)
  have h2' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + η * S'.b) := by
    refine finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht => ?_)
    rw [coe_eta] at ht
    simp [ht] at h2
  have h3' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + η ^ 2 * S'.b) := by
    refine finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht => ?_)
    rw [coe_eta] at ht
    simp [ht] at h3
  rw [h1'.emultiplicity_eq_multiplicity]; rw [Nat.cast_lt] at h1
  rw [h2'.emultiplicity_eq_multiplicity]; rw [Nat.cast_lt] at h2
  rw [h3'.emultiplicity_eq_multiplicity]; rw [Nat.cast_lt] at h3
  have := (pow_dvd_pow_of_dvd (lambda_sq_dvd_c S') 3).mul_left S'.u
  rw [← pow_mul]; rw [← S'.H]; rw [a_cube_add_b_cube_eq_mul]; rw [pow_dvd_iff_le_emultiplicity]; rw [emultiplicity_mul hζ.zeta_sub_one_prime']; rw [emultiplicity_mul hζ.zeta_sub_one_prime']; rw [h1'.emultiplicity_eq_multiplicity]; rw [h2'.emultiplicity_eq_multiplicity]; rw [h3'.emultiplicity_eq_multiplicity]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [Nat.cast_le] at this
  lia

open Units in
/--
lemma `ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd` / 引理 `ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd`

English:
lemma ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd
  proof: by
  rcases lambda_sq_dvd_or_dvd_or_dvd S' with h | h | h
  · exact ⟨S'.a, S'.b, S'.H, S'.coprime, S'.ha, S'.hb, h⟩
  · refine ⟨S'.a, η * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ => S'.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · simp [mul_pow, hζ.toInteger_cube_eq_one, one_mul, S'.H]
    · refine (isCoprime_mul_unit_left_

中文:
引理 ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd
  证明: by
  rcases lambda_sq_dvd_or_dvd_or_dvd S' with h | h | h
  · exact ⟨S'.a, S'.b, S'.H, S'.coprime, S'.ha, S'.hb, h⟩
  · refine ⟨S'.a, η * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ => S'.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · simp [mul_pow, hζ.toInteger_cube_eq_one, one_mul, S'.H]
    · refine (isCoprime_mul_unit_left_

Depends on / 依赖: Units.isUnit, coe_eta, coprime, isCoprime_mul_unit_left_right, isUnit, lambda_sq_dvd_or_dvd_or_dvd, mul_assoc, mul_comm, mul_one, mul_pow, one_mul, pow_succ, toInteger_cube_eq_one
-/
lemma ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd :
    exists (a' b' : 𝓞 K), a' ^ 3 + b' ^ 3 = S'.u * S'.c ^ 3 ∧ IsCoprime a' b' ∧ ¬ fun ∣ a' ∧
      ¬ fun ∣ b' ∧ fun ^ 2 ∣ a' + b' := by
  rcases lambda_sq_dvd_or_dvd_or_dvd S' with h | h | h
  · exact ⟨S'.a, S'.b, S'.H, S'.coprime, S'.ha, S'.hb, h⟩
  · refine ⟨S'.a, η * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ => S'.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · simp [mul_pow, hζ.toInteger_cube_eq_one, one_mul, S'.H]
    · refine (isCoprime_mul_unit_left_right (Units.isUnit η) _ _).2 S'.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S'.b, mul_assoc, ← pow_succ', coe_eta,
        hζ.toInteger_cube_eq_one, mul_one]
  · refine ⟨S'.a, η ^ 2 * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ => S'.hb ⟨η * x, ?_⟩, h⟩
    · rw [mul_pow, ← pow_mul, mul_comm 2, pow_mul, coe_eta, hζ.toInteger_cube_eq_one, one_pow,
        one_mul, S'.H]
    · exact (isCoprime_mul_unit_left_right ((Units.isUnit η).pow _) _ _).2 S'.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S'.b, mul_assoc, ← pow_succ, coe_eta,
        hζ.toInteger_cube_eq_one, mul_one]

/--
lemma `exists_Solution_of_Solution'` / 引理 `exists_Solution_of_Solution'`

English:
lemma exists_Solution_of_Solution'
  statement: exists (S₁ : Solution hζ), S₁.multiplicity = S'.multiplicity
  proof: by
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd S'
  exact ⟨
  { a := a
    b := b
    c := S'.c
    u := S'.u
    ha := ha
    hb := hb
    hc := S'.hc
    coprime := coprime
    hcdvd := S'.hcdvd
    H := H
    hab := hab }, rfl⟩

中文:
引理 exists_Solution_of_Solution'
  结论: 存在 (S₁ : Solution hζ), S₁.multiplicity = S'.multiplicity
  证明: by
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd S'
  exact ⟨
  { a := a
    b := b
    c := S'.c
    u := S'.u
    ha := ha
    hb := hb
    hc := S'.hc
    coprime := coprime
    hcdvd := S'.hcdvd
    H := H
    hab := hab }, rfl⟩

Depends on / 依赖: coprime, ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd
-/
lemma exists_Solution_of_Solution' : exists (S₁ : Solution hζ), S₁.multiplicity = S'.multiplicity := by
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd S'
  exact ⟨
  { a := a
    b := b
    c := S'.c
    u := S'.u
    ha := ha
    hb := hb
    hc := S'.hc
    coprime := coprime
    hcdvd := S'.hcdvd
    H := H
    hab := hab }, rfl⟩

end IsCyclotomicExtension

namespace Solution

/--
lemma `a_add_eta_mul_b` / 引理 `a_add_eta_mul_b`

English:
lemma a_add_eta_mul_b
  statement: S.a + η * S.b = (S.a + S.b) + fun * S.b
  proof: by rw [coe_eta]; ring

中文:
引理 a_add_eta_mul_b
  结论: S.a + η * S.b = (S.a + S.b) + fun * S.b
  证明: by rw [coe_eta]; ring

Depends on / 依赖: coe_eta
-/
lemma a_add_eta_mul_b : S.a + η * S.b = (S.a + S.b) + fun * S.b := by rw [coe_eta]; ring

/--
lemma `lambda_dvd_a_add_eta_mul_b` / 引理 `lambda_dvd_a_add_eta_mul_b`

English:
lemma lambda_dvd_a_add_eta_mul_b
  statement: fun ∣ (S.a + η * S.b)
  proof: a_add_eta_mul_b S ▸ dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨S.b, by rw [mul_comm]⟩

中文:
引理 lambda_dvd_a_add_eta_mul_b
  结论: fun ∣ (S.a + η * S.b)
  证明: a_add_eta_mul_b S ▸ dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨S.b, by rw [mul_comm]⟩

Depends on / 依赖: S.hab, a_add_eta_mul_b, dvd_add, dvd_pow_self, dvd_trans, mul_comm
-/
lemma lambda_dvd_a_add_eta_mul_b : fun ∣ (S.a + η * S.b) :=
  a_add_eta_mul_b S ▸ dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨S.b, by rw [mul_comm]⟩

/--
lemma `lambda_dvd_a_add_eta_sq_mul_b` / 引理 `lambda_dvd_a_add_eta_sq_mul_b`

English:
lemma lambda_dvd_a_add_eta_sq_mul_b
  statement: fun ∣ (S.a + η ^ 2 * S.b)
  proof: by
  rw [show S.a + η ^ 2 * S.b = (S.a + S.b) + fun ^ 2 * S.b + 2 * fun * S.b by rw [coe_eta]; ring]
  exact dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨fun * S.b, by ring⟩)
    ⟨2 * S.b, by ring⟩

中文:
引理 lambda_dvd_a_add_eta_sq_mul_b
  结论: fun ∣ (S.a + η ^ 2 * S.b)
  证明: by
  rw [show S.a + η ^ 2 * S.b = (S.a + S.b) + fun ^ 2 * S.b + 2 * fun * S.b by rw [coe_eta]; ring]
  exact dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨fun * S.b, by ring⟩)
    ⟨2 * S.b, by ring⟩

Depends on / 依赖: S.hab, coe_eta, dvd_add, dvd_pow_self, dvd_trans
-/
lemma lambda_dvd_a_add_eta_sq_mul_b : fun ∣ (S.a + η ^ 2 * S.b) := by
  rw [show S.a + η ^ 2 * S.b = (S.a + S.b) + fun ^ 2 * S.b + 2 * fun * S.b by rw [coe_eta]; ring]
  exact dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨fun * S.b, by ring⟩)
    ⟨2 * S.b, by ring⟩

section IsCyclotomicExtension

variable [NumberField K] [IsCyclotomicExtension {3} Rat K]

/--
lemma `lambda_sq_not_dvd_a_add_eta_mul_b` / 引理 `lambda_sq_not_dvd_a_add_eta_mul_b`

English:
lemma lambda_sq_not_dvd_a_add_eta_mul_b
  statement: ¬ fun ^ 2 ∣ (S.a + η * S.b)
  proof: by
  simp_rw [a_add_eta_mul_b, dvd_add_right S.hab, pow_two, mul_dvd_mul_iff_left
    hζ.zeta_sub_one_prime'.ne_zero, S.hb, not_false_eq_true]

中文:
引理 lambda_sq_not_dvd_a_add_eta_mul_b
  结论: ¬ fun ^ 2 ∣ (S.a + η * S.b)
  证明: by
  simp_rw [a_add_eta_mul_b, dvd_add_right S.hab, pow_two, mul_dvd_mul_iff_left
    hζ.zeta_sub_one_prime'.ne_zero, S.hb, not_false_eq_true]

Depends on / 依赖: S.hab, S.hb, a_add_eta_mul_b, dvd_add_right, mul_dvd_mul_iff_left, ne_zero, not_false_eq_true, pow_two, simp_rw, zeta_sub_one_prime
-/
lemma lambda_sq_not_dvd_a_add_eta_mul_b : ¬ fun ^ 2 ∣ (S.a + η * S.b) := by
  simp_rw [a_add_eta_mul_b, dvd_add_right S.hab, pow_two, mul_dvd_mul_iff_left
    hζ.zeta_sub_one_prime'.ne_zero, S.hb, not_false_eq_true]

/--
lemma `lambda_sq_not_dvd_a_add_eta_sq_mul_b` / 引理 `lambda_sq_not_dvd_a_add_eta_sq_mul_b`

English:
lemma lambda_sq_not_dvd_a_add_eta_sq_mul_b
  statement: ¬ fun ^ 2 ∣ (S.a + η ^ 2 * S.b)
  proof: by
  intro ⟨k, hk⟩
  rcases S.hab with ⟨k', hk'⟩
  refine S.hb ⟨(k - k') * (-η), ?_⟩
  rw [show S.a + η ^ 2 * S.b = S.a + S.b - S.b + η ^ 2 * S.b by ring]; rw [hk']; rw [show fun ^ 2 * k' - S.b + η ^ 2 * S.b = fun * (S.b * (η + 1) + fun * k') by rw [coe_eta]; ring,
    pow_two, mul_assoc] at hk
  si

中文:
引理 lambda_sq_not_dvd_a_add_eta_sq_mul_b
  结论: ¬ fun ^ 2 ∣ (S.a + η ^ 2 * S.b)
  证明: by
  intro ⟨k, hk⟩
  rcases S.hab with ⟨k', hk'⟩
  refine S.hb ⟨(k - k') * (-η), ?_⟩
  rw [show S.a + η ^ 2 * S.b = S.a + S.b - S.b + η ^ 2 * S.b by ring]; rw [hk']; rw [show fun ^ 2 * k' - S.b + η ^ 2 * S.b = fun * (S.b * (η + 1) + fun * k') by rw [coe_eta]; ring,
    pow_two, mul_assoc] at hk
  si

Depends on / 依赖: S.hab, S.hb, apply_fun, coe_eta, eta_sq, mul_assoc, mul_eq_mul_left_iff, ne_zero, or_false, pow_two, zeta_sub_one_prime
-/
lemma lambda_sq_not_dvd_a_add_eta_sq_mul_b : ¬ fun ^ 2 ∣ (S.a + η ^ 2 * S.b) := by
  intro ⟨k, hk⟩
  rcases S.hab with ⟨k', hk'⟩
  refine S.hb ⟨(k - k') * (-η), ?_⟩
  rw [show S.a + η ^ 2 * S.b = S.a + S.b - S.b + η ^ 2 * S.b by ring]; rw [hk']; rw [show fun ^ 2 * k' - S.b + η ^ 2 * S.b = fun * (S.b * (η + 1) + fun * k') by rw [coe_eta]; ring,
    pow_two, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, hζ.zeta_sub_one_prime'.ne_zero, or_false] at hk
  apply_fun (· * -↑η) at hk
  rw [show (S.b * (η + 1) + fun * k') * -η = (-S.b) * (η ^ 2 + η + 1 - 1) - η * fun * k' by ring]; rw [eta_sq]; rw [show -S.b * (-↑η - 1 + ↑η + 1 - 1) = S.b by ring]; rw [sub_eq_iff_eq_add] at hk
  rw [hk]
  ring

attribute [local instance] IsCyclotomicExtension.Rat.three_pid
attribute [local instance] UniqueFactorizationMonoid.toGCDMonoid

/--
lemma `associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b` / 引理 `associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b`

English:
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b
  statement: {p : 𝓞 K} (hp : Prime p)
  proof: by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a]; rw [← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηb
  rwa [one_mul, one_mul, coe_eta, IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.c

中文:
引理 associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b
  结论: {p : 𝓞 K} (hp : Prime p)
  证明: by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a]; rw [← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηb
  rwa [one_mul, one_mul, coe_eta, IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.c

Depends on / 依赖: IsUnit, IsUnit.dvd_mul_right, S.coprime, associated_of_dvd, coe_eta, coprime, dvd_mul_right, dvd_mul_sub_mul_mul_gcd_of_dvd, gcd_isUnit_iff, hp.associated_of_dvd, one_mul, p_lam, zeta_sub_one_prime
-/
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpab : p ∣ S.a + S.b) (hpaηb : p ∣ S.a + η * S.b) : Associated p fun := by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a]; rw [← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηb
  rwa [one_mul, one_mul, coe_eta, IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime] at this

/--
lemma `associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b` / 引理 `associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b`

English:
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b
  statement: {p : 𝓞 K} (hp : Prime p)
  proof: by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a]; rw [← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηsqb
  rw [one_mul]; rw [mul_one]; rw [IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2

中文:
引理 associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b
  结论: {p : 𝓞 K} (hp : Prime p)
  证明: by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a]; rw [← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηsqb
  rw [one_mul]; rw [mul_one]; rw [IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2

Depends on / 依赖: IsUnit, IsUnit.dvd_mul_right, S.coprime, associated_of_dvd, coe_eta, convert, coprime, dvd_mul_of_dvd_left, dvd_mul_right, dvd_mul_sub_mul_mul_gcd_of_dvd, dvd_neg, eta_sq, gcd_isUnit_iff, hp.associated_of_dvd, mul_one, neg_mul, neg_sub, one_mul, p_lam, pow_two
-/
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpab : p ∣ (S.a + S.b)) (hpaηsqb : p ∣ (S.a + η ^ 2 * S.b)) : Associated p fun := by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a]; rw [← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηsqb
  rw [one_mul]; rw [mul_one]; rw [IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime]; rw [← dvd_neg] at this
  convert! dvd_mul_of_dvd_left this η using 1
  rw [eta_sq]; rw [neg_sub]; rw [sub_mul]; rw [sub_mul]; rw [neg_mul]; rw [← pow_two]; rw [eta_sq]; rw [coe_eta]
  ring

/--
lemma `associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b` / 引理 `associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b`

English:
lemma associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b
  statement: {p : 𝓞 K} (hp : Prime p)
  proof: by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a] at hpaηb
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpaηb hpaηsqb
  rw [one_mul]; rw [mul_one]; rw [IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime] at thi

中文:
引理 associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b
  结论: {p : 𝓞 K} (hp : Prime p)
  证明: by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a] at hpaηb
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpaηb hpaηsqb
  rw [one_mul]; rw [mul_one]; rw [IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime] at thi

Depends on / 依赖: IsUnit, IsUnit.dvd_mul_right, S.coprime, associated_of_dvd, convert, coprime, dvd_mul_of_dvd_left, dvd_mul_right, dvd_mul_sub_mul_mul_gcd_of_dvd, eta_sq, gcd_isUnit_iff, hp.associated_of_dvd, mul_assoc, mul_one, one_mul, p_lam, pow_two, zeta_sub_one_prime
-/
lemma associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpaηb : p ∣ S.a + η * S.b) (hpaηsqb : p ∣ S.a + η ^ 2 * S.b) : Associated p fun := by
  suffices p_lam : p ∣ fun from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a] at hpaηb
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpaηb hpaηsqb
  rw [one_mul]; rw [mul_one]; rw [IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime] at this
  convert! (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left this η) η) using 1
  symm
  calc _ = (-η.1 - 1 - η) * (-η - 1) := by rw [eta_sq, mul_assoc, ← pow_two, eta_sq]
  _ = 2 * η.1 ^ 2 + 3 * η + 1 := by ring
  _ = fun := by rw [eta_sq, coe_eta]; ring

end IsCyclotomicExtension

/--
Definition of `y` / `y` 的定义

English:
definition y
  body: (lambda_dvd_a_add_eta_mul_b S).choose

中文:
定义 y
  定义体: (lambda_dvd_a_add_eta_mul_b S).choose

Depends on / 依赖: lambda_dvd_a_add_eta_mul_b
-/
noncomputable def y := (lambda_dvd_a_add_eta_mul_b S).choose
/--
lemma `y_spec` / 引理 `y_spec`

English:
lemma y_spec
  statement: S.a + η * S.b = fun * S.y
  proof: (lambda_dvd_a_add_eta_mul_b S).choose_spec

中文:
引理 y_spec
  结论: S.a + η * S.b = fun * S.y
  证明: (lambda_dvd_a_add_eta_mul_b S).choose_spec

Depends on / 依赖: choose_spec, lambda_dvd_a_add_eta_mul_b
-/
lemma y_spec : S.a + η * S.b = fun * S.y :=
  (lambda_dvd_a_add_eta_mul_b S).choose_spec

/--
Definition of `z` / `z` 的定义

English:
definition z
  body: (lambda_dvd_a_add_eta_sq_mul_b S).choose

中文:
定义 z
  定义体: (lambda_dvd_a_add_eta_sq_mul_b S).choose

Depends on / 依赖: lambda_dvd_a_add_eta_sq_mul_b
-/
noncomputable def z := (lambda_dvd_a_add_eta_sq_mul_b S).choose
/--
lemma `z_spec` / 引理 `z_spec`

English:
lemma z_spec
  statement: S.a + η ^ 2 * S.b = fun * S.z
  proof: (lambda_dvd_a_add_eta_sq_mul_b S).choose_spec

中文:
引理 z_spec
  结论: S.a + η ^ 2 * S.b = fun * S.z
  证明: (lambda_dvd_a_add_eta_sq_mul_b S).choose_spec

Depends on / 依赖: choose_spec, lambda_dvd_a_add_eta_sq_mul_b
-/
lemma z_spec : S.a + η ^ 2 * S.b = fun * S.z :=
  (lambda_dvd_a_add_eta_sq_mul_b S).choose_spec

variable [NumberField K] [IsCyclotomicExtension {3} Rat K]

/--
lemma `lambda_not_dvd_y` / 引理 `lambda_not_dvd_y`

English:
lemma lambda_not_dvd_y
  statement: ¬ fun ∣ S.y
  proof: fun h => by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta]; rw [← y_spec]; rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_mul_b _ h

中文:
引理 lambda_not_dvd_y
  结论: ¬ fun ∣ S.y
  证明: fun h => by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta]; rw [← y_spec]; rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_mul_b _ h

Depends on / 依赖: coe_eta, lambda_sq_not_dvd_a_add_eta_mul_b, mul_dvd_mul_left, pow_two, replace, y_spec
-/
lemma lambda_not_dvd_y : ¬ fun ∣ S.y := fun h => by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta]; rw [← y_spec]; rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_mul_b _ h

/--
lemma `lambda_not_dvd_z` / 引理 `lambda_not_dvd_z`

English:
lemma lambda_not_dvd_z
  statement: ¬ fun ∣ S.z
  proof: fun h => by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta]; rw [← z_spec]; rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_sq_mul_b _ h

中文:
引理 lambda_not_dvd_z
  结论: ¬ fun ∣ S.z
  证明: fun h => by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta]; rw [← z_spec]; rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_sq_mul_b _ h

Depends on / 依赖: coe_eta, lambda_sq_not_dvd_a_add_eta_sq_mul_b, mul_dvd_mul_left, pow_two, replace, z_spec
-/
lemma lambda_not_dvd_z : ¬ fun ∣ S.z := fun h => by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta]; rw [← z_spec]; rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_sq_mul_b _ h

/--
lemma `lambda_pow_dvd_a_add_b` / 引理 `lambda_pow_dvd_a_add_b`

English:
lemma lambda_pow_dvd_a_add_b
  statement: fun ^ (3 * S.multiplicity - 2) ∣ S.a + S.b
  proof: by
  have h : fun ^ S.multiplicity ∣ S.c := pow_multiplicity_dvd _ _
  replace h : (fun ^ multiplicity S) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  rw [← S.H]; rw [a_cube_add_b_cube_eq_mul]; rw [← pow_mul]; rw [mul_comm]; rw [y_spec]; rw [z_spec] at h
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_lef

中文:
引理 lambda_pow_dvd_a_add_b
  结论: fun ^ (3 * S.multiplicity - 2) ∣ S.a + S.b
  证明: by
  have h : fun ^ S.multiplicity ∣ S.c := pow_multiplicity_dvd _ _
  replace h : (fun ^ multiplicity S) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  rw [← S.H]; rw [a_cube_add_b_cube_eq_mul]; rw [← pow_mul]; rw [mul_comm]; rw [y_spec]; rw [z_spec] at h
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_lef

Depends on / 依赖: S.lambda_not_dvd_y, S.lambda_not_dvd_z, S.multiplicity, S.two_le_multiplicity, a_cube_add_b_cube_eq_mul, lambda_not_dvd_y, lambda_not_dvd_z, mul_comm, multiplicity, pow_dvd_of_dvd_mul_left, pow_mul, pow_multiplicity_dvd, pow_suc, replace, two_le_multiplicity, y_spec, z_spec, zeta_sub_one_prime
-/
lemma lambda_pow_dvd_a_add_b : fun ^ (3 * S.multiplicity - 2) ∣ S.a + S.b := by
  have h : fun ^ S.multiplicity ∣ S.c := pow_multiplicity_dvd _ _
  replace h : (fun ^ multiplicity S) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  rw [← S.H]; rw [a_cube_add_b_cube_eq_mul]; rw [← pow_mul]; rw [mul_comm]; rw [y_spec]; rw [z_spec] at h
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_z
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_y
  have := S.two_le_multiplicity
  rw [show 3 * multiplicity S = 3 * multiplicity S - 2 + 1 + 1 by lia]; rw [pow_succ]; rw [pow_succ]; rw [show (S.a + S.b) * (fun * y S) * (fun * z S) = (S.a + S.b) * y S * z S * fun * fun by ring] at h
  simp only [mul_dvd_mul_iff_right hζ.zeta_sub_one_prime'.ne_zero] at h
  rwa [show (S.a + S.b) * y S * z S = y S * (z S * (S.a + S.b)) by ring] at h

/--
Definition of `x` / `x` 的定义

English:
definition x
  body: (lambda_pow_dvd_a_add_b S).choose

中文:
定义 x
  定义体: (lambda_pow_dvd_a_add_b S).choose

Depends on / 依赖: lambda_pow_dvd_a_add_b
-/
noncomputable def x := (lambda_pow_dvd_a_add_b S).choose
/--
lemma `x_spec` / 引理 `x_spec`

English:
lemma x_spec
  statement: S.a + S.b = fun ^ (3 * S.multiplicity - 2) * S.x
  proof: (lambda_pow_dvd_a_add_b S).choose_spec

中文:
引理 x_spec
  结论: S.a + S.b = fun ^ (3 * S.multiplicity - 2) * S.x
  证明: (lambda_pow_dvd_a_add_b S).choose_spec

Depends on / 依赖: choose_spec, lambda_pow_dvd_a_add_b
-/
lemma x_spec : S.a + S.b = fun ^ (3 * S.multiplicity - 2) * S.x :=
  (lambda_pow_dvd_a_add_b S).choose_spec

/--
Definition of `w` / `w` 的定义

English:
definition w
  body: (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose

omit [NumberField K] [IsCyclotomicExtension {3} Rat K] in

中文:
定义 w
  定义体: (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose

omit [NumberField K] [IsCyclotomicExtension {3} Rat K] in

Depends on / 依赖: pow_multiplicity_dvd, toInteger
-/
noncomputable def w :=
  (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose

omit [NumberField K] [IsCyclotomicExtension {3} Rat K] in
/--
lemma `w_spec` / 引理 `w_spec`

English:
lemma w_spec
  statement: S.c = fun ^ S.multiplicity * S.w
  proof: (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose_spec

中文:
引理 w_spec
  结论: S.c = fun ^ S.multiplicity * S.w
  证明: (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose_spec

Depends on / 依赖: choose_spec, pow_multiplicity_dvd, toInteger
-/
lemma w_spec : S.c = fun ^ S.multiplicity * S.w :=
  (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose_spec

/--
lemma `lambda_not_dvd_w` / 引理 `lambda_not_dvd_w`

English:
lemma lambda_not_dvd_w
  statement: ¬ fun ∣ S.w
  proof: fun h => by
  refine S.toSolution'.multiplicity_lambda_c_finite.not_pow_dvd_of_multiplicity_lt
    (lt_add_one S.multiplicity) ?_
  rw [pow_succ']; rw [mul_comm]
  exact S.w_spec ▸ (mul_dvd_mul_left (fun ^ S.multiplicity) h)

中文:
引理 lambda_not_dvd_w
  结论: ¬ fun ∣ S.w
  证明: fun h => by
  refine S.toSolution'.multiplicity_lambda_c_finite.not_pow_dvd_of_multiplicity_lt
    (lt_add_one S.multiplicity) ?_
  rw [pow_succ']; rw [mul_comm]
  exact S.w_spec ▸ (mul_dvd_mul_left (fun ^ S.multiplicity) h)

Depends on / 依赖: S.multiplicity, S.toSolution, S.w_spec, lt_add_one, mul_comm, mul_dvd_mul_left, multiplicity, multiplicity_lambda_c_finite, multiplicity_lambda_c_finite.not_pow_dvd_of_multiplicity_lt, not_pow_dvd_of_multiplicity_lt, pow_succ, toSolution, w_spec
-/
lemma lambda_not_dvd_w : ¬ fun ∣ S.w := fun h => by
  refine S.toSolution'.multiplicity_lambda_c_finite.not_pow_dvd_of_multiplicity_lt
    (lt_add_one S.multiplicity) ?_
  rw [pow_succ']; rw [mul_comm]
  exact S.w_spec ▸ (mul_dvd_mul_left (fun ^ S.multiplicity) h)

/--
lemma `lambda_not_dvd_x` / 引理 `lambda_not_dvd_x`

English:
lemma lambda_not_dvd_x
  statement: ¬ fun ∣ S.x
  proof: fun h => by
  replace h := mul_dvd_mul_left (fun ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm]; rw [← x_spec] at h
  replace h :=
    mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  simp only [← a_cube_add_b_cube_eq_mul, S.H, w_spec, Units.isUnit, IsUnit.dv

中文:
引理 lambda_not_dvd_x
  结论: ¬ fun ∣ S.x
  证明: fun h => by
  replace h := mul_dvd_mul_left (fun ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm]; rw [← x_spec] at h
  replace h :=
    mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  simp only [← a_cube_add_b_cube_eq_mul, S.H, w_spec, Units.isUnit, IsUnit.dv

Depends on / 依赖: IsUnit, IsUnit.dvd_mul_left, S.lambda_dvd_a_add_eta_mul_b, S.lambda_dvd_a_add_eta_sq_mul_b, S.multiplicity, S.two_le_multiplicity, Units.isUnit, a_cube_add_b_cube_eq_mul, dvd_mul_left, isUnit, lambda_dvd_a_add_eta_mul_b, lambda_dvd_a_add_eta_sq_mul_b, mul_assoc, mul_comm, mul_dvd_mul, mul_dvd_mul_left, mul_pow, multiplicity, pow_succ, replace
-/
lemma lambda_not_dvd_x : ¬ fun ∣ S.x := fun h => by
  replace h := mul_dvd_mul_left (fun ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm]; rw [← x_spec] at h
  replace h :=
    mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  simp only [← a_cube_add_b_cube_eq_mul, S.H, w_spec, Units.isUnit, IsUnit.dvd_mul_left] at h
  rw [← pow_succ']; rw [mul_comm]; rw [← mul_assoc]; rw [← pow_succ'] at h
  have := S.two_le_multiplicity
  rw [show 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S by lia]; rw [mul_pow]; rw [← pow_mul]; rw [mul_comm _ 3]; rw [mul_dvd_mul_iff_left _] at h
· exact lambda_not_dvd_w _ hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h
  · simp [hζ.zeta_sub_one_prime'.ne_zero]

attribute [local instance] IsCyclotomicExtension.Rat.three_pid

/--
lemma `isCoprime_helper` / 引理 `isCoprime_helper`

English:
lemma isCoprime_helper
  statement: {r s t w : 𝓞 K} (hr : ¬ fun ∣ r) (hs : ¬ fun ∣ s)
  proof: by
  refine isCoprime_of_prime_dvd (not_and.2 (fun _ hz => hs (by simp [hz])))
    (fun p hp p_dvd_r p_dvd_s => hr ?_)
  rwa [← Associated.dvd_iff_dvd_left <| Hp hp (H₁ p_dvd_r) (H₂ p_dvd_s)]

中文:
引理 isCoprime_helper
  结论: {r s t w : 𝓞 K} (hr : ¬ fun ∣ r) (hs : ¬ fun ∣ s)
  证明: by
  refine isCoprime_of_prime_dvd (not_and.2 (fun _ hz => hs (by simp [hz])))
    (fun p hp p_dvd_r p_dvd_s => hr ?_)
  rwa [← Associated.dvd_iff_dvd_left <| Hp hp (H₁ p_dvd_r) (H₂ p_dvd_s)]

Depends on / 依赖: Associated, Associated.dvd_iff_dvd_left, dvd_iff_dvd_left, isCoprime_of_prime_dvd, not_and, p_dvd_r, p_dvd_s
-/
lemma isCoprime_helper {r s t w : 𝓞 K} (hr : ¬ fun ∣ r) (hs : ¬ fun ∣ s)
    (Hp : forall {p}, Prime p -> p ∣ t -> p ∣ w -> Associated p fun) (H₁ : forall {q}, q ∣ r -> q ∣ t)
    (H₂ : forall {q}, q ∣ s -> q ∣ w) : IsCoprime r s := by
  refine isCoprime_of_prime_dvd (not_and.2 (fun _ hz => hs (by simp [hz])))
    (fun p hp p_dvd_r p_dvd_s => hr ?_)
  rwa [← Associated.dvd_iff_dvd_left <| Hp hp (H₁ p_dvd_r) (H₂ p_dvd_s)]

/--
lemma `isCoprime_x_y` / 引理 `isCoprime_x_y`

English:
lemma isCoprime_x_y
  statement: IsCoprime S.x S.y
  proof: isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_y S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b S) (fun hq => x_spec S ▸ hq.mul_left _)
      (fun hq => y_spec S ▸ hq.mul_left _)

中文:
引理 isCoprime_x_y
  结论: IsCoprime S.x S.y
  证明: isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_y S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b S) (fun hq => x_spec S ▸ hq.mul_left _)
      (fun hq => y_spec S ▸ hq.mul_left _)

Depends on / 依赖: associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b, hq.mul_left, isCoprime_helper, lambda_not_dvd_x, lambda_not_dvd_y, mul_left, x_spec, y_spec
-/
lemma isCoprime_x_y : IsCoprime S.x S.y :=
  isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_y S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b S) (fun hq => x_spec S ▸ hq.mul_left _)
      (fun hq => y_spec S ▸ hq.mul_left _)

/--
lemma `isCoprime_x_z` / 引理 `isCoprime_x_z`

English:
lemma isCoprime_x_z
  statement: IsCoprime S.x S.z
  proof: isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b S) (fun hq => x_spec S ▸ hq.mul_left _)
      (fun hq => z_spec S ▸ hq.mul_left _)

中文:
引理 isCoprime_x_z
  结论: IsCoprime S.x S.z
  证明: isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b S) (fun hq => x_spec S ▸ hq.mul_left _)
      (fun hq => z_spec S ▸ hq.mul_left _)

Depends on / 依赖: associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b, hq.mul_left, isCoprime_helper, lambda_not_dvd_x, lambda_not_dvd_z, mul_left, x_spec, z_spec
-/
lemma isCoprime_x_z : IsCoprime S.x S.z :=
  isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b S) (fun hq => x_spec S ▸ hq.mul_left _)
      (fun hq => z_spec S ▸ hq.mul_left _)

/--
lemma `isCoprime_y_z` / 引理 `isCoprime_y_z`

English:
lemma isCoprime_y_z
  statement: IsCoprime S.y S.z
  proof: isCoprime_helper (lambda_not_dvd_y S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b S)
    (fun hq => y_spec S ▸ hq.mul_left _) (fun hq => z_spec S ▸ hq.mul_left _)

中文:
引理 isCoprime_y_z
  结论: IsCoprime S.y S.z
  证明: isCoprime_helper (lambda_not_dvd_y S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b S)
    (fun hq => y_spec S ▸ hq.mul_left _) (fun hq => z_spec S ▸ hq.mul_left _)

Depends on / 依赖: associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b, hq.mul_left, isCoprime_helper, lambda_not_dvd_y, lambda_not_dvd_z, mul_left, y_spec, z_spec
-/
lemma isCoprime_y_z : IsCoprime S.y S.z :=
  isCoprime_helper (lambda_not_dvd_y S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b S)
    (fun hq => y_spec S ▸ hq.mul_left _) (fun hq => z_spec S ▸ hq.mul_left _)

/--
lemma `x_mul_y_mul_z_eq_u_mul_w_cube` / 引理 `x_mul_y_mul_z_eq_u_mul_w_cube`

English:
lemma x_mul_y_mul_z_eq_u_mul_w_cube
  statement: S.x * S.y * S.z = S.u * S.w ^ 3
  proof: by
  suffices hh : fun ^ (3 * S.multiplicity - 2) * S.x * fun * S.y * fun * S.z =
      S.u * fun ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show fun ^ (3 * multiplicity S - 2) * x S * fun * y S * fun * z S =
      fun ^ (3 * multiplicity S - 2) * fun * fun * x S * y S * z S by ring] at hh
    have

中文:
引理 x_mul_y_mul_z_eq_u_mul_w_cube
  结论: S.x * S.y * S.z = S.u * S.w ^ 3
  证明: by
  suffices hh : fun ^ (3 * S.multiplicity - 2) * S.x * fun * S.y * fun * S.z =
      S.u * fun ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show fun ^ (3 * multiplicity S - 2) * x S * fun * y S * fun * z S =
      fun ^ (3 * multiplicity S - 2) * fun * fun * x S * y S * z S by ring] at hh
    have

Depends on / 依赖: S.multiplicity, S.two_le_multiplicity, mul_assoc, mul_comm, multiplicity, pow_succ, two_le_multiplicity
-/
lemma x_mul_y_mul_z_eq_u_mul_w_cube : S.x * S.y * S.z = S.u * S.w ^ 3 := by
  suffices hh : fun ^ (3 * S.multiplicity - 2) * S.x * fun * S.y * fun * S.z =
      S.u * fun ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show fun ^ (3 * multiplicity S - 2) * x S * fun * y S * fun * z S =
      fun ^ (3 * multiplicity S - 2) * fun * fun * x S * y S * z S by ring] at hh
    have := S.two_le_multiplicity
    rw [mul_comm _ (fun ^ (3 * multiplicity S))]; rw [← pow_succ]; rw [← pow_succ]; rw [show 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S by lia]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc] at hh
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.zeta_sub_one_prime'.ne_zero, ne_eq,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, false_and, or_false] at hh
    convert! hh using 1
    ring
  simp only [← x_spec, mul_assoc, ← y_spec, ← z_spec]
  rw [mul_comm 3]; rw [pow_mul]; rw [← mul_pow]; rw [← w_spec]; rw [← S.H]; rw [a_cube_add_b_cube_eq_mul]
  ring

/--
lemma `exists_cube_associated` / 引理 `exists_cube_associated`

English:
lemma exists_cube_associated
  proof: by
  have h₁ := S.isCoprime_x_z.mul_left S.isCoprime_y_z
  have h₂ : Associated (S.w ^ 3) (S.x * S.y * S.z) :=
    ⟨S.u, by rw [x_mul_y_mul_z_eq_u_mul_w_cube S, mul_comm]⟩
  obtain ⟨T, h₃⟩ := exists_associated_pow_of_associated_pow_mul h₁ h₂
  exact ⟨exists_associated_pow_of_associated_pow_mul S.isC

中文:
引理 exists_cube_associated
  证明: by
  have h₁ := S.isCoprime_x_z.mul_left S.isCoprime_y_z
  have h₂ : Associated (S.w ^ 3) (S.x * S.y * S.z) :=
    ⟨S.u, by rw [x_mul_y_mul_z_eq_u_mul_w_cube S, mul_comm]⟩
  obtain ⟨T, h₃⟩ := exists_associated_pow_of_associated_pow_mul h₁ h₂
  exact ⟨exists_associated_pow_of_associated_pow_mul S.isC

Depends on / 依赖: Associated, S.isCoprime_x_y, S.isCoprime_x_y.symm, S.isCoprime_x_z.mul_left, S.isCoprime_y_z, exists_associated_pow_of_associated_pow_mul, isCoprime_x_y, isCoprime_x_z, isCoprime_y_z, mul_comm, mul_left, x_mul_y_mul_z_eq_u_mul_w_cube
-/
lemma exists_cube_associated :
    (exists X, Associated (X ^ 3) S.x) ∧ (exists Y, Associated (Y ^ 3) S.y) ∧
      exists Z, Associated (Z ^ 3) S.z := by
  have h₁ := S.isCoprime_x_z.mul_left S.isCoprime_y_z
  have h₂ : Associated (S.w ^ 3) (S.x * S.y * S.z) :=
    ⟨S.u, by rw [x_mul_y_mul_z_eq_u_mul_w_cube S, mul_comm]⟩
  obtain ⟨T, h₃⟩ := exists_associated_pow_of_associated_pow_mul h₁ h₂
  exact ⟨exists_associated_pow_of_associated_pow_mul S.isCoprime_x_y h₃,
    exists_associated_pow_of_associated_pow_mul S.isCoprime_x_y.symm (mul_comm _ S.x ▸ h₃),
    exists_associated_pow_of_associated_pow_mul h₁.symm (mul_comm _ S.z ▸ h₂)⟩

/--
Definition of `X` / `X` 的定义

English:
definition X
  body: (exists_cube_associated S).1.choose

中文:
定义 X
  定义体: (exists_cube_associated S).1.choose

Depends on / 依赖: Membership, NonemptyInterval, exists_cube_associated
-/
noncomputable def X := (exists_cube_associated S).1.choose
/--
Definition of `u₁` / `u₁` 的定义

English:
definition u₁
  body: (exists_cube_associated S).1.choose_spec.choose

中文:
定义 u₁
  定义体: (exists_cube_associated S).1.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, exists_cube_associated
-/
noncomputable def u₁ := (exists_cube_associated S).1.choose_spec.choose
/--
lemma `X_u₁_spec` / 引理 `X_u₁_spec`

English:
lemma X_u₁_spec
  statement: S.X ^ 3 * S.u₁ = S.x
  proof: (exists_cube_associated S).1.choose_spec.choose_spec

中文:
引理 X_u₁_spec
  结论: S.X ^ 3 * S.u₁ = S.x
  证明: (exists_cube_associated S).1.choose_spec.choose_spec

Depends on / 依赖: choose_spec, choose_spec.choose_spec, exists_cube_associated
-/
lemma X_u₁_spec : S.X ^ 3 * S.u₁ = S.x :=
  (exists_cube_associated S).1.choose_spec.choose_spec

/--
Definition of `Y` / `Y` 的定义

English:
definition Y
  body: (exists_cube_associated S).2.1.choose

中文:
定义 Y
  定义体: (exists_cube_associated S).2.1.choose

Depends on / 依赖: exists_cube_associated
-/
noncomputable def Y := (exists_cube_associated S).2.1.choose
/--
Definition of `u₂` / `u₂` 的定义

English:
definition u₂
  body: (exists_cube_associated S).2.1.choose_spec.choose

中文:
定义 u₂
  定义体: (exists_cube_associated S).2.1.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, exists_cube_associated
-/
noncomputable def u₂ := (exists_cube_associated S).2.1.choose_spec.choose
/--
lemma `Y_u₂_spec` / 引理 `Y_u₂_spec`

English:
lemma Y_u₂_spec
  statement: S.Y ^ 3 * S.u₂ = S.y
  proof: (exists_cube_associated S).2.1.choose_spec.choose_spec

中文:
引理 Y_u₂_spec
  结论: S.Y ^ 3 * S.u₂ = S.y
  证明: (exists_cube_associated S).2.1.choose_spec.choose_spec

Depends on / 依赖: choose_spec, choose_spec.choose_spec, exists_cube_associated
-/
lemma Y_u₂_spec : S.Y ^ 3 * S.u₂ = S.y :=
  (exists_cube_associated S).2.1.choose_spec.choose_spec

/--
Definition of `Z` / `Z` 的定义

English:
definition Z
  body: (exists_cube_associated S).2.2.choose

中文:
定义 Z
  定义体: (exists_cube_associated S).2.2.choose

Depends on / 依赖: exists_cube_associated
-/
noncomputable def Z := (exists_cube_associated S).2.2.choose
/--
Definition of `u₃` / `u₃` 的定义

English:
definition u₃
  body: (exists_cube_associated S).2.2.choose_spec.choose

中文:
定义 u₃
  定义体: (exists_cube_associated S).2.2.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, exists_cube_associated
-/
noncomputable def u₃ := (exists_cube_associated S).2.2.choose_spec.choose
/--
lemma `Z_u₃_spec` / 引理 `Z_u₃_spec`

English:
lemma Z_u₃_spec
  statement: S.Z ^ 3 * S.u₃ = S.z
  proof: (exists_cube_associated S).2.2.choose_spec.choose_spec

中文:
引理 Z_u₃_spec
  结论: S.Z ^ 3 * S.u₃ = S.z
  证明: (exists_cube_associated S).2.2.choose_spec.choose_spec

Depends on / 依赖: choose_spec, choose_spec.choose_spec, exists_cube_associated
-/
lemma Z_u₃_spec : S.Z ^ 3 * S.u₃ = S.z :=
  (exists_cube_associated S).2.2.choose_spec.choose_spec

/--
lemma `X_ne_zero` / 引理 `X_ne_zero`

English:
lemma X_ne_zero
  statement: S.X != 0
  proof: fun h => lambda_not_dvd_x S by simp [← X_u₁_spec, h]

中文:
引理 X_ne_zero
  结论: S.X != 0
  证明: fun h => lambda_not_dvd_x S by simp [← X_u₁_spec, h]

Depends on / 依赖: lambda_not_dvd_x
-/
lemma X_ne_zero : S.X != 0 :=
fun h => lambda_not_dvd_x S by simp [← X_u₁_spec, h]

/--
lemma `lambda_not_dvd_X` / 引理 `lambda_not_dvd_X`

English:
lemma lambda_not_dvd_X
  statement: ¬ fun ∣ S.X
  proof: fun h => lambda_not_dvd_x S X_u₁_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

中文:
引理 lambda_not_dvd_X
  结论: ¬ fun ∣ S.X
  证明: fun h => lambda_not_dvd_x S X_u₁_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

Depends on / 依赖: dvd_mul_of_dvd_left, dvd_pow, lambda_not_dvd_x
-/
lemma lambda_not_dvd_X : ¬ fun ∣ S.X :=
fun h => lambda_not_dvd_x S X_u₁_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

/--
lemma `lambda_not_dvd_Y` / 引理 `lambda_not_dvd_Y`

English:
lemma lambda_not_dvd_Y
  statement: ¬ fun ∣ S.Y
  proof: fun h => lambda_not_dvd_y S Y_u₂_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

中文:
引理 lambda_not_dvd_Y
  结论: ¬ fun ∣ S.Y
  证明: fun h => lambda_not_dvd_y S Y_u₂_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

Depends on / 依赖: dvd_mul_of_dvd_left, dvd_pow, lambda_not_dvd_y
-/
lemma lambda_not_dvd_Y : ¬ fun ∣ S.Y :=
fun h => lambda_not_dvd_y S Y_u₂_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

/--
lemma `lambda_not_dvd_Z` / 引理 `lambda_not_dvd_Z`

English:
lemma lambda_not_dvd_Z
  statement: ¬ fun ∣ S.Z
  proof: fun h => lambda_not_dvd_z S Z_u₃_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

中文:
引理 lambda_not_dvd_Z
  结论: ¬ fun ∣ S.Z
  证明: fun h => lambda_not_dvd_z S Z_u₃_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

Depends on / 依赖: dvd_mul_of_dvd_left, dvd_pow, lambda_not_dvd_z
-/
lemma lambda_not_dvd_Z : ¬ fun ∣ S.Z :=
fun h => lambda_not_dvd_z S Z_u₃_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

/--
lemma `isCoprime_Y_Z` / 引理 `isCoprime_Y_Z`

English:
lemma isCoprime_Y_Z
  statement: IsCoprime S.Y S.Z
  proof: by
  rw [← IsCoprime.pow_iff (m := 3) (n := 3) (by decide) (by decide)]; rw [← isCoprime_mul_unit_right_left S.u₂.isUnit]; rw [← isCoprime_mul_unit_right_right S.u₃.isUnit]; rw [Y_u₂_spec]; rw [Z_u₃_spec]
  exact isCoprime_y_z S

中文:
引理 isCoprime_Y_Z
  结论: IsCoprime S.Y S.Z
  证明: by
  rw [← IsCoprime.pow_iff (m := 3) (n := 3) (by decide) (by decide)]; rw [← isCoprime_mul_unit_right_left S.u₂.isUnit]; rw [← isCoprime_mul_unit_right_right S.u₃.isUnit]; rw [Y_u₂_spec]; rw [Z_u₃_spec]
  exact isCoprime_y_z S

Depends on / 依赖: IsCoprime, IsCoprime.pow_iff, isCoprime_mul_unit_right_left, isCoprime_mul_unit_right_right, isCoprime_y_z, isUnit, pow_iff
-/
lemma isCoprime_Y_Z : IsCoprime S.Y S.Z := by
  rw [← IsCoprime.pow_iff (m := 3) (n := 3) (by decide) (by decide)]; rw [← isCoprime_mul_unit_right_left S.u₂.isUnit]; rw [← isCoprime_mul_unit_right_right S.u₃.isUnit]; rw [Y_u₂_spec]; rw [Z_u₃_spec]
  exact isCoprime_y_z S

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
/--
lemma `formula1` / 引理 `formula1`

English:
lemma formula1
  statement: S.X^3*S.u₁*fun^(3*S.multiplicity-2)+S.Y^3*S.u₂*fun*η+S.Z^3*S.u₃*fun*η^2 = 0
  proof: by
  rw [X_u₁_spec]; rw [Y_u₂_spec]; rw [Z_u₃_spec]; rw [mul_comm S.x]; rw [← x_spec]; rw [mul_comm S.y]; rw [← y_spec]; rw [mul_comm S.z]; rw [← z_spec]; rw [eta_sq]
  calc _ = S.a+S.b+η^2*S.b-S.a+η^2*S.b+2*η*S.b+S.b := by ring
  _ = 0 := by rw [eta_sq]; ring

中文:
引理 formula1
  结论: S.X^3*S.u₁*fun^(3*S.multiplicity-2)+S.Y^3*S.u₂*fun*η+S.Z^3*S.u₃*fun*η^2 = 0
  证明: by
  rw [X_u₁_spec]; rw [Y_u₂_spec]; rw [Z_u₃_spec]; rw [mul_comm S.x]; rw [← x_spec]; rw [mul_comm S.y]; rw [← y_spec]; rw [mul_comm S.z]; rw [← z_spec]; rw [eta_sq]
  calc _ = S.a+S.b+η^2*S.b-S.a+η^2*S.b+2*η*S.b+S.b := by ring
  _ = 0 := by rw [eta_sq]; ring

Depends on / 依赖: eta_sq, mul_comm, x_spec, y_spec, z_spec
-/
lemma formula1 : S.X^3*S.u₁*fun^(3*S.multiplicity-2)+S.Y^3*S.u₂*fun*η+S.Z^3*S.u₃*fun*η^2 = 0 := by
  rw [X_u₁_spec]; rw [Y_u₂_spec]; rw [Z_u₃_spec]; rw [mul_comm S.x]; rw [← x_spec]; rw [mul_comm S.y]; rw [← y_spec]; rw [mul_comm S.z]; rw [← z_spec]; rw [eta_sq]
  calc _ = S.a+S.b+η^2*S.b-S.a+η^2*S.b+2*η*S.b+S.b := by ring
  _ = 0 := by rw [eta_sq]; ring

/--
Definition of `u₄` / `u₄` 的定义

English:
definition u₄
  body: η * S.u₃ * S.u₂⁻¹

中文:
定义 u₄
  定义体: η * S.u₃ * S.u₂⁻¹
-/
noncomputable def u₄ := η * S.u₃ * S.u₂⁻¹
/--
lemma `u₄_def` / 引理 `u₄_def`

English:
lemma u₄_def
  statement: S.u₄ = η * S.u₃ * S.u₂⁻¹
  proof: rfl

中文:
引理 u₄_def
  结论: S.u₄ = η * S.u₃ * S.u₂⁻¹
  证明: rfl
-/
lemma u₄_def : S.u₄ = η * S.u₃ * S.u₂⁻¹ := rfl
/--
Definition of `u₅` / `u₅` 的定义

English:
definition u₅
  body: -η ^ 2 * S.u₁ * S.u₂⁻¹

中文:
定义 u₅
  定义体: -η ^ 2 * S.u₁ * S.u₂⁻¹
-/
noncomputable def u₅ := -η ^ 2 * S.u₁ * S.u₂⁻¹
/--
lemma `u₅_def` / 引理 `u₅_def`

English:
lemma u₅_def
  statement: S.u₅ = -η ^ 2 * S.u₁ * S.u₂⁻¹
  proof: rfl

example (a b : 𝓞 K) (ha : a != 0) (hb : b != 0) : a * b != 0 := by
  exact mul_ne_zero ha hb

中文:
引理 u₅_def
  结论: S.u₅ = -η ^ 2 * S.u₁ * S.u₂⁻¹
  证明: rfl

example (a b : 𝓞 K) (ha : a != 0) (hb : b != 0) : a * b != 0 := by
  exact mul_ne_zero ha hb
-/
lemma u₅_def : S.u₅ = -η ^ 2 * S.u₁ * S.u₂⁻¹ := rfl

example (a b : 𝓞 K) (ha : a != 0) (hb : b != 0) : a * b != 0 := by
  exact mul_ne_zero ha hb

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
/--
lemma `formula2` / 引理 `formula2`

English:
lemma formula2
  proof: by
  rw [u₅_def]; rw [neg_mul]; rw [neg_mul]; rw [Units.val_neg]; rw [neg_mul]; rw [eq_neg_iff_add_eq_zero]; rw [add_assoc]; rw [add_comm (S.u₄ * S.Z ^ 3)]; rw [← add_assoc]; rw [add_comm (S.Y ^ 3)]
apply mul_right_cancel₀ mul_ne_zero
    (mul_ne_zero hζ.zeta_sub_one_prime'.ne_zero S.u₂.isUnit.ne_ze

中文:
引理 formula2
  证明: by
  rw [u₅_def]; rw [neg_mul]; rw [neg_mul]; rw [Units.val_neg]; rw [neg_mul]; rw [eq_neg_iff_add_eq_zero]; rw [add_assoc]; rw [add_comm (S.u₄ * S.Z ^ 3)]; rw [← add_assoc]; rw [add_comm (S.Y ^ 3)]
apply mul_right_cancel₀ mul_ne_zero
    (mul_ne_zero hζ.zeta_sub_one_prime'.ne_zero S.u₂.isUnit.ne_ze

Depends on / 依赖: S.multiplicity, S.two_le_multiplicity, Units.isUnit, Units.val_neg, add_assoc, add_comm, add_mul, congrm, eq_neg_iff_add_eq_zero, formula1, isUnit, isUnit.ne_zero, mul_ne_zero, multiplicity, ne_zero, neg_mul, two_le_multiplicity, val_neg, zero_mul, zeta_sub_one_prime
-/
lemma formula2 :
    S.Y ^ 3 + S.u₄ * S.Z ^ 3 = S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  rw [u₅_def]; rw [neg_mul]; rw [neg_mul]; rw [Units.val_neg]; rw [neg_mul]; rw [eq_neg_iff_add_eq_zero]; rw [add_assoc]; rw [add_comm (S.u₄ * S.Z ^ 3)]; rw [← add_assoc]; rw [add_comm (S.Y ^ 3)]
apply mul_right_cancel₀ mul_ne_zero
    (mul_ne_zero hζ.zeta_sub_one_prime'.ne_zero S.u₂.isUnit.ne_zero) (Units.isUnit η).ne_zero
  simp only [zero_mul, add_mul]
  rw [← formula1 S]
  congrm ?_ + ?_ + ?_
  · have : (S.multiplicity-1)*3+1 = 3*S.multiplicity-2 := by have := S.two_le_multiplicity; lia
    calc _ = S.X^3 *(S.u₂*S.u₂⁻¹)*(η^3*S.u₁)*(fun^((S.multiplicity-1)*3)*fun) := by push_cast; ring
    _ = S.X^3*S.u₁*fun^(3*S.multiplicity-2) := by simp [hζ.toInteger_cube_eq_one, ← pow_succ, this]
  · ring
  · simp only [u₄_def, inv_eq_one_div, mul_div_assoc', mul_one, val_div_eq_divp, Units.val_mul,
      IsUnit.unit_spec, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]
    ring

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
/--
lemma `lambda_sq_div_u₅_mul` / 引理 `lambda_sq_div_u₅_mul`

English:
lemma lambda_sq_div_u₅_mul
  statement: fun ^ 2 ∣ S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3
  proof: by
  use fun^(3*S.multiplicity-5)*S.u₅*(S.X^3)
  have : 3*(S.multiplicity-1) = 2+(3*S.multiplicity-5) := by have := S.two_le_multiplicity; lia
  calc _ = fun^(3*(S.multiplicity-1))*S.u₅*S.X^3 := by ring
  _ = fun^2*fun^(3*S.multiplicity-5)*S.u₅*S.X^3 := by rw [this, pow_add]
  _ = fun^2*(fun^(3*S.mu

中文:
引理 lambda_sq_div_u₅_mul
  结论: fun ^ 2 ∣ S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3
  证明: by
  use fun^(3*S.multiplicity-5)*S.u₅*(S.X^3)
  have : 3*(S.multiplicity-1) = 2+(3*S.multiplicity-5) := by have := S.two_le_multiplicity; lia
  calc _ = fun^(3*(S.multiplicity-1))*S.u₅*S.X^3 := by ring
  _ = fun^2*fun^(3*S.multiplicity-5)*S.u₅*S.X^3 := by rw [this, pow_add]
  _ = fun^2*(fun^(3*S.mu

Depends on / 依赖: S.multiplicity, S.two_le_multiplicity, multiplicity, pow_add, two_le_multiplicity
-/
lemma lambda_sq_div_u₅_mul : fun ^ 2 ∣ S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  use fun^(3*S.multiplicity-5)*S.u₅*(S.X^3)
  have : 3*(S.multiplicity-1) = 2+(3*S.multiplicity-5) := by have := S.two_le_multiplicity; lia
  calc _ = fun^(3*(S.multiplicity-1))*S.u₅*S.X^3 := by ring
  _ = fun^2*fun^(3*S.multiplicity-5)*S.u₅*S.X^3 := by rw [this, pow_add]
  _ = fun^2*(fun^(3*S.multiplicity-5)*S.u₅*S.X^3) := by ring

/--
lemma `u₄_eq_one_or_neg_one` / 引理 `u₄_eq_one_or_neg_one`

English:
lemma u₄_eq_one_or_neg_one
  statement: S.u₄ = 1 ∨ S.u₄ = -1
  proof: by
  have : fun ^ 2 ∣ fun ^ 4 := ⟨fun ^ 2, by ring⟩
  have h := S.lambda_sq_div_u₅_mul
  apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ
  rcases h with ⟨X, hX⟩
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.lambda_not_dvd_Y with
    HY | 

中文:
引理 u₄_eq_one_or_neg_one
  结论: S.u₄ = 1 ∨ S.u₄ = -1
  证明: by
  have : fun ^ 2 ∣ fun ^ 4 := ⟨fun ^ 2, by ring⟩
  have h := S.lambda_sq_div_u₅_mul
  apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ
  rcases h with ⟨X, hX⟩
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.lambda_not_dvd_Y with
    HY | 

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent, S.lambda_not_dvd_Y, S.lambda_not_dvd_Z, S.lambda_sq_div_u, eq_one_or_neg_one_of_unit_of_congruent, lambda_not_dvd_Y, lambda_not_dvd_Z, lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd, replace, this.trans
-/
lemma u₄_eq_one_or_neg_one : S.u₄ = 1 ∨ S.u₄ = -1 := by
  have : fun ^ 2 ∣ fun ^ 4 := ⟨fun ^ 2, by ring⟩
  have h := S.lambda_sq_div_u₅_mul
  apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ
  rcases h with ⟨X, hX⟩
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.lambda_not_dvd_Y with
    HY | HY <;> rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd
      hζ S.lambda_not_dvd_Z with HZ | HZ <;> replace HY := this.trans HY <;> replace HZ :=
      this.trans HZ <;> rcases HY with ⟨Y, hY⟩ <;> rcases HZ with ⟨Z, hZ⟩
  · refine ⟨-1, X - Y - S.u₄ * Z, ?_⟩
    rw [show fun ^ 2 * (X - Y - S.u₄ * Z) = fun ^ 2 * X - fun ^ 2 * Y - S.u₄ * (fun ^ 2 * Z) by ring]; rw [← hX]; rw [← hY]; rw [← hZ]; rw [← formula2]
    ring
  · refine ⟨1, -X + Y + S.u₄ * Z, ?_⟩
    rw [show fun ^ 2 * (-X + Y + S.u₄ * Z) = -(fun ^ 2 * X - fun ^ 2 * Y - S.u₄ * (fun ^ 2 * Z)) by ring]; rw [← hX]; rw [← hY]; rw [← hZ]; rw [← formula2]
    ring
  · refine ⟨1, X - Y - S.u₄ * Z, ?_⟩
    rw [show fun ^ 2 * (X - Y - S.u₄ * Z) = fun ^ 2 * X - fun ^ 2 * Y - S.u₄ * (fun ^ 2 * Z) by ring]; rw [← hX]; rw [← hY]; rw [← hZ]; rw [← formula2]
    ring
  · refine ⟨-1, -X + Y + S.u₄ * Z, ?_⟩
    rw [show fun ^ 2 * (-X + Y + S.u₄ * Z) = -(fun ^ 2 * X - fun ^ 2 * Y - S.u₄ * (fun ^ 2 * Z)) by ring]; rw [← hX]; rw [← hY]; rw [← hZ]; rw [← formula2]
    ring

/--
lemma `u₄_sq` / 引理 `u₄_sq`

English:
lemma u₄_sq
  statement: S.u₄ ^ 2 = 1
  proof: by
  rcases S.u₄_eq_one_or_neg_one with h | h <;> simp [h]

中文:
引理 u₄_sq
  结论: S.u₄ ^ 2 = 1
  证明: by
  rcases S.u₄_eq_one_or_neg_one with h | h <;> simp [h]
-/
lemma u₄_sq : S.u₄ ^ 2 = 1 := by
  rcases S.u₄_eq_one_or_neg_one with h | h <;> simp [h]

/--
lemma `formula3` / 引理 `formula3`

English:
lemma formula3
  proof: calc S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.Y ^ 3 + S.u₄ ^ 2 * S.u₄ * S.Z ^ 3 := by ring
  _ = S.Y ^ 3 + S.u₄ * S.Z ^ 3 := by simp [← Units.val_pow_eq_pow_val, S.u₄_sq]
  _ = S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3 := S.formula2

中文:
引理 formula3
  证明: calc S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.Y ^ 3 + S.u₄ ^ 2 * S.u₄ * S.Z ^ 3 := by ring
  _ = S.Y ^ 3 + S.u₄ * S.Z ^ 3 := by simp [← Units.val_pow_eq_pow_val, S.u₄_sq]
  _ = S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3 := S.formula2

Depends on / 依赖: S.formula2, S.multiplicity, Units.val_pow_eq_pow_val, formula2, multiplicity, val_pow_eq_pow_val
-/
lemma formula3 :
    S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3 :=
  calc S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.Y ^ 3 + S.u₄ ^ 2 * S.u₄ * S.Z ^ 3 := by ring
  _ = S.Y ^ 3 + S.u₄ * S.Z ^ 3 := by simp [← Units.val_pow_eq_pow_val, S.u₄_sq]
  _ = S.u₅ * (fun ^ (S.multiplicity - 1) * S.X) ^ 3 := S.formula2

/--
Definition of `Solution'_descent` / `Solution'_descent` 的定义

English:
definition Solution'_descent
  signature: : Solution' hζ where
  body: S.Y
  b := S.u₄ * S.Z
  c := fun ^ (S.multiplicity - 1) * S.X
  u := S.u₅
  ha := S.lambda_not_dvd_Y
hb := fun h => S.lambda_not_dvd_Z Units.dvd_mul_left.1 h
hc := fun h => S.X_ne_zero by simpa [hζ.zeta_sub_one_prime'.ne_zero] using h
  coprime := (isCoprime_mul_unit_left_right S.u₄.isUnit _ _).2 S.

中文:
定义 Solution'_descent
  签名: : Solution' hζ where
  定义体: S.Y
  b := S.u₄ * S.Z
  c := fun ^ (S.multiplicity - 1) * S.X
  u := S.u₅
  ha := S.lambda_not_dvd_Y
hb := fun h => S.lambda_not_dvd_Z Units.dvd_mul_left.1 h
hc := fun h => S.X_ne_zero by simpa [hζ.zeta_sub_one_prime'.ne_zero] using h
  coprime := (isCoprime_mul_unit_left_right S.u₄.isUnit _ _).2 S.
-/
noncomputable def Solution'_descent : Solution' hζ where
  a := S.Y
  b := S.u₄ * S.Z
  c := fun ^ (S.multiplicity - 1) * S.X
  u := S.u₅
  ha := S.lambda_not_dvd_Y
hb := fun h => S.lambda_not_dvd_Z Units.dvd_mul_left.1 h
hc := fun h => S.X_ne_zero by simpa [hζ.zeta_sub_one_prime'.ne_zero] using h
  coprime := (isCoprime_mul_unit_left_right S.u₄.isUnit _ _).2 S.isCoprime_Y_Z
  hcdvd := by
    refine dvd_mul_of_dvd_left (dvd_pow_self _ (fun h => ?_)) _
    rw [Nat.sub_eq_iff_eq_add (le_trans (by simp) S.two_le_multiplicity)]; rw [zero_add] at h
    simpa [h] using S.two_le_multiplicity
  H := formula3 S

/--
lemma `Solution'_descent_multiplicity` / 引理 `Solution'_descent_multiplicity`

English:
lemma Solution'_descent_multiplicity
  statement: S.Solution'_descent.multiplicity = S.multiplicity - 1
  proof: by
  refine multiplicity_eq_of_dvd_of_not_dvd
    (by simp [Solution'_descent]) (fun h => S.lambda_not_dvd_X ?_)
  obtain ⟨k, hk : fun ^ (S.multiplicity - 1) * S.X = fun ^ (S.multiplicity - 1 + 1) * k⟩ := h
  rw [pow_succ]; rw [mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.

中文:
引理 Solution'_descent_multiplicity
  结论: S.Solution'_descent.multiplicity = S.multiplicity - 1
  证明: by
  refine multiplicity_eq_of_dvd_of_not_dvd
    (by simp [Solution'_descent]) (fun h => S.lambda_not_dvd_X ?_)
  obtain ⟨k, hk : fun ^ (S.multiplicity - 1) * S.X = fun ^ (S.multiplicity - 1 + 1) * k⟩ := h
  rw [pow_succ]; rw [mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.
-/
lemma Solution'_descent_multiplicity : S.Solution'_descent.multiplicity = S.multiplicity - 1 := by
  refine multiplicity_eq_of_dvd_of_not_dvd
    (by simp [Solution'_descent]) (fun h => S.lambda_not_dvd_X ?_)
  obtain ⟨k, hk : fun ^ (S.multiplicity - 1) * S.X = fun ^ (S.multiplicity - 1 + 1) * k⟩ := h
  rw [pow_succ]; rw [mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.zeta_sub_one_prime'.ne_zero, ne_eq,
    false_and, or_false] at hk
  simp [hk]

/--
lemma `Solution'_descent_multiplicity_lt` / 引理 `Solution'_descent_multiplicity_lt`

English:
lemma Solution'_descent_multiplicity_lt
  proof: by
  rw [Solution'_descent_multiplicity S]; rw [Nat.sub_one]
exact Nat.pred_lt by have := S.two_le_multiplicity; lia

中文:
引理 Solution'_descent_multiplicity_lt
  证明: by
  rw [Solution'_descent_multiplicity S]; rw [Nat.sub_one]
exact Nat.pred_lt by have := S.two_le_multiplicity; lia
-/
lemma Solution'_descent_multiplicity_lt :
    (Solution'_descent S).multiplicity < S.multiplicity := by
  rw [Solution'_descent_multiplicity S]; rw [Nat.sub_one]
exact Nat.pred_lt by have := S.two_le_multiplicity; lia

/--
theorem `exists_Solution_multiplicity_lt` / 定理 `exists_Solution_multiplicity_lt`

English:
theorem exists_Solution_multiplicity_lt
  proof: by
  obtain ⟨S', hS'⟩ := exists_Solution_of_Solution' (Solution'_descent S)
  exact ⟨S', hS' ▸ Solution'_descent_multiplicity_lt S⟩

中文:
定理 exists_Solution_multiplicity_lt
  证明: by
  obtain ⟨S', hS'⟩ := exists_Solution_of_Solution' (Solution'_descent S)
  exact ⟨S', hS' ▸ Solution'_descent_multiplicity_lt S⟩

Depends on / 依赖: Solution, _descent, _descent_multiplicity_lt, exists_Solution_of_Solution
-/
theorem exists_Solution_multiplicity_lt :
    exists S₁ : Solution hζ, S₁.multiplicity < S.multiplicity := by
  obtain ⟨S', hS'⟩ := exists_Solution_of_Solution' (Solution'_descent S)
  exact ⟨S', hS' ▸ Solution'_descent_multiplicity_lt S⟩

end Solution

end FermatLastTheoremForThreeGen

end eisenstein

end case2

set_option backward.isDefEq.respectTransparency false in
/-- Fermat's Last Theorem for `n = 3`: if `a b c : ℕ` are all non-zero then
`a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
public theorem fermatLastTheoremThree : FermatLastTheoremFor 3 := by
  let K := CyclotomicField 3 Rat
  let hζ := IsCyclotomicExtension.zeta_spec 3 Rat K
  have : NumberField K := IsCyclotomicExtension.numberField {3} Rat _
  apply FermatLastTheoremForThree_of_FermatLastTheoremThreeGen hζ
  intro a b c u hc ha hb hcdvd coprime H
  let S' : FermatLastTheoremForThreeGen.Solution' hζ :=
  { a := a
    b := b
    c := c
    u := u
    ha := ha
    hb := hb
    hc := hc
    coprime := coprime
    hcdvd := hcdvd
    H := H }
  obtain ⟨S, -⟩ := FermatLastTheoremForThreeGen.exists_Solution_of_Solution' S'
  obtain ⟨Smin, hSmin⟩ := S.exists_minimal
  obtain ⟨Sfin, hSfin⟩ := Smin.exists_Solution_multiplicity_lt
  linarith [hSmin Sfin]
