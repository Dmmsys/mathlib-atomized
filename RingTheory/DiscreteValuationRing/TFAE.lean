/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Zero

/-!

# Equivalent conditions for DVR

In `IsDiscreteValuationRing.TFAE`, we show that the following are equivalent for a
Noetherian local domain that is not a field `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a Dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

Also see `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` for a version without `¬ IsField R`.
-/

public section


variable (R : Type*) [CommRing R]

open scoped Multiplicative

open IsLocalRing Module

/--
theorem `exists_maximalIdeal_pow_eq_of_principal` / 定理 `exists_maximalIdeal_pow_eq_of_principal`

English:
theorem exists_maximalIdeal_pow_eq_of_principal
  statement: [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
  proof: by
  by_cases h : IsField R
  · let _ := h.toField
    exact ⟨0, by simp [(eq_bot_or_eq_top I).resolve_left hI]⟩
  classical
  obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
  by_cases hI' : I = ⊤
  · use 0; rw [pow_zero, hI', Ideal.one_eq_top]
  have H : forall r : R, ¬IsUnit r ↔ x ∣ r := fun r =>
    (Se

中文:
定理 存在_maximalIdeal_pow_eq_of_principal
  结论: [是Noether环 R] [是局部环 R] [是整环 R]
  证明: by
  by_cases h : IsField R
  · let _ := h.toField
    exact ⟨0, by simp [(eq_bot_or_eq_top I).resolve_left hI]⟩
  classical
  obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
  by_cases hI' : I = ⊤
  · use 0; rw [pow_zero, hI', Ideal.one_eq_top]
  have H : forall r : R, ¬IsUnit r ↔ x ∣ r := fun r =>
    (Se

Depends on / 依赖: Ideal.mem_span_singleton, Ideal.one_eq_top, Ideal.span, IsDiscreteValuationRing, IsDiscreteValuationRing.irreducible_of_s, IsField, IsUnit, Ring.ne_bot_of_isMaximal_of_not_isField, SetLike, SetLike.ext_iff.mp, classical, eq_bot_or_eq_top, ext_iff, h.toField, irreducible_of_s, isMaximal, maximalIdeal, maximalIdeal.isMaximal, mem_span_singleton, ne_bot_of_isMaximal_of_not_isField
-/
theorem exists_maximalIdeal_pow_eq_of_principal [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I != ⊥) :
    exists n : Nat, I = maximalIdeal R ^ n := by
  by_cases h : IsField R
  · let _ := h.toField
    exact ⟨0, by simp [(eq_bot_or_eq_top I).resolve_left hI]⟩
  classical
  obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
  by_cases hI' : I = ⊤
  · use 0; rw [pow_zero, hI', Ideal.one_eq_top]
  have H : forall r : R, ¬IsUnit r ↔ x ∣ r := fun r =>
    (SetLike.ext_iff.mp hx r).trans Ideal.mem_span_singleton
  have : x != 0 := by
    rintro rfl
    apply Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal R) h
    simp [hx]
  have hx' := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x this hx
  have H' : forall r : R, r != 0 -> r in nonunits R -> exists n : Nat, Associated (x ^ n) r := by
    intro r hr₁ hr₂
    obtain ⟨f, hf₁, rfl, hf₂⟩ := (WfDvdMonoid.not_isUnit_iff_exists_factors_eq r hr₁).mp hr₂
    have : forall b in f, Associated x b := by
      intro b hb
      exact Irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1)
    clear hr₁ hr₂ hf₁
    induction f using Multiset.induction with
    | empty => exact (hf₂ rfl).elim
    | cons fa fs fh => ?_
    rcases eq_or_ne fs ∅ with (rfl | hf')
    · use 1
      rw [pow_one]; rw [Multiset.prod_cons]; rw [Multiset.empty_eq_zero]; rw [Multiset.prod_zero]; rw [mul_one]
      exact this _ (Multiset.mem_cons_self _ _)
    · obtain ⟨n, hn⟩ := fh hf' fun b hb => this _ (Multiset.mem_cons_of_mem hb)
      use n + 1
      rw [pow_add]; rw [Multiset.prod_cons]; rw [mul_comm]; rw [pow_one]
      exact Associated.mul_mul (this _ (Multiset.mem_cons_self _ _)) hn
  have : exists n : Nat, x ^ n in I := by
    obtain ⟨r, hr₁, hr₂⟩ : exists r : R, r in I ∧ r != 0 := by
      by_contra! h; apply hI; rw [eq_bot_iff]; exact h
    obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximalIdeal hI' hr₁)
    use n
    rwa [← I.unit_mul_mem_iff_mem u.isUnit, mul_comm]
  use Nat.find this
  apply le_antisymm
  · change forall s in I, s in _
    by_contra! ⟨s, hs₁, hs₂⟩
    apply hs₂
    by_cases hs₃ : s = 0; · rw [hs₃]; exact zero_mem _
    obtain ⟨n, u, rfl⟩ := H' s hs₃ (le_maximalIdeal hI' hs₁)
    rw [mul_comm]; rw [Ideal.unit_mul_mem_iff_mem _ u.isUnit] at hs₁ ⊢
    apply Ideal.pow_le_pow_right (Nat.find_min' this hs₁)
    apply Ideal.pow_mem_pow
    exact (H _).mpr (dvd_refl _)
  · rw [hx, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Nat.find_spec this

/--
theorem `maximalIdeal_isPrincipal_of_isDedekindDomain` / 定理 `maximalIdeal_isPrincipal_of_isDedekindDomain`

English:
theorem maximalIdeal_isPrincipal_of_isDedekindDomain
  given: [IsLocalRing R] [IsDedekindDomain R]
  proof: by
  classical
  by_cases ne_bot : maximalIdeal R = ⊥
  · rw [ne_bot]; infer_instance
  obtain ⟨a, ha₁, ha₂⟩ : exists a in maximalIdeal R, a != (0 : R) := by
    by_contra! h'; apply ne_bot; rwa [eq_bot_iff]
  have hle : Ideal.span {a} <= maximalIdeal R := by rwa [Ideal.span_le, Set.singleton_subset

中文:
定理 maximalIdeal_isPrincipal_of_isDedekindDomain
  条件: [是局部环 R] [是Dedekind整环 R]
  证明: by
  classical
  by_cases ne_bot : maximalIdeal R = ⊥
  · rw [ne_bot]; infer_instance
  obtain ⟨a, ha₁, ha₂⟩ : exists a in maximalIdeal R, a != (0 : R) := by
    by_contra! h'; apply ne_bot; rwa [eq_bot_iff]
  have hle : Ideal.span {a} <= maximalIdeal R := by rwa [Ideal.span_le, Set.singleton_subset

Depends on / 依赖: Ideal.radical_eq_sInf, Ideal.span, Ideal.span_le, Set.singleton_subset_iff, classical, eq_bot_iff, eq_maximalIdeal, infer_instance, isMaximal, le_antisymm, le_sInf, maximalIdeal, ne_bot, radical, radical_eq_sInf, sInf_le, singleton_subset_iff, span_le
-/
theorem maximalIdeal_isPrincipal_of_isDedekindDomain [IsLocalRing R] [IsDedekindDomain R] :
    (maximalIdeal R).IsPrincipal := by
  classical
  by_cases ne_bot : maximalIdeal R = ⊥
  · rw [ne_bot]; infer_instance
  obtain ⟨a, ha₁, ha₂⟩ : exists a in maximalIdeal R, a != (0 : R) := by
    by_contra! h'; apply ne_bot; rwa [eq_bot_iff]
  have hle : Ideal.span {a} <= maximalIdeal R := by rwa [Ideal.span_le, Set.singleton_subset_iff]
  have : (Ideal.span {a}).radical = maximalIdeal R := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hle, inferInstance⟩
    · refine
        le_sInf fun I hI =>
          (eq_maximalIdeal <| hI.2.isMaximal (fun e => ha₂ ?_)).ge
      rw [← Ideal.span_singleton_eq_bot]; rw [eq_bot_iff]; rw [← e]; exact hI.1
  have : exists n, maximalIdeal R ^ n <= Ideal.span {a} := by
    rw [← this]; apply Ideal.exists_radical_pow_le_of_fg; exact IsNoetherian.noetherian _
  rcases hn : Nat.find this with - | n
  · have := Nat.find_spec this
    rw [hn]; rw [pow_zero]; rw [Ideal.one_eq_top] at this
    exact (Ideal.IsMaximal.ne_top inferInstance (eq_top_iff.mpr <| this.trans hle)).elim
  obtain ⟨b, hb₁, hb₂⟩ : exists b in maximalIdeal R ^ n, b ∉ Ideal.span {a} := by
    by_contra! h'; rw [Nat.find_eq_iff] at hn; exact hn.2 n n.lt_succ_self fun x hx => h' x hx
  have hb₃ : forall m in maximalIdeal R, exists k : R, k * a = b * m := by
    intro m hm; rw [← Ideal.mem_span_singleton']; apply Nat.find_spec this
    rw [hn]; rw [pow_succ]; exact Ideal.mul_mem_mul hb₁ hm
  have hb₄ : b != 0 := by rintro rfl; apply hb₂; exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have ha₃ : algebraMap R K a != 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx : forall y in M, x * y in M
  · have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine (hb₂ (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul]; rw [e]; rw [div_mul_cancel₀ _ ha₃]
    · rw [Submodule.ne_bot_iff]; refine ⟨_, ⟨a, ha₁, rfl⟩, ?_⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha₂
    · apply Submodule.FG.map; exact IsNoetherian.noetherian _
  · have :
        (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hx with h
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm]; rw [← map_mul]; rw [← hk]; rw [map_mul]; rw [mul_div_cancel_right₀ _ ha₃]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : exists y in maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one]; rw [Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one]; rw [← mul_div_right_comm]; rw [div_eq_one_iff_eq ha₃]; rw [← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm; obtain ⟨k, hk⟩ := hb₃ m hm; rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk]; rw [mul_comm]; exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

/--
theorem `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` / 定理 `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`

English:
theorem tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
  proof: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 -> 1 := fun _ => ((IsBezout.TFAE (R := R)).out 0 1).mp ‹_›
  tfae_have 1 -> 4
  | H => ⟨inferInstance, fun P hP hP' => eq_maximalIdeal (hP'.isMaximal hP)⟩
  tfae_have 4 -> 3 :=
    fun ⟨h₁, h₂⟩ => { h₁ with maximalOfPrime := (h₂ _ · · ▸ m

中文:
定理 tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
  证明: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 -> 1 := fun _ => ((IsBezout.TFAE (R := R)).out 0 1).mp ‹_›
  tfae_have 1 -> 4
  | H => ⟨inferInstance, fun P hP hP' => eq_maximalIdeal (hP'.isMaximal hP)⟩
  tfae_have 4 -> 3 :=
    fun ⟨h₁, h₂⟩ => { h₁ with maximalOfPrime := (h₂ _ · · ▸ m

Depends on / 依赖: IsBezout, IsBezout.TFAE, eq_maximalIdeal, exists_maximalIdeal_pow_eq_of_principa, finrank_cotangentSpace_le_one_iff, isMaximal, maximalIdeal, maximalIdeal.isMaximal, maximalIdeal_isPrincipal_of_isDedekindDomain, maximalOfPrime, tfae_have
-/
theorem tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] :
    List.TFAE
      [IsPrincipalIdealRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ forall P : Ideal R, P != ⊥ -> P.IsPrime -> P = maximalIdeal R,
        (maximalIdeal R).IsPrincipal,
        finrank (ResidueField R) (CotangentSpace R) <= 1,
        forall I != ⊥, exists n : Nat, I = maximalIdeal R ^ n] := by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 -> 1 := fun _ => ((IsBezout.TFAE (R := R)).out 0 1).mp ‹_›
  tfae_have 1 -> 4
  | H => ⟨inferInstance, fun P hP hP' => eq_maximalIdeal (hP'.isMaximal hP)⟩
  tfae_have 4 -> 3 :=
    fun ⟨h₁, h₂⟩ => { h₁ with maximalOfPrime := (h₂ _ · · ▸ maximalIdeal.isMaximal R) }
  tfae_have 3 -> 5 := fun h => maximalIdeal_isPrincipal_of_isDedekindDomain R
  tfae_have 6 ↔ 5 := finrank_cotangentSpace_le_one_iff
  tfae_have 5 -> 7 := exists_maximalIdeal_pow_eq_of_principal R
  tfae_have 7 -> 2 := by
    rw [ValuationRing.iff_ideal_total]
    intro H
    constructor
    intro I J
    by_cases hI : I = ⊥; · order
    by_cases hJ : J = ⊥; · order
    obtain ⟨n, rfl⟩ := H I hI
    obtain ⟨m, rfl⟩ := H J hJ
    exact (le_total m n).imp Ideal.pow_le_pow_right Ideal.pow_le_pow_right
  tfae_finish

/--
theorem `IsDiscreteValuationRing.TFAE` / 定理 `IsDiscreteValuationRing.TFAE`

English:
theorem IsDiscreteValuationRing.TFAE
  statement: [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
  proof: by
  have : finrank (ResidueField R) (CotangentSpace R) = 1 ↔
      finrank (ResidueField R) (CotangentSpace R) <= 1 := by
    simp [Nat.le_one_iff_eq_zero_or_eq_one, finrank_cotangentSpace_eq_zero_iff, h]
  rw [this]
  have : maximalIdeal R != ⊥ := isField_iff_maximalIdeal_eq.not.mp h
  convert! tf

中文:
定理 是离散赋值环.TFAE
  结论: [是Noether环 R] [是局部环 R] [是整环 R]
  证明: by
  have : finrank (ResidueField R) (CotangentSpace R) = 1 ↔
      finrank (ResidueField R) (CotangentSpace R) <= 1 := by
    simp [Nat.le_one_iff_eq_zero_or_eq_one, finrank_cotangentSpace_eq_zero_iff, h]
  rw [this]
  have : maximalIdeal R != ⊥ := isField_iff_maximalIdeal_eq.not.mp h
  convert! tf

Depends on / 依赖: CotangentSpace, Nat.le_one_iff_eq_zero_or_eq_one, ResidueField, convert, finrank, finrank_cotangentSpace_eq_zero_iff, h.unique, isField_iff_maximalIdeal_eq, isField_iff_maximalIdeal_eq.not.mp, le_one_iff_eq_zero_or_eq_one, maximalIdeal, not_a_field, tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain, unique
-/
theorem IsDiscreteValuationRing.TFAE [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h : ¬IsField R) :
    List.TFAE
      [IsDiscreteValuationRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ exists! P : Ideal R, P != ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal,
        finrank (ResidueField R) (CotangentSpace R) = 1,
        forall (I) (_ : I != ⊥), exists n : Nat, I = maximalIdeal R ^ n] := by
  have : finrank (ResidueField R) (CotangentSpace R) = 1 ↔
      finrank (ResidueField R) (CotangentSpace R) <= 1 := by
    simp [Nat.le_one_iff_eq_zero_or_eq_one, finrank_cotangentSpace_eq_zero_iff, h]
  rw [this]
  have : maximalIdeal R != ⊥ := isField_iff_maximalIdeal_eq.not.mp h
  convert! tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R
  · exact ⟨fun _ => inferInstance, fun h => { h with not_a_field' := this }⟩
  · exact ⟨fun h P h₁ h₂ => h.unique ⟨h₁, h₂⟩ ⟨this, inferInstance⟩,
      fun H => ⟨_, ⟨this, inferInstance⟩, fun P hP => H P hP.1 hP.2⟩⟩

variable {R}

/--
lemma `IsLocalRing.finrank_CotangentSpace_eq_one_iff` / 引理 `IsLocalRing.finrank_CotangentSpace_eq_one_iff`

English:
lemma IsLocalRing.finrank_CotangentSpace_eq_one_iff
  statement: [IsNoetherianRing R] [IsLocalRing R]
  proof: by
  by_cases hR : IsField R
  · let := hR.toField
    simp only [finrank_cotangentSpace_eq_zero, zero_ne_one, false_iff]
    exact fun h => h.3 maximalIdeal_eq_bot
  · exact (IsDiscreteValuationRing.TFAE R hR).out 5 0

中文:
引理 是局部环.finrank_CotangentSpace_eq_one_iff
  结论: [是Noether环 R] [是局部环 R]
  证明: by
  by_cases hR : IsField R
  · let := hR.toField
    simp only [finrank_cotangentSpace_eq_zero, zero_ne_one, false_iff]
    exact fun h => h.3 maximalIdeal_eq_bot
  · exact (IsDiscreteValuationRing.TFAE R hR).out 5 0

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.TFAE, IsField, false_iff, finrank_cotangentSpace_eq_zero, hR.toField, maximalIdeal_eq_bot, toField, zero_ne_one
-/
lemma IsLocalRing.finrank_CotangentSpace_eq_one_iff [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] : finrank (ResidueField R) (CotangentSpace R) = 1 ↔ IsDiscreteValuationRing R := by
  by_cases hR : IsField R
  · let := hR.toField
    simp only [finrank_cotangentSpace_eq_zero, zero_ne_one, false_iff]
    exact fun h => h.3 maximalIdeal_eq_bot
  · exact (IsDiscreteValuationRing.TFAE R hR).out 5 0

variable (R)

/--
lemma `IsLocalRing.finrank_CotangentSpace_eq_one` / 引理 `IsLocalRing.finrank_CotangentSpace_eq_one`

English:
lemma IsLocalRing.finrank_CotangentSpace_eq_one
  given: [IsDomain R] [IsDiscreteValuationRing R]
  proof: finrank_CotangentSpace_eq_one_iff.mpr ‹_›

中文:
引理 是局部环.finrank_CotangentSpace_eq_one
  条件: [是整环 R] [是离散赋值环 R]
  证明: finrank_CotangentSpace_eq_one_iff.mpr ‹_›

Depends on / 依赖: finrank_CotangentSpace_eq_one_iff, finrank_CotangentSpace_eq_one_iff.mpr
-/
lemma IsLocalRing.finrank_CotangentSpace_eq_one [IsDomain R] [IsDiscreteValuationRing R] :
    finrank (ResidueField R) (CotangentSpace R) = 1 :=
  finrank_CotangentSpace_eq_one_iff.mpr ‹_›

open Ring in
/--
lemma `IsDiscreteValuationRing.ringKrullDim_eq_one` / 引理 `IsDiscreteValuationRing.ringKrullDim_eq_one`

English:
lemma IsDiscreteValuationRing.ringKrullDim_eq_one
  given: [IsDomain R] [IsDiscreteValuationRing R]
  proof: by
  refine eq_of_le_of_not_lt (krullDimLE_iff (n := 1).mp ?_) fun h => ?_
  · exact krullDimLE_one_iff_of_isPrime_bot.mpr fun I hI hI' => hI'.isMaximal hI
  · have : KrullDimLE 0 R := krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp h)
    exact IsDiscreteValuationRing.not_isField R KrullDimLE.is

中文:
引理 是离散赋值环.ringKrullDim_eq_one
  条件: [是整环 R] [是离散赋值环 R]
  证明: by
  refine eq_of_le_of_not_lt (krullDimLE_iff (n := 1).mp ?_) fun h => ?_
  · exact krullDimLE_one_iff_of_isPrime_bot.mpr fun I hI hI' => hI'.isMaximal hI
  · have : KrullDimLE 0 R := krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp h)
    exact IsDiscreteValuationRing.not_isField R KrullDimLE.is

Depends on / 依赖: ENat.WithBot.lt_add_one_iff.mp, IsDiscreteValuationRing, IsDiscreteValuationRing.not_isField, KrullDimLE, KrullDimLE.isField_of_isDomain, WithBot, eq_of_le_of_not_lt, isField_of_isDomain, isMaximal, krullDimLE_iff, krullDimLE_iff.mpr, krullDimLE_one_iff_of_isPrime_bot, krullDimLE_one_iff_of_isPrime_bot.mpr, lt_add_one_iff, not_isField
-/
lemma IsDiscreteValuationRing.ringKrullDim_eq_one [IsDomain R] [IsDiscreteValuationRing R] :
    ringKrullDim R = 1 := by
  refine eq_of_le_of_not_lt (krullDimLE_iff (n := 1).mp ?_) fun h => ?_
  · exact krullDimLE_one_iff_of_isPrime_bot.mpr fun I hI hI' => hI'.isMaximal hI
  · have : KrullDimLE 0 R := krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp h)
    exact IsDiscreteValuationRing.not_isField R KrullDimLE.isField_of_isDomain

open Ring in
/--
lemma `IsDiscreteValuationRing.not_krullDimLE_zero` / 引理 `IsDiscreteValuationRing.not_krullDimLE_zero`

English:
lemma IsDiscreteValuationRing.not_krullDimLE_zero
  given: [IsDomain R] [IsDiscreteValuationRing R]
  proof: by
  simp [krullDimLE_iff, ringKrullDim_eq_one R]

中文:
引理 是离散赋值环.not_krullDimLE_zero
  条件: [是整环 R] [是离散赋值环 R]
  证明: by
  simp [krullDimLE_iff, ringKrullDim_eq_one R]

Depends on / 依赖: krullDimLE_iff, ringKrullDim_eq_one
-/
lemma IsDiscreteValuationRing.not_krullDimLE_zero [IsDomain R] [IsDiscreteValuationRing R] :
      ¬ KrullDimLE 0 R := by
  simp [krullDimLE_iff, ringKrullDim_eq_one R]

open Ring in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] [IsDiscreteValuationRing R] : KrullDimLE 1 R
  body: krullDimLE_iff.mpr (IsDiscreteValuationRing.ringKrullDim_eq_one R).le

中文:
实例 [是整环
  签名: R] [是离散赋值环 R] : Krull维数不超过 1 R
  定义体: krullDimLE_iff.mpr (IsDiscreteValuationRing.ringKrullDim_eq_one R).le

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.ringKrullDim_eq_one, krullDimLE_iff, krullDimLE_iff.mpr, ringKrullDim_eq_one
-/
instance [IsDomain R] [IsDiscreteValuationRing R] : KrullDimLE 1 R :=
    krullDimLE_iff.mpr (IsDiscreteValuationRing.ringKrullDim_eq_one R).le

instance (priority := 100) IsDedekindDomain.isPrincipalIdealRing
    [IsLocalRing R] [IsDedekindDomain R] : IsPrincipalIdealRing R :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 2 0).mp ‹_›
