/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!

# Maximal ideal of local rings

We prove basic properties of the maximal ideal of a local ring.

-/

public section

namespace IsLocalRing

variable {R S K : Type*}

section CommSemiring

variable [CommSemiring R] [IsLocalRing R]

@[simp]
/--
theorem `mem_maximalIdeal` / 定理 `mem_maximalIdeal`

English:
theorem mem_maximalIdeal
  given: (x)
  statement: x in maximalIdeal R ↔ x in nonunits R
  proof: Iff.rfl

中文:
定理 mem_maximalIdeal
  条件: (x)
  结论: x in maximalIdeal R ↔ x in nonunits R
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_maximalIdeal (x) : x in maximalIdeal R ↔ x in nonunits R :=
  Iff.rfl

variable (R)

/--
Instance `maximalIdeal.isMaximal` / 实例 `maximalIdeal.isMaximal`

English:
instance maximalIdeal.isMaximal
  signature: : (maximalIdeal R).IsMaximal
  body: by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    rw [mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H

中文:
实例 maximalIdeal.isMaximal
  签名: : (maximalIdeal R).是极大
  定义体: by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    rw [mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H

Depends on / 依赖: Classical, Classical.not_not, I.mul_mem_left, Ideal.isMaximal_iff, isMaximal_iff, isUnit_one, mem_maximalIdeal, mem_nonunits_iff, mul_mem_left, not_not
-/
instance maximalIdeal.isMaximal : (maximalIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    rw [mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H

/--
theorem `isMaximal_iff` / 定理 `isMaximal_iff`

English:
theorem isMaximal_iff
  given: {I : Ideal R}
  statement: I.IsMaximal ↔ I = maximalIdeal R where
  proof: hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ h => hI.1.1 ∘ I.eq_top_of_isUnit_mem h
  mpr e := e ▸ maximalIdeal.isMaximal R

中文:
定理 isMaximal_iff
  条件: {I : 理想 R}
  结论: I.是极大 ↔ I = maximalIdeal R where
  证明: hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ h => hI.1.1 ∘ I.eq_top_of_isUnit_mem h
  mpr e := e ▸ maximalIdeal.isMaximal R

Depends on / 依赖: I.eq_top_of_isUnit_mem, eq_of_le, eq_top_of_isUnit_mem, hI.eq_of_le, isMaximal, maximalIdeal, maximalIdeal.isMaximal
-/
theorem isMaximal_iff {I : Ideal R} : I.IsMaximal ↔ I = maximalIdeal R where
  mp hI := hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ h => hI.1.1 ∘ I.eq_top_of_isUnit_mem h
  mpr e := e ▸ maximalIdeal.isMaximal R

/--
theorem `maximal_ideal_unique` / 定理 `maximal_ideal_unique`

English:
theorem maximal_ideal_unique
  statement: exists! I : Ideal R, I.IsMaximal
  proof: by
  simp [isMaximal_iff]

中文:
定理 maximal_ideal_unique
  结论: 存在! I : 理想 R, I.是极大
  证明: by
  simp [isMaximal_iff]

Depends on / 依赖: isMaximal_iff
-/
theorem maximal_ideal_unique : exists! I : Ideal R, I.IsMaximal := by
  simp [isMaximal_iff]

variable {R}

/--
theorem `eq_maximalIdeal` / 定理 `eq_maximalIdeal`

English:
theorem eq_maximalIdeal
  given: {I : Ideal R} (hI : I.IsMaximal)
  statement: I = maximalIdeal R
  proof: ExistsUnique.unique (maximal_ideal_unique R) hI maximalIdeal.isMaximal R

中文:
定理 eq_maximalIdeal
  条件: {I : 理想 R} (hI : I.是极大)
  结论: I = maximalIdeal R
  证明: ExistsUnique.unique (maximal_ideal_unique R) hI maximalIdeal.isMaximal R

Depends on / 依赖: ExistsUnique, ExistsUnique.unique, isMaximal, maximalIdeal, maximalIdeal.isMaximal, maximal_ideal_unique, unique
-/
theorem eq_maximalIdeal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R :=
ExistsUnique.unique (maximal_ideal_unique R) hI maximalIdeal.isMaximal R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (MaximalSpectrum R)
  body: ⟨maximalIdeal R, maximalIdeal.isMaximal R⟩
uniq := fun I => MaximalSpectrum.ext_iff.mpr eq_maximalIdeal I.isMaximal

omit [IsLocalRing R] in

中文:
实例 :
  签名: 唯一 (极大谱 R)
  定义体: ⟨maximalIdeal R, maximalIdeal.isMaximal R⟩
uniq := fun I => MaximalSpectrum.ext_iff.mpr eq_maximalIdeal I.isMaximal

omit [IsLocalRing R] in

Depends on / 依赖: isMaximal, maximalIdeal, maximalIdeal.isMaximal
-/
instance : Unique (MaximalSpectrum R) where
  default := ⟨maximalIdeal R, maximalIdeal.isMaximal R⟩
uniq := fun I => MaximalSpectrum.ext_iff.mpr eq_maximalIdeal I.isMaximal

omit [IsLocalRing R] in
/--
theorem `of_singleton_maximalSpectrum` / 定理 `of_singleton_maximalSpectrum`

English:
theorem of_singleton_maximalSpectrum
  statement: [Subsingleton (MaximalSpectrum R)]
  proof: let m := Classical.arbitrary (MaximalSpectrum R)
  .of_unique_max_ideal ⟨m.asIdeal, m.isMaximal,
fun I hI => MaximalSpectrum.mk.inj Subsingleton.elim ⟨I, hI⟩ m⟩

中文:
定理 of_singleton_maximalSpectrum
  结论: [子单例 (极大谱 R)]
  证明: let m := Classical.arbitrary (MaximalSpectrum R)
  .of_unique_max_ideal ⟨m.asIdeal, m.isMaximal,
fun I hI => MaximalSpectrum.mk.inj Subsingleton.elim ⟨I, hI⟩ m⟩

Depends on / 依赖: Classical, Classical.arbitrary, MaximalSpectrum, MaximalSpectrum.mk.inj, Subsingleton, Subsingleton.elim, arbitrary, asIdeal, isMaximal, m.asIdeal, m.isMaximal, of_unique_max_ideal
-/
theorem of_singleton_maximalSpectrum [Subsingleton (MaximalSpectrum R)]
    [Nonempty (MaximalSpectrum R)] : IsLocalRing R :=
  let m := Classical.arbitrary (MaximalSpectrum R)
  .of_unique_max_ideal ⟨m.asIdeal, m.isMaximal,
fun I hI => MaximalSpectrum.mk.inj Subsingleton.elim ⟨I, hI⟩ m⟩

/--
theorem `le_maximalIdeal` / 定理 `le_maximalIdeal`

English:
theorem le_maximalIdeal
  given: {J : Ideal R} (hJ : J != ⊤)
  statement: J <= maximalIdeal R
  proof: by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]

中文:
定理 le_maximalIdeal
  条件: {J : 理想 R} (hJ : J != ⊤)
  结论: J <= maximalIdeal R
  证明: by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]

Depends on / 依赖: Ideal.exists_le_maximal, eq_maximalIdeal, exists_le_maximal
-/
theorem le_maximalIdeal {J : Ideal R} (hJ : J != ⊤) : J <= maximalIdeal R := by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]

/--
theorem `le_maximalIdeal_of_isPrime` / 定理 `le_maximalIdeal_of_isPrime`

English:
theorem le_maximalIdeal_of_isPrime
  given: (p : Ideal R) [hp : p.IsPrime]
  statement: p <= maximalIdeal R
  proof: le_maximalIdeal hp.ne_top

中文:
定理 le_maximalIdeal_of_isPrime
  条件: (p : 理想 R) [hp : p.是素]
  结论: p <= maximalIdeal R
  证明: le_maximalIdeal hp.ne_top

Depends on / 依赖: hp.ne_top, le_maximalIdeal, ne_top
-/
theorem le_maximalIdeal_of_isPrime (p : Ideal R) [hp : p.IsPrime] : p <= maximalIdeal R :=
  le_maximalIdeal hp.ne_top

/--
theorem `notMem_maximalIdeal` / 定理 `notMem_maximalIdeal`

English:
theorem notMem_maximalIdeal
  given: {x : R}
  statement: x ∉ maximalIdeal R ↔ IsUnit x
  proof: by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]

中文:
定理 notMem_maximalIdeal
  条件: {x : R}
  结论: x ∉ maximalIdeal R ↔ 是单位 x
  证明: by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]

Depends on / 依赖: mem_maximalIdeal, mem_nonunits_iff, not_not
-/
theorem notMem_maximalIdeal {x : R} : x ∉ maximalIdeal R ↔ IsUnit x := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]

/--
theorem `isField_iff_maximalIdeal_eq` / 定理 `isField_iff_maximalIdeal_eq`

English:
theorem isField_iff_maximalIdeal_eq
  statement: IsField R ↔ maximalIdeal R = ⊥
  proof: not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩

中文:
定理 isField_iff_maximalIdeal_eq
  结论: 是域 R ↔ maximalIdeal R = ⊥
  证明: not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩

Depends on / 依赖: Ideal.IsMaximal.isPrime, IsMaximal, Ring.ne_bot_of_isMaximal_of_not_isField, Ring.not_isField_iff_exists_prime.mpr, isPrime, ne_bot_of_isMaximal_of_not_isField, not_iff_not, not_iff_not.mp, not_isField_iff_exists_prime
-/
theorem isField_iff_maximalIdeal_eq : IsField R ↔ maximalIdeal R = ⊥ :=
  not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩

end CommSemiring

section CommRing

variable [CommRing R] [IsLocalRing R]

/--
theorem `maximalIdeal_le_jacobson` / 定理 `maximalIdeal_le_jacobson`

English:
theorem maximalIdeal_le_jacobson
  given: (I : Ideal R)
  proof: le_sInf fun _ ⟨_, h⟩ => le_of_eq (IsLocalRing.eq_maximalIdeal h).symm

中文:
定理 maximalIdeal_le_jacobson
  条件: (I : 理想 R)
  证明: le_sInf fun _ ⟨_, h⟩ => le_of_eq (IsLocalRing.eq_maximalIdeal h).symm

Depends on / 依赖: IsLocalRing, IsLocalRing.eq_maximalIdeal, eq_maximalIdeal, le_of_eq, le_sInf
-/
theorem maximalIdeal_le_jacobson (I : Ideal R) :
    IsLocalRing.maximalIdeal R <= I.jacobson :=
  le_sInf fun _ ⟨_, h⟩ => le_of_eq (IsLocalRing.eq_maximalIdeal h).symm

/--
theorem `jacobson_eq_maximalIdeal` / 定理 `jacobson_eq_maximalIdeal`

English:
theorem jacobson_eq_maximalIdeal
  given: (I : Ideal R) (h : I != ⊤)
  proof: le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)

中文:
定理 jacobson_eq_maximalIdeal
  条件: (I : 理想 R) (h : I != ⊤)
  证明: le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)

Depends on / 依赖: isMaximal, le_antisymm, le_maximalIdeal, maximalIdeal, maximalIdeal.isMaximal, maximalIdeal_le_jacobson, mul_comm, sInf_le
-/
theorem jacobson_eq_maximalIdeal (I : Ideal R) (h : I != ⊤) :
    I.jacobson = IsLocalRing.maximalIdeal R :=
  le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)

variable (R) in
/--
theorem `ringJacobson_eq_maximalIdeal` / 定理 `ringJacobson_eq_maximalIdeal`

English:
theorem ringJacobson_eq_maximalIdeal
  statement: Ring.jacobson R = maximalIdeal R
  proof: Ideal.jacobson_bot.symm.trans (jacobson_eq_maximalIdeal _ top_ne_bot.symm)

中文:
定理 ringJacobson_eq_maximalIdeal
  结论: 环.jacobson R = maximalIdeal R
  证明: Ideal.jacobson_bot.symm.trans (jacobson_eq_maximalIdeal _ top_ne_bot.symm)

Depends on / 依赖: Ideal.jacobson_bot.symm.trans, completeSpace_coe, isClosed_closure, isClosed_closure.completeSpace_coe, jacobson_bot, jacobson_eq_maximalIdeal, top_ne_bot, top_ne_bot.symm
-/
theorem ringJacobson_eq_maximalIdeal : Ring.jacobson R = maximalIdeal R :=
  Ideal.jacobson_bot.symm.trans (jacobson_eq_maximalIdeal _ top_ne_bot.symm)

end CommRing

section

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/--
theorem `ker_eq_maximalIdeal` / 定理 `ker_eq_maximalIdeal`

English:
theorem ker_eq_maximalIdeal
  given: [DivisionRing K] (φ : R ->+* K) (hφ : Function.Surjective φ)
  proof: IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ) hφ

中文:
定理 ker_eq_maximalIdeal
  条件: [除环 K] (φ : R ->+* K) (hφ : 函数.满射 φ)
  证明: IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ) hφ

Depends on / 依赖: IsLocalRing, IsLocalRing.eq_maximalIdeal, RingHom, RingHom.ker_isMaximal_of_surjective, eq_maximalIdeal, ker_isMaximal_of_surjective
-/
theorem ker_eq_maximalIdeal [DivisionRing K] (φ : R ->+* K) (hφ : Function.Surjective φ) :
    RingHom.ker φ = maximalIdeal R :=
IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ) hφ

end

/--
theorem `maximalIdeal_eq_bot` / 定理 `maximalIdeal_eq_bot`

English:
theorem maximalIdeal_eq_bot
  given: {R : Type*} [Field R]
  statement: IsLocalRing.maximalIdeal R = ⊥
  proof: IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)

中文:
定理 maximalIdeal_eq_bot
  条件: {R : 类型} [域 R]
  结论: 是局部环.maximalIdeal R = ⊥
  证明: IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)

Depends on / 依赖: Field.toIsField, IsLocalRing, IsLocalRing.isField_iff_maximalIdeal_eq.mp, isField_iff_maximalIdeal_eq, toIsField
-/
theorem maximalIdeal_eq_bot {R : Type*} [Field R] : IsLocalRing.maximalIdeal R = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)

end IsLocalRing

/--
lemma `Subsemiring.isLocalRing_of_unit` / 引理 `Subsemiring.isLocalRing_of_unit`

English:
lemma Subsemiring.isLocalRing_of_unit
  statement: {R : Type*} [Semiring R] [IsLocalRing R] (S : Subsemiring R)
  proof: (‹IsLocalRing R›.isUnit_or_isUnit_of_add_one congr(Subtype.val $hxy)).elim
      (fun hx => Or.inl (h_unit x.val x.prop hx)) (fun hy => Or.inr (h_unit y.val y.prop hy))

中文:
引理 子半环.isLocalRing_of_unit
  结论: {R : 类型} [半环 R] [是局部环 R] (S : 子半环 R)
  证明: (‹IsLocalRing R›.isUnit_or_isUnit_of_add_one congr(Subtype.val $hxy)).elim
      (fun hx => Or.inl (h_unit x.val x.prop hx)) (fun hy => Or.inr (h_unit y.val y.prop hy))

Depends on / 依赖: IsLocalRing, Or.inl, Or.inr, Subtype, Subtype.val, h_unit, isUnit_or_isUnit_of_add_one, x.prop, x.val, y.prop, y.val
-/
lemma Subsemiring.isLocalRing_of_unit {R : Type*} [Semiring R] [IsLocalRing R] (S : Subsemiring R)
    (h_unit : forall (x : R) (hx : x in S), IsUnit x -> IsUnit (⟨x, hx⟩ : S)) :
    IsLocalRing S where
  isUnit_or_isUnit_of_add_one {x y} hxy :=
    (‹IsLocalRing R›.isUnit_or_isUnit_of_add_one congr(Subtype.val $hxy)).elim
      (fun hx => Or.inl (h_unit x.val x.prop hx)) (fun hy => Or.inr (h_unit y.val y.prop hy))

/--
lemma `Subring.isLocalRing_of_unit` / 引理 `Subring.isLocalRing_of_unit`

English:
lemma Subring.isLocalRing_of_unit
  statement: {R : Type*} [Ring R] [IsLocalRing R] (S : Subring R)
  proof: S.toSubsemiring.isLocalRing_of_unit h_unit

中文:
引理 子环.isLocalRing_of_unit
  结论: {R : 类型} [环 R] [是局部环 R] (S : 子环 R)
  证明: S.toSubsemiring.isLocalRing_of_unit h_unit

Depends on / 依赖: S.toSubsemiring.isLocalRing_of_unit, h_unit, isLocalRing_of_unit, toSubsemiring
-/
lemma Subring.isLocalRing_of_unit {R : Type*} [Ring R] [IsLocalRing R] (S : Subring R)
    (h_unit : forall (x : R) (hx : x in S), IsUnit x -> IsUnit (⟨x, hx⟩ : S)) :
    IsLocalRing S :=
  S.toSubsemiring.isLocalRing_of_unit h_unit
