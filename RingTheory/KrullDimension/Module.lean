/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!

# Krull Dimension of Module

In this file we define `Module.supportDim R M` for an `R`-module `M` as
the krull dimension of its support. It is equal to the krull dimension of `R / Ann M` when
`M` is finitely generated.

-/

@[expose] public section

variable (R : Type*) [CommRing R]

variable (M : Type*) [AddCommGroup M] [Module R M] (N : Type*) [AddCommGroup N] [Module R N]

namespace Module

open Order

/--
Definition of `supportDim` / `supportDim` 的定义

English:
definition supportDim
  signature: : WithBot Nat∞
  body: krullDim (Module.support R M)

@[nontriviality]

中文:
定义 supportDim
  签名: : WithBot 自然数∞
  定义体: krullDim (Module.support R M)

@[nontriviality]

Depends on / 依赖: Module, Module.support, krullDim, support
-/
noncomputable def supportDim : WithBot Nat∞ :=
  krullDim (Module.support R M)

@[nontriviality]
/--
lemma `supportDim_eq_bot_of_subsingleton` / 引理 `supportDim_eq_bot_of_subsingleton`

English:
lemma supportDim_eq_bot_of_subsingleton
  given: [Subsingleton M]
  statement: supportDim R M = ⊥
  proof: by
  simpa [supportDim, support_eq_empty_iff]

中文:
引理 supportDim_eq_bot_of_subsingleton
  条件: [子单例 M]
  结论: supportDim R M = ⊥
  证明: by
  simpa [supportDim, support_eq_empty_iff]

Depends on / 依赖: supportDim, support_eq_empty_iff
-/
lemma supportDim_eq_bot_of_subsingleton [Subsingleton M] : supportDim R M = ⊥ := by
  simpa [supportDim, support_eq_empty_iff]

/--
lemma `supportDim_ne_bot_of_nontrivial` / 引理 `supportDim_ne_bot_of_nontrivial`

English:
lemma supportDim_ne_bot_of_nontrivial
  given: [Nontrivial M]
  statement: supportDim R M != ⊥
  proof: by
  have : Nonempty (Module.support R M) := nonempty_support_of_nontrivial.to_subtype
  simp [supportDim]

中文:
引理 supportDim_ne_bot_of_nontrivial
  条件: [非平凡 M]
  结论: supportDim R M != ⊥
  证明: by
  have : Nonempty (Module.support R M) := nonempty_support_of_nontrivial.to_subtype
  simp [supportDim]

Depends on / 依赖: Module, Module.support, Nonempty, nonempty_support_of_nontrivial, nonempty_support_of_nontrivial.to_subtype, support, supportDim, to_subtype
-/
lemma supportDim_ne_bot_of_nontrivial [Nontrivial M] : supportDim R M != ⊥ := by
  have : Nonempty (Module.support R M) := nonempty_support_of_nontrivial.to_subtype
  simp [supportDim]

/--
lemma `supportDim_eq_bot_iff_subsingleton` / 引理 `supportDim_eq_bot_iff_subsingleton`

English:
lemma supportDim_eq_bot_iff_subsingleton
  statement: supportDim R M = ⊥ ↔ Subsingleton M
  proof: by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff]

中文:
引理 supportDim_eq_bot_iff_subsingleton
  结论: supportDim R M = ⊥ ↔ 子单例 M
  证明: by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff]

Depends on / 依赖: krullDim_eq_bot_iff, supportDim, support_eq_empty_iff
-/
lemma supportDim_eq_bot_iff_subsingleton : supportDim R M = ⊥ ↔ Subsingleton M := by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff]

/--
lemma `supportDim_ne_bot_iff_nontrivial` / 引理 `supportDim_ne_bot_iff_nontrivial`

English:
lemma supportDim_ne_bot_iff_nontrivial
  statement: supportDim R M != ⊥ ↔ Nontrivial M
  proof: by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff, not_subsingleton_iff_nontrivial]

中文:
引理 supportDim_ne_bot_iff_nontrivial
  结论: supportDim R M != ⊥ ↔ 非平凡 M
  证明: by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff, not_subsingleton_iff_nontrivial]

Depends on / 依赖: krullDim_eq_bot_iff, not_subsingleton_iff_nontrivial, supportDim, support_eq_empty_iff
-/
lemma supportDim_ne_bot_iff_nontrivial : supportDim R M != ⊥ ↔ Nontrivial M := by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff, not_subsingleton_iff_nontrivial]

/--
lemma `supportDim_eq_ringKrullDim_quotient_annihilator` / 引理 `supportDim_eq_ringKrullDim_quotient_annihilator`

English:
lemma supportDim_eq_ringKrullDim_quotient_annihilator
  given: [Module.Finite R M]
  proof: by
  simp only [supportDim]
  rw [support_eq_zeroLocus]; rw [ringKrullDim_quotient]

中文:
引理 supportDim_eq_ringKrullDim_quotient_annihilator
  条件: [模.有限 R M]
  证明: by
  simp only [supportDim]
  rw [support_eq_zeroLocus]; rw [ringKrullDim_quotient]

Depends on / 依赖: ringKrullDim_quotient, supportDim, support_eq_zeroLocus
-/
lemma supportDim_eq_ringKrullDim_quotient_annihilator [Module.Finite R M] :
    supportDim R M = ringKrullDim (R ⧸ annihilator R M) := by
  simp only [supportDim]
  rw [support_eq_zeroLocus]; rw [ringKrullDim_quotient]

/--
lemma `supportDim_self_eq_ringKrullDim` / 引理 `supportDim_self_eq_ringKrullDim`

English:
lemma supportDim_self_eq_ringKrullDim
  statement: supportDim R R = ringKrullDim R
  proof: by
  have : annihilator R R = ⊥ :=
    annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {a₁ a₂} a => a)
  rw [supportDim_eq_ringKrullDim_quotient_annihilator]; rw [this]
  exact (RingEquiv.ringKrullDim (RingEquiv.quotientBot R))

中文:
引理 supportDim_self_eq_ringKrullDim
  结论: supportDim R R = ringKrullDim R
  证明: by
  have : annihilator R R = ⊥ :=
    annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {a₁ a₂} a => a)
  rw [supportDim_eq_ringKrullDim_quotient_annihilator]; rw [this]
  exact (RingEquiv.ringKrullDim (RingEquiv.quotientBot R))

Depends on / 依赖: RingEquiv, RingEquiv.quotientBot, RingEquiv.ringKrullDim, annihilator, annihilator_eq_bot, annihilator_eq_bot.mpr, faithfulSMul_iff_algebraMap_injective, quotientBot, ringKrullDim, supportDim_eq_ringKrullDim_quotient_annihilator
-/
lemma supportDim_self_eq_ringKrullDim : supportDim R R = ringKrullDim R := by
  have : annihilator R R = ⊥ :=
    annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {a₁ a₂} a => a)
  rw [supportDim_eq_ringKrullDim_quotient_annihilator]; rw [this]
  exact (RingEquiv.ringKrullDim (RingEquiv.quotientBot R))

/--
lemma `supportDim_le_ringKrullDim` / 引理 `supportDim_le_ringKrullDim`

English:
lemma supportDim_le_ringKrullDim
  statement: supportDim R M <= ringKrullDim R
  proof: krullDim_le_of_strictMono (fun a => a) fun {_ _} lt => lt

中文:
引理 supportDim_le_ringKrullDim
  结论: supportDim R M <= ringKrullDim R
  证明: krullDim_le_of_strictMono (fun a => a) fun {_ _} lt => lt

Depends on / 依赖: krullDim_le_of_strictMono
-/
lemma supportDim_le_ringKrullDim : supportDim R M <= ringKrullDim R :=
  krullDim_le_of_strictMono (fun a => a) fun {_ _} lt => lt

variable {R M N}

/--
lemma `supportDim_quotient_eq_ringKrullDim` / 引理 `supportDim_quotient_eq_ringKrullDim`

English:
lemma supportDim_quotient_eq_ringKrullDim
  given: (I : Ideal R)
  proof: by
  rw [supportDim_eq_ringKrullDim_quotient_annihilator]; rw [Ideal.annihilator_quotient]

中文:
引理 supportDim_quotient_eq_ringKrullDim
  条件: (I : 理想 R)
  证明: by
  rw [supportDim_eq_ringKrullDim_quotient_annihilator]; rw [Ideal.annihilator_quotient]

Depends on / 依赖: Ideal.annihilator_quotient, annihilator_quotient, supportDim_eq_ringKrullDim_quotient_annihilator
-/
lemma supportDim_quotient_eq_ringKrullDim (I : Ideal R) :
    supportDim R (R ⧸ I) = ringKrullDim (R ⧸ I) := by
  rw [supportDim_eq_ringKrullDim_quotient_annihilator]; rw [Ideal.annihilator_quotient]

/--
lemma `supportDim_le_of_injective` / 引理 `supportDim_le_of_injective`

English:
lemma supportDim_le_of_injective
  given: (f : M ->ₗ[R] N) (h : Function.Injective f)
  proof: krullDim_le_of_strictMono (fun a => ⟨a.1, Module.support_subset_of_injective f h a.2⟩)
    (fun {_ _} lt => lt)

中文:
引理 supportDim_le_of_injective
  条件: (f : M ->ₗ[R] N) (h : 函数.单射 f)
  证明: krullDim_le_of_strictMono (fun a => ⟨a.1, Module.support_subset_of_injective f h a.2⟩)
    (fun {_ _} lt => lt)

Depends on / 依赖: Module, Module.support_subset_of_injective, krullDim_le_of_strictMono, support_subset_of_injective
-/
lemma supportDim_le_of_injective (f : M ->ₗ[R] N) (h : Function.Injective f) :
    supportDim R M <= supportDim R N :=
  krullDim_le_of_strictMono (fun a => ⟨a.1, Module.support_subset_of_injective f h a.2⟩)
    (fun {_ _} lt => lt)

/--
lemma `supportDim_le_of_surjective` / 引理 `supportDim_le_of_surjective`

English:
lemma supportDim_le_of_surjective
  given: (f : M ->ₗ[R] N) (h : Function.Surjective f)
  proof: krullDim_le_of_strictMono (fun a => ⟨a.1, Module.support_subset_of_surjective f h a.2⟩)
    (fun {_ _} lt => lt)

中文:
引理 supportDim_le_of_surjective
  条件: (f : M ->ₗ[R] N) (h : 函数.满射 f)
  证明: krullDim_le_of_strictMono (fun a => ⟨a.1, Module.support_subset_of_surjective f h a.2⟩)
    (fun {_ _} lt => lt)

Depends on / 依赖: Module, Module.support_subset_of_surjective, krullDim_le_of_strictMono, support_subset_of_surjective
-/
lemma supportDim_le_of_surjective (f : M ->ₗ[R] N) (h : Function.Surjective f) :
    supportDim R N <= supportDim R M :=
  krullDim_le_of_strictMono (fun a => ⟨a.1, Module.support_subset_of_surjective f h a.2⟩)
    (fun {_ _} lt => lt)

/--
lemma `supportDim_eq_of_equiv` / 引理 `supportDim_eq_of_equiv`

English:
lemma supportDim_eq_of_equiv
  given: (e : M ≃ₗ[R] N)
  proof: le_antisymm (supportDim_le_of_injective e e.injective)
    (supportDim_le_of_surjective e e.surjective)

中文:
引理 supportDim_eq_of_equiv
  条件: (e : M ≃ₗ[R] N)
  证明: le_antisymm (supportDim_le_of_injective e e.injective)
    (supportDim_le_of_surjective e e.surjective)

Depends on / 依赖: e.injective, e.surjective, injective, le_antisymm, supportDim_le_of_injective, supportDim_le_of_surjective, surjective
-/
lemma supportDim_eq_of_equiv (e : M ≃ₗ[R] N) :
    supportDim R M = supportDim R N :=
  le_antisymm (supportDim_le_of_injective e e.injective)
    (supportDim_le_of_surjective e e.surjective)

end Module

open Ideal IsLocalRing

/--
lemma `support_of_supportDim_eq_zero` / 引理 `support_of_supportDim_eq_zero`

English:
lemma support_of_supportDim_eq_zero
  statement: [IsLocalRing R]
  proof: by
  let _ : Nontrivial N := by simp [← Module.supportDim_ne_bot_iff_nontrivial R, dim]
  rw [PrimeSpectrum.zeroLocus_eq_singleton]
  apply le_antisymm
  · intro p hp
    by_contra nmem
    push _ in _ at nmem
    have : p < ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal IsPrime.ne_top') nmem
    have : Module.supportDim R N > 0 := by
      simp only [Module.supportDim, gt_iff_lt, Order.krullDim_pos_iff, Subtype.exists,
        Subtype.mk_lt_mk, exists_prop]
      use p
      simpa [hp] using! ⟨_, IsLocalRing.closedPoint_mem_support R N, this⟩
    exact (ne_of_lt this) dim.symm
  · simpa using! IsLocalRing.closedPoint_mem_support R N

中文:
引理 support_of_supportDim_eq_zero
  结论: [是局部环 R]
  证明: by
  let _ : Nontrivial N := by simp [← Module.supportDim_ne_bot_iff_nontrivial R, dim]
  rw [PrimeSpectrum.zeroLocus_eq_singleton]
  apply le_antisymm
  · intro p hp
    by_contra nmem
    push _ in _ at nmem
    have : p < ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal IsPrime.ne_top') nmem
    have : Module.supportDim R N > 0 := by
      simp only [Module.supportDim, gt_iff_lt, Order.krullDim_pos_iff, Subtype.exists,
        Subtype.mk_lt_mk, exists_prop]
      use p
      simpa [hp] using! ⟨_, IsLocalRing.closedPoint_mem_support R N, this⟩
    exact (ne_of_lt this) dim.symm
  · simpa using! IsLocalRing.closedPoint_mem_support R N

Depends on / 依赖: IsLocalRing, IsLocalRing.le_maximalIdeal, IsMaximal, IsMaximal.isPrime, IsPrime, IsPrime.ne_top, Module, Module.supportDim, Module.supportDim_ne_bot_iff_nontrivial, Nontrivial, Order.krullDim_pos_iff, PrimeSpectrum, PrimeSpectrum.zeroLocus_eq_singleton, Subtype, Subtype.exists, Subtype.mk_lt_mk, exists_prop, gt_iff_lt, isPrime, krullDim_pos_iff
-/
lemma support_of_supportDim_eq_zero [IsLocalRing R]
    (dim : Module.supportDim R N = 0) :
    Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  let _ : Nontrivial N := by simp [← Module.supportDim_ne_bot_iff_nontrivial R, dim]
  rw [PrimeSpectrum.zeroLocus_eq_singleton]
  apply le_antisymm
  · intro p hp
    by_contra nmem
    push _ in _ at nmem
    have : p < ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal IsPrime.ne_top') nmem
    have : Module.supportDim R N > 0 := by
      simp only [Module.supportDim, gt_iff_lt, Order.krullDim_pos_iff, Subtype.exists,
        Subtype.mk_lt_mk, exists_prop]
      use p
      simpa [hp] using! ⟨_, IsLocalRing.closedPoint_mem_support R N, this⟩
    exact (ne_of_lt this) dim.symm
  · simpa using! IsLocalRing.closedPoint_mem_support R N
