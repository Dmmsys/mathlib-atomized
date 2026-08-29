/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Nullstellensatz

This file establishes a version of Hilbert's classical Nullstellensatz for `MvPolynomial`s.
The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.

The statement is in terms of new definitions `vanishingIdeal` and `zeroLocus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishingIdeal` and `zeroLocus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/

@[expose] public section

open Ideal

noncomputable section

namespace MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*}

variable (K) in
/--
Definition of `zeroLocus` / `zeroLocus` 的定义

English:
definition zeroLocus
  signature: (I : Ideal (MvPolynomial σ k))
  body: {x : σ -> K | forall p in I, aeval x p = 0}

@[simp]

中文:
定义 zeroLocus
  签名: (I : 理想 (多元多项式 σ k))
  定义体: {x : σ -> K | forall p in I, aeval x p = 0}

@[simp]
-/
def zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ -> K) :=
  {x : σ -> K | forall p in I, aeval x p = 0}

@[simp]
/--
theorem `mem_zeroLocus_iff` / 定理 `mem_zeroLocus_iff`

English:
theorem mem_zeroLocus_iff
  given: {I : Ideal (MvPolynomial σ k)} {x : σ -> K}
  proof: Iff.rfl

中文:
定理 mem_zeroLocus_iff
  条件: {I : 理想 (多元多项式 σ k)} {x : σ -> K}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_zeroLocus_iff {I : Ideal (MvPolynomial σ k)} {x : σ -> K} :
    x in zeroLocus K I ↔ forall p in I, aeval x p = 0 :=
  Iff.rfl

/--
theorem `zeroLocus_anti_mono` / 定理 `zeroLocus_anti_mono`

English:
theorem zeroLocus_anti_mono
  given: {I J : Ideal (MvPolynomial σ k)} (h : I <= J)
  proof: fun _ hx p hp => hx p h hp

@[simp]

中文:
定理 zeroLocus_anti_mono
  条件: {I J : 理想 (多元多项式 σ k)} (h : I <= J)
  证明: fun _ hx p hp => hx p h hp

@[simp]
-/
theorem zeroLocus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I <= J) :
zeroLocus K J <= zeroLocus K I := fun _ hx p hp => hx p h hp

@[simp]
/--
theorem `zeroLocus_bot` / 定理 `zeroLocus_bot`

English:
theorem zeroLocus_bot
  statement: zeroLocus K (⊥ : Ideal (MvPolynomial σ k)) = ⊤
  proof: eq_top_iff.2 fun x _ _ hp => Trans.trans (congr_arg (aeval x) (mem_bot.1 hp)) (eval x).map_zero

@[simp]

中文:
定理 zeroLocus_bot
  结论: zeroLocus K (⊥ : 理想 (多元多项式 σ k)) = ⊤
  证明: eq_top_iff.2 fun x _ _ hp => Trans.trans (congr_arg (aeval x) (mem_bot.1 hp)) (eval x).map_zero

@[simp]

Depends on / 依赖: Trans.trans, congr_arg, eq_top_iff, map_zero, mem_bot
-/
theorem zeroLocus_bot : zeroLocus K (⊥ : Ideal (MvPolynomial σ k)) = ⊤ :=
  eq_top_iff.2 fun x _ _ hp => Trans.trans (congr_arg (aeval x) (mem_bot.1 hp)) (eval x).map_zero

@[simp]
/--
theorem `zeroLocus_top` / 定理 `zeroLocus_top`

English:
theorem zeroLocus_top
  statement: zeroLocus K (⊤ : Ideal (MvPolynomial σ k)) = ⊥
  proof: eq_bot_iff.2 fun x hx => one_ne_zero
    ((aeval (R := k) x).map_one ▸ hx 1 Submodule.mem_top : (1 : K) = 0)

中文:
定理 zeroLocus_top
  结论: zeroLocus K (⊤ : 理想 (多元多项式 σ k)) = ⊥
  证明: eq_bot_iff.2 fun x hx => one_ne_zero
    ((aeval (R := k) x).map_one ▸ hx 1 Submodule.mem_top : (1 : K) = 0)

Depends on / 依赖: Submodule, Submodule.mem_top, eq_bot_iff, map_one, mem_top, one_ne_zero
-/
theorem zeroLocus_top : zeroLocus K (⊤ : Ideal (MvPolynomial σ k)) = ⊥ :=
  eq_bot_iff.2 fun x hx => one_ne_zero
    ((aeval (R := k) x).map_one ▸ hx 1 Submodule.mem_top : (1 : K) = 0)

variable (k) in
/--
Definition of `vanishingIdeal` / `vanishingIdeal` 的定义

English:
definition vanishingIdeal
  signature: (V : Set (σ -> K))
  body: {p | forall x in V, aeval x p = 0}
  zero_mem' _ _ := map_zero _
  add_mem' {p q} hp hq x hx := by simp only [hq x hx, hp x hx, add_zero, map_add]
  smul_mem' p q hq x hx := by
    simp only [hq x hx, smul_eq_mul, mul_zero, map_mul]

@[simp]

中文:
定义 vanishingIdeal
  签名: (V : 集合 (σ -> K))
  定义体: {p | forall x in V, aeval x p = 0}
  zero_mem' _ _ := map_zero _
  add_mem' {p q} hp hq x hx := by simp only [hq x hx, hp x hx, add_zero, map_add]
  smul_mem' p q hq x hx := by
    simp only [hq x hx, smul_eq_mul, mul_zero, map_mul]

@[simp]
-/
def vanishingIdeal (V : Set (σ -> K)) : Ideal (MvPolynomial σ k) where
  carrier := {p | forall x in V, aeval x p = 0}
  zero_mem' _ _ := map_zero _
  add_mem' {p q} hp hq x hx := by simp only [hq x hx, hp x hx, add_zero, map_add]
  smul_mem' p q hq x hx := by
    simp only [hq x hx, smul_eq_mul, mul_zero, map_mul]

@[simp]
/--
theorem `mem_vanishingIdeal_iff` / 定理 `mem_vanishingIdeal_iff`

English:
theorem mem_vanishingIdeal_iff
  given: {V : Set (σ -> K)} {p : MvPolynomial σ k}
  proof: Iff.rfl

中文:
定理 mem_vanishingIdeal_iff
  条件: {V : 集合 (σ -> K)} {p : 多元多项式 σ k}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_vanishingIdeal_iff {V : Set (σ -> K)} {p : MvPolynomial σ k} :
    p in vanishingIdeal k V ↔ forall x in V, aeval x p = 0 :=
  Iff.rfl

/--
theorem `vanishingIdeal_anti_mono` / 定理 `vanishingIdeal_anti_mono`

English:
theorem vanishingIdeal_anti_mono
  given: {A B : Set (σ -> K)} (h : A <= B)
  proof: fun _ hp x hx => hp x h hx

中文:
定理 vanishingIdeal_anti_mono
  条件: {A B : 集合 (σ -> K)} (h : A <= B)
  证明: fun _ hp x hx => hp x h hx
-/
theorem vanishingIdeal_anti_mono {A B : Set (σ -> K)} (h : A <= B) :
vanishingIdeal k B <= vanishingIdeal k A := fun _ hp x hx => hp x h hx

/--
theorem `vanishingIdeal_empty` / 定理 `vanishingIdeal_empty`

English:
theorem vanishingIdeal_empty
  statement: vanishingIdeal k (∅ : Set (σ -> K)) = ⊤
  proof: le_antisymm le_top fun _ _ x hx => absurd hx (Set.notMem_empty x)

中文:
定理 vanishingIdeal_empty
  结论: vanishingIdeal k (∅ : 集合 (σ -> K)) = ⊤
  证明: le_antisymm le_top fun _ _ x hx => absurd hx (Set.notMem_empty x)

Depends on / 依赖: Set.notMem_empty, absurd, le_antisymm, le_top, notMem_empty
-/
theorem vanishingIdeal_empty : vanishingIdeal k (∅ : Set (σ -> K)) = ⊤ :=
  le_antisymm le_top fun _ _ x hx => absurd hx (Set.notMem_empty x)

/--
theorem `le_vanishingIdeal_zeroLocus` / 定理 `le_vanishingIdeal_zeroLocus`

English:
theorem le_vanishingIdeal_zeroLocus
  given: (I : Ideal (MvPolynomial σ k))
  proof: fun p hp _ hx => hx p hp

中文:
定理 le_vanishingIdeal_zeroLocus
  条件: (I : 理想 (多元多项式 σ k))
  证明: fun p hp _ hx => hx p hp
-/
theorem le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I <= vanishingIdeal k (zeroLocus K I) := fun p hp _ hx => hx p hp

/--
theorem `zeroLocus_vanishingIdeal_le` / 定理 `zeroLocus_vanishingIdeal_le`

English:
theorem zeroLocus_vanishingIdeal_le
  given: (V : Set (σ -> K))
  statement: V <= zeroLocus K (vanishingIdeal k V)
  proof: fun V hV _ hp => hp V hV

中文:
定理 zeroLocus_vanishingIdeal_le
  条件: (V : 集合 (σ -> K))
  结论: V <= zeroLocus K (vanishingIdeal k V)
  证明: fun V hV _ hp => hp V hV
-/
theorem zeroLocus_vanishingIdeal_le (V : Set (σ -> K)) : V <= zeroLocus K (vanishingIdeal k V) :=
  fun V hV _ hp => hp V hV

/--
theorem `zeroLocus_vanishingIdeal_galoisConnection` / 定理 `zeroLocus_vanishingIdeal_galoisConnection`

English:
theorem zeroLocus_vanishingIdeal_galoisConnection
  proof: GaloisConnection.monotone_intro (fun _ _ => vanishingIdeal_anti_mono)
    (fun _ _ => zeroLocus_anti_mono) le_vanishingIdeal_zeroLocus zeroLocus_vanishingIdeal_le

中文:
定理 zeroLocus_vanishingIdeal_galoisConnection
  证明: GaloisConnection.monotone_intro (fun _ _ => vanishingIdeal_anti_mono)
    (fun _ _ => zeroLocus_anti_mono) le_vanishingIdeal_zeroLocus zeroLocus_vanishingIdeal_le

Depends on / 依赖: GaloisConnection, GaloisConnection.monotone_intro, le_vanishingIdeal_zeroLocus, monotone_intro, vanishingIdeal_anti_mono, zeroLocus_anti_mono, zeroLocus_vanishingIdeal_le
-/
theorem zeroLocus_vanishingIdeal_galoisConnection :
    @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ -> K))ᵒᵈ _ _
      (zeroLocus K) (vanishingIdeal k) :=
  GaloisConnection.monotone_intro (fun _ _ => vanishingIdeal_anti_mono)
    (fun _ _ => zeroLocus_anti_mono) le_vanishingIdeal_zeroLocus zeroLocus_vanishingIdeal_le

/--
theorem `le_zeroLocus_iff_le_vanishingIdeal` / 定理 `le_zeroLocus_iff_le_vanishingIdeal`

English:
theorem le_zeroLocus_iff_le_vanishingIdeal
  given: {V : Set (σ -> K)} {I : Ideal (MvPolynomial σ k)}
  proof: zeroLocus_vanishingIdeal_galoisConnection.le_iff_le

中文:
定理 le_zeroLocus_iff_le_vanishingIdeal
  条件: {V : 集合 (σ -> K)} {I : 理想 (多元多项式 σ k)}
  证明: zeroLocus_vanishingIdeal_galoisConnection.le_iff_le

Depends on / 依赖: le_iff_le, zeroLocus_vanishingIdeal_galoisConnection, zeroLocus_vanishingIdeal_galoisConnection.le_iff_le
-/
theorem le_zeroLocus_iff_le_vanishingIdeal {V : Set (σ -> K)} {I : Ideal (MvPolynomial σ k)} :
    V <= zeroLocus K I ↔ I <= vanishingIdeal k V :=
  zeroLocus_vanishingIdeal_galoisConnection.le_iff_le

/--
theorem `zeroLocus_span` / 定理 `zeroLocus_span`

English:
theorem zeroLocus_span
  given: (S : Set (MvPolynomial σ k))
  proof: eq_of_forall_le_iff fun _ => le_zeroLocus_iff_le_vanishingIdeal.trans
    Ideal.span_le.trans forall₂_comm

中文:
定理 zeroLocus_span
  条件: (S : 集合 (多元多项式 σ k))
  证明: eq_of_forall_le_iff fun _ => le_zeroLocus_iff_le_vanishingIdeal.trans
    Ideal.span_le.trans forall₂_comm

Depends on / 依赖: Ideal.span_le.trans, eq_of_forall_le_iff, le_zeroLocus_iff_le_vanishingIdeal, le_zeroLocus_iff_le_vanishingIdeal.trans, span_le
-/
theorem zeroLocus_span (S : Set (MvPolynomial σ k)) :
    zeroLocus K (Ideal.span S) = { x | forall p in S, aeval x p = 0 } :=
eq_of_forall_le_iff fun _ => le_zeroLocus_iff_le_vanishingIdeal.trans
    Ideal.span_le.trans forall₂_comm

/--
theorem `mem_vanishingIdeal_singleton_iff` / 定理 `mem_vanishingIdeal_singleton_iff`

English:
theorem mem_vanishingIdeal_singleton_iff
  given: (x : σ -> K) (p : MvPolynomial σ k)
  proof: ⟨fun h => h x rfl, fun hpx _ hy => hy.symm ▸ hpx⟩

中文:
定理 mem_vanishingIdeal_singleton_iff
  条件: (x : σ -> K) (p : 多元多项式 σ k)
  证明: ⟨fun h => h x rfl, fun hpx _ hy => hy.symm ▸ hpx⟩

Depends on / 依赖: hy.symm
-/
theorem mem_vanishingIdeal_singleton_iff (x : σ -> K) (p : MvPolynomial σ k) :
    p in (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) ↔ aeval x p = 0 :=
  ⟨fun h => h x rfl, fun hpx _ hy => hy.symm ▸ hpx⟩

instance {x : σ -> K} : (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)).IsPrime := by
  convert! RingHom.ker_isPrime (aeval (R := k) x)
  ext; simp

instance {x : σ -> K} : (vanishingIdeal K {x} : Ideal (MvPolynomial σ K)).IsMaximal := by
  convert! RingHom.ker_isMaximal_of_surjective (aeval (R := K) x) ?_
  · ext; simp
  · intro z; use C z; simp

/--
theorem `radical_le_vanishingIdeal_zeroLocus` / 定理 `radical_le_vanishingIdeal_zeroLocus`

English:
theorem radical_le_vanishingIdeal_zeroLocus
  given: (I : Ideal (MvPolynomial σ k))
  proof: by
  intro p hp x hx
  rw [← mem_vanishingIdeal_singleton_iff]
  rw [radical_eq_sInf] at hp
  refine
    (mem_sInf.mp hp)
      ⟨le_trans (le_vanishingIdeal_zeroLocus I)
          (vanishingIdeal_anti_mono fun y hy => hy.symm ▸ hx),
        inferInstance⟩

中文:
定理 radical_le_vanishingIdeal_zeroLocus
  条件: (I : 理想 (多元多项式 σ k))
  证明: by
  intro p hp x hx
  rw [← mem_vanishingIdeal_singleton_iff]
  rw [radical_eq_sInf] at hp
  refine
    (mem_sInf.mp hp)
      ⟨le_trans (le_vanishingIdeal_zeroLocus I)
          (vanishingIdeal_anti_mono fun y hy => hy.symm ▸ hx),
        inferInstance⟩

Depends on / 依赖: hy.symm, le_trans, le_vanishingIdeal_zeroLocus, mem_sInf, mem_sInf.mp, mem_vanishingIdeal_singleton_iff, radical_eq_sInf, vanishingIdeal_anti_mono
-/
theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I.radical <= vanishingIdeal k (zeroLocus K I) := by
  intro p hp x hx
  rw [← mem_vanishingIdeal_singleton_iff]
  rw [radical_eq_sInf] at hp
  refine
    (mem_sInf.mp hp)
      ⟨le_trans (le_vanishingIdeal_zeroLocus I)
          (vanishingIdeal_anti_mono fun y hy => hy.symm ▸ hx),
        inferInstance⟩

/--
Definition of `pointToPoint` / `pointToPoint` 的定义

English:
definition pointToPoint
  signature: (x : σ -> K)
  body: ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩

@[simp]

中文:
定义 pointToPoint
  签名: (x : σ -> K)
  定义体: ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩

@[simp]

Depends on / 依赖: MvPolynomial, infer_instance, vanishingIdeal
-/
def pointToPoint (x : σ -> K) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩

@[simp]
/--
theorem `vanishingIdeal_pointToPoint` / 定理 `vanishingIdeal_pointToPoint`

English:
theorem vanishingIdeal_pointToPoint
  given: (V : Set (σ -> K))
  proof: le_antisymm
    (fun _ hp x hx =>
      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
        (⟨x, hx, rfl⟩ : _))
        x rfl)
    fun _ hp =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun _ hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun _ hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1

中文:
定理 vanishingIdeal_pointToPoint
  条件: (V : 集合 (σ -> K))
  证明: le_antisymm
    (fun _ hp x hx =>
      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
        (⟨x, hx, rfl⟩ : _))
        x rfl)
    fun _ hp =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun _ hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun _ hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.mem_vanishingIdeal, Set.mem_singleton_iff, infer_instance, le_antisymm, mem_singleton_iff, mem_vanishingIdeal, vanishingIdeal
-/
theorem vanishingIdeal_pointToPoint (V : Set (σ -> K)) :
    PrimeSpectrum.vanishingIdeal (pointToPoint '' V) = MvPolynomial.vanishingIdeal k V :=
  le_antisymm
    (fun _ hp x hx =>
      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
        (⟨x, hx, rfl⟩ : _))
        x rfl)
    fun _ hp =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun _ hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun _ hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1

/--
theorem `pointToPoint_zeroLocus_le` / 定理 `pointToPoint_zeroLocus_le`

English:
theorem pointToPoint_zeroLocus_le
  given: (I : Ideal (MvPolynomial σ K))
  proof: fun J hJ =>
  let ⟨_, hx⟩ := hJ
  (le_trans (le_vanishingIdeal_zeroLocus (K := K) I)
      (hx.2 ▸ vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I <= J.asIdeal)

中文:
定理 pointToPoint_zeroLocus_le
  条件: (I : 理想 (多元多项式 σ K))
  证明: fun J hJ =>
  let ⟨_, hx⟩ := hJ
  (le_trans (le_vanishingIdeal_zeroLocus (K := K) I)
      (hx.2 ▸ vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I <= J.asIdeal)

Depends on / 依赖: MvPolynomial, MvPolynomial.zeroLocus, PrimeSpectrum, PrimeSpectrum.zeroLocus, zeroLocus
-/
theorem pointToPoint_zeroLocus_le (I : Ideal (MvPolynomial σ K)) :
    pointToPoint (k := K) '' MvPolynomial.zeroLocus K I <= PrimeSpectrum.zeroLocus I := fun J hJ =>
  let ⟨_, hx⟩ := hJ
  (le_trans (le_vanishingIdeal_zeroLocus (K := K) I)
      (hx.2 ▸ vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I <= J.asIdeal)

variable [IsAlgClosed K] [Finite σ]

variable (K) in
/--
theorem `eq_vanishingIdeal_singleton_of_isMaximal` / 定理 `eq_vanishingIdeal_singleton_of_isMaximal`

English:
theorem eq_vanishingIdeal_singleton_of_isMaximal
  given: {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal)
  proof: by
  let : Field (MvPolynomial σ k ⧸ I) := Quotient.field I
  have : Algebra.IsAlgebraic k (MvPolynomial σ k ⧸ I) := by
    rw [Algebra.isAlgebraic_iff_isIntegral]; rw [← algebraMap_isIntegral_iff]
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : (MvPolynomial σ k ⧸ I) ->ₐ[k] K := IsAlgClosed.lift
  let x : σ -> K := fun s => φ (Ideal.Quotient.mk I (X s))
  have : aeval x = φ.comp (Quotient.mkₐ k I) := by ext; simp [x]
  use x
  simp [Ideal.ext_iff, this, Ideal.Quotient.eq_zero_iff_mem]

中文:
定理 eq_vanishingIdeal_singleton_of_isMaximal
  条件: {I : 理想 (多元多项式 σ k)} (hI : I.是极大)
  证明: by
  let : Field (MvPolynomial σ k ⧸ I) := Quotient.field I
  have : Algebra.IsAlgebraic k (MvPolynomial σ k ⧸ I) := by
    rw [Algebra.isAlgebraic_iff_isIntegral]; rw [← algebraMap_isIntegral_iff]
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : (MvPolynomial σ k ⧸ I) ->ₐ[k] K := IsAlgClosed.lift
  let x : σ -> K := fun s => φ (Ideal.Quotient.mk I (X s))
  have : aeval x = φ.comp (Quotient.mkₐ k I) := by ext; simp [x]
  use x
  simp [Ideal.ext_iff, this, Ideal.Quotient.eq_zero_iff_mem]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.isAlgebraic_iff_isIntegral, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, IsAlgClosed, IsAlgClosed.lift, IsAlgebraic, MvPolynomial, MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing, Quotient, Quotient.field, Quotient.mk, algebraMap_isIntegral_iff, comp_C_integral_of_surjective_of_isJacobsonRing, isAlgebraic_iff_isIntegral, mk_surjective
-/
theorem eq_vanishingIdeal_singleton_of_isMaximal {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal) :
    exists x : σ -> K, I = vanishingIdeal k {x} := by
  let : Field (MvPolynomial σ k ⧸ I) := Quotient.field I
  have : Algebra.IsAlgebraic k (MvPolynomial σ k ⧸ I) := by
    rw [Algebra.isAlgebraic_iff_isIntegral]; rw [← algebraMap_isIntegral_iff]
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : (MvPolynomial σ k ⧸ I) ->ₐ[k] K := IsAlgClosed.lift
  let x : σ -> K := fun s => φ (Ideal.Quotient.mk I (X s))
  have : aeval x = φ.comp (Quotient.mkₐ k I) := by ext; simp [x]
  use x
  simp [Ideal.ext_iff, this, Ideal.Quotient.eq_zero_iff_mem]

/--
theorem `isMaximal_iff_eq_vanishingIdeal_singleton` / 定理 `isMaximal_iff_eq_vanishingIdeal_singleton`

English:
theorem isMaximal_iff_eq_vanishingIdeal_singleton
  given: {I : Ideal (MvPolynomial σ K)}
  proof: ⟨eq_vanishingIdeal_singleton_of_isMaximal K,
    fun ⟨_, hx⟩ => hx ▸ inferInstance⟩

中文:
定理 isMaximal_iff_eq_vanishingIdeal_singleton
  条件: {I : 理想 (多元多项式 σ K)}
  证明: ⟨eq_vanishingIdeal_singleton_of_isMaximal K,
    fun ⟨_, hx⟩ => hx ▸ inferInstance⟩

Depends on / 依赖: eq_vanishingIdeal_singleton_of_isMaximal
-/
theorem isMaximal_iff_eq_vanishingIdeal_singleton {I : Ideal (MvPolynomial σ K)} :
    I.IsMaximal ↔ exists x : σ -> K, I = vanishingIdeal K {x} :=
  ⟨eq_vanishingIdeal_singleton_of_isMaximal K,
    fun ⟨_, hx⟩ => hx ▸ inferInstance⟩

/-- Main statement of the Nullstellensatz -/
@[simp]
/--
theorem `vanishingIdeal_zeroLocus_eq_radical` / 定理 `vanishingIdeal_zeroLocus_eq_radical`

English:
theorem vanishingIdeal_zeroLocus_eq_radical
  given: (I : Ideal (MvPolynomial σ k))
  proof: by
  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
  rw [I.radical_eq_jacobson]
  apply le_sInf
  rintro J ⟨hJI, hJ⟩
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine hx.symm ▸ vanishingIdeal_anti_mono fun y hy p hp => ?_
  rw [← mem_vanishingIdeal_singleton_iff]; rw [Set.mem_singleton_iff.1 hy]; rw [← hx]
  exact hJI hp

@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`

中文:
定理 vanishingIdeal_zeroLocus_eq_radical
  条件: (I : 理想 (多元多项式 σ k))
  证明: by
  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
  rw [I.radical_eq_jacobson]
  apply le_sInf
  rintro J ⟨hJI, hJ⟩
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine hx.symm ▸ vanishingIdeal_anti_mono fun y hy p hp => ?_
  rw [← mem_vanishingIdeal_singleton_iff]; rw [Set.mem_singleton_iff.1 hy]; rw [← hx]
  exact hJI hp

@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`

Depends on / 依赖: I.radical_eq_jacobson, Set.mem_singleton_iff, eq_vanishingIdeal_singleton_of_isMaximal, hx.symm, le_antisymm, le_sInf, mem_singleton_iff, mem_vanishingIdeal_singleton_iff, radical_eq_jacobson, radical_le_vanishingIdeal_zeroLocus, vanishingIdeal_anti_mono
-/
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal k (zeroLocus K I) = I.radical := by
  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
  rw [I.radical_eq_jacobson]
  apply le_sInf
  rintro J ⟨hJI, hJ⟩
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine hx.symm ▸ vanishingIdeal_anti_mono fun y hy p hp => ?_
  rw [← mem_vanishingIdeal_singleton_iff]; rw [Set.mem_singleton_iff.1 hy]; rw [← hx]
  exact hJI hp

@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`
/--
theorem `IsPrime.vanishingIdeal_zeroLocus` / 定理 `IsPrime.vanishingIdeal_zeroLocus`

English:
theorem IsPrime.vanishingIdeal_zeroLocus
  given: (P : Ideal (MvPolynomial σ k)) [h : P.IsPrime]
  proof: Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical

中文:
定理 是素.vanishingIdeal_zeroLocus
  条件: (P : 理想 (多元多项式 σ k)) [h : P.是素]
  证明: Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical

Depends on / 依赖: Trans.trans, h.radical, radical, vanishingIdeal_zeroLocus_eq_radical
-/
theorem IsPrime.vanishingIdeal_zeroLocus (P : Ideal (MvPolynomial σ k)) [h : P.IsPrime] :
    vanishingIdeal k (zeroLocus K P) = P :=
  Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical

end MvPolynomial
