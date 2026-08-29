/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Ring Homomorphisms surjective on stalks

In this file, we prove some results on ring homomorphisms surjective on stalks, to be used in
the development of immersions in algebraic geometry.

A ring homomorphism `R →+* S` is surjective on stalks if `R_p →+* S_q` is surjective for all pairs
of primes `p = f⁻¹(q)`. We show that this property is stable under composition and base change, and
that surjections and localizations satisfy this.

-/

@[expose] public section

variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable {T : Type*} [CommRing T]
variable {g : S ->+* T} {f : R ->+* S}

namespace RingHom

/--
Definition of `SurjectiveOnStalks` / `SurjectiveOnStalks` 的定义

English:
definition SurjectiveOnStalks
  signature: (f : R ->+* S)
  body: forall (P : Ideal S) (_ : P.IsPrime), Function.Surjective (Localization.localRingHom _ P f rfl)

中文:
定义 SurjectiveOnStalks
  签名: (f : R ->+* S)
  定义体: forall (P : Ideal S) (_ : P.IsPrime), Function.Surjective (Localization.localRingHom _ P f rfl)

Depends on / 依赖: Function, Function.Surjective, IsPrime, Localization, Localization.localRingHom, P.IsPrime, Surjective, localRingHom
-/
def SurjectiveOnStalks (f : R ->+* S) : Prop :=
  forall (P : Ideal S) (_ : P.IsPrime), Function.Surjective (Localization.localRingHom _ P f rfl)

/--
lemma `surjective_localRingHom_iff` / 引理 `surjective_localRingHom_iff`

English:
lemma surjective_localRingHom_iff
  given: (P : Ideal S) [P.IsPrime]
  proof: by
  constructor
  · intro H y
    obtain ⟨a, ha⟩ := H (IsLocalization.mk' _ y (1 : P.primeCompl))
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (P.comap f).primeCompl a
    rw [Localization.localRingHom_mk']; rw [IsLocalization.mk'_eq_iff_eq]; rw [Submonoid.coe_one]; rw [one_mul]; rw [IsLocalization.eq_iff_exists P.primeCompl] at ha
    obtain ⟨c, hc⟩ := ha
    simp only [← mul_assoc] at hc
    exact ⟨_, _, _, c.2, t.2, hc.symm⟩
  · refine fun H y => Localization.ind (fun ⟨y, t, h⟩ => ?_) y
    simp only
    obtain ⟨yx, ys, yc, hyc, hy, ey⟩ := H y
    obtain ⟨tx, ts, yt, hyt, ht, et⟩ := H t
    refine ⟨Localization.mk (yx * ts) ⟨ys * tx, Submonoid.mul_mem _ hy ?_⟩, ?_⟩
    · exact fun H => mul_mem (P.primeCompl.mul_mem hyt ht) h (et ▸ Ideal.mul_mem_left _ yt H)
    · simp only [Localization.mk_eq_mk', Localization.localRingHom_mk', map_mul f,
        IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists P.primeCompl]
      refine ⟨⟨yc, hyc⟩ * ⟨yt, hyt⟩, ?_⟩
      simp only [Submonoid.coe_mul]
      convert! congr($(ey.symm) * $(et)) using 1 <;> ring

中文:
引理 surjective_localRingHom_iff
  条件: (P : 理想 S) [P.是素]
  证明: by
  constructor
  · intro H y
    obtain ⟨a, ha⟩ := H (IsLocalization.mk' _ y (1 : P.primeCompl))
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (P.comap f).primeCompl a
    rw [Localization.localRingHom_mk']; rw [IsLocalization.mk'_eq_iff_eq]; rw [Submonoid.coe_one]; rw [one_mul]; rw [IsLocalization.eq_iff_exists P.primeCompl] at ha
    obtain ⟨c, hc⟩ := ha
    simp only [← mul_assoc] at hc
    exact ⟨_, _, _, c.2, t.2, hc.symm⟩
  · refine fun H y => Localization.ind (fun ⟨y, t, h⟩ => ?_) y
    simp only
    obtain ⟨yx, ys, yc, hyc, hy, ey⟩ := H y
    obtain ⟨tx, ts, yt, hyt, ht, et⟩ := H t
    refine ⟨Localization.mk (yx * ts) ⟨ys * tx, Submonoid.mul_mem _ hy ?_⟩, ?_⟩
    · exact fun H => mul_mem (P.primeCompl.mul_mem hyt ht) h (et ▸ Ideal.mul_mem_left _ yt H)
    · simp only [Localization.mk_eq_mk', Localization.localRingHom_mk', map_mul f,
        IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists P.primeCompl]
      refine ⟨⟨yc, hyc⟩ * ⟨yt, hyt⟩, ?_⟩
      simp only [Submonoid.coe_mul]
      convert! congr($(ey.symm) * $(et)) using 1 <;> ring

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.exists_mk, IsLocalization.mk, Localization, Localization.ind, Localization.localRingHom_mk, P.comap, P.primeCompl, Submonoid, Submonoid.coe_one, _eq_iff_eq, coe_one, eq_iff_exists, exists_mk, hc.symm, localRingHom_mk, mul_assoc, one_mul, primeCompl
-/
lemma surjective_localRingHom_iff (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom _ P f rfl) ↔
      forall s : S, exists x r : R, exists c ∉ P, f r ∉ P ∧ c * f r * s = c * f x := by
  constructor
  · intro H y
    obtain ⟨a, ha⟩ := H (IsLocalization.mk' _ y (1 : P.primeCompl))
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (P.comap f).primeCompl a
    rw [Localization.localRingHom_mk']; rw [IsLocalization.mk'_eq_iff_eq]; rw [Submonoid.coe_one]; rw [one_mul]; rw [IsLocalization.eq_iff_exists P.primeCompl] at ha
    obtain ⟨c, hc⟩ := ha
    simp only [← mul_assoc] at hc
    exact ⟨_, _, _, c.2, t.2, hc.symm⟩
  · refine fun H y => Localization.ind (fun ⟨y, t, h⟩ => ?_) y
    simp only
    obtain ⟨yx, ys, yc, hyc, hy, ey⟩ := H y
    obtain ⟨tx, ts, yt, hyt, ht, et⟩ := H t
    refine ⟨Localization.mk (yx * ts) ⟨ys * tx, Submonoid.mul_mem _ hy ?_⟩, ?_⟩
    · exact fun H => mul_mem (P.primeCompl.mul_mem hyt ht) h (et ▸ Ideal.mul_mem_left _ yt H)
    · simp only [Localization.mk_eq_mk', Localization.localRingHom_mk', map_mul f,
        IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists P.primeCompl]
      refine ⟨⟨yc, hyc⟩ * ⟨yt, hyt⟩, ?_⟩
      simp only [Submonoid.coe_mul]
      convert! congr($(ey.symm) * $(et)) using 1 <;> ring

/--
lemma `surjectiveOnStalks_iff_forall_ideal` / 引理 `surjectiveOnStalks_iff_forall_ideal`

English:
lemma surjectiveOnStalks_iff_forall_ideal
  proof: by
  simp_rw [SurjectiveOnStalks, surjective_localRingHom_iff]
  refine ⟨fun H I hI s => ?_, fun H I hI => H I hI.ne_top⟩
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM.isPrime s
  exact ⟨x, r, c, fun h => hc (hIM h), fun h => hr (hIM h), e⟩

中文:
引理 surjectiveOnStalks_iff_对任意_ideal
  证明: by
  simp_rw [SurjectiveOnStalks, surjective_localRingHom_iff]
  refine ⟨fun H I hI s => ?_, fun H I hI => H I hI.ne_top⟩
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM.isPrime s
  exact ⟨x, r, c, fun h => hc (hIM h), fun h => hr (hIM h), e⟩

Depends on / 依赖: I.exists_le_maximal, SurjectiveOnStalks, exists_le_maximal, hI.ne_top, hM.isPrime, isPrime, ne_top, simp_rw, surjective_localRingHom_iff
-/
lemma surjectiveOnStalks_iff_forall_ideal :
    f.SurjectiveOnStalks ↔
      forall I : Ideal S, I != ⊤ -> forall s : S, exists x r : R, exists c ∉ I, f r ∉ I ∧ c * f r * s = c * f x := by
  simp_rw [SurjectiveOnStalks, surjective_localRingHom_iff]
  refine ⟨fun H I hI s => ?_, fun H I hI => H I hI.ne_top⟩
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM.isPrime s
  exact ⟨x, r, c, fun h => hc (hIM h), fun h => hr (hIM h), e⟩

/--
lemma `surjectiveOnStalks_iff_forall_maximal` / 引理 `surjectiveOnStalks_iff_forall_maximal`

English:
lemma surjectiveOnStalks_iff_forall_maximal
  proof: by
  refine ⟨fun H I hI => H I hI.isPrime, fun H I hI => ?_⟩
  simp_rw [surjective_localRingHom_iff] at H ⊢
  intro s
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM s
  exact ⟨x, r, c, fun h => hc (hIM h), fun h => hr (hIM h), e⟩

中文:
引理 surjectiveOnStalks_iff_对任意_maximal
  证明: by
  refine ⟨fun H I hI => H I hI.isPrime, fun H I hI => ?_⟩
  simp_rw [surjective_localRingHom_iff] at H ⊢
  intro s
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM s
  exact ⟨x, r, c, fun h => hc (hIM h), fun h => hr (hIM h), e⟩

Depends on / 依赖: I.exists_le_maximal, exists_le_maximal, hI.isPrime, hI.ne_top, isPrime, ne_top, simp_rw, surjective_localRingHom_iff
-/
lemma surjectiveOnStalks_iff_forall_maximal :
    f.SurjectiveOnStalks ↔ forall (I : Ideal S) (_ : I.IsMaximal),
      Function.Surjective (Localization.localRingHom _ I f rfl) := by
  refine ⟨fun H I hI => H I hI.isPrime, fun H I hI => ?_⟩
  simp_rw [surjective_localRingHom_iff] at H ⊢
  intro s
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM s
  exact ⟨x, r, c, fun h => hc (hIM h), fun h => hr (hIM h), e⟩

/--
lemma `surjectiveOnStalks_iff_forall_maximal'` / 引理 `surjectiveOnStalks_iff_forall_maximal'`

English:
lemma surjectiveOnStalks_iff_forall_maximal'
  proof: by
  simp only [surjectiveOnStalks_iff_forall_maximal, surjective_localRingHom_iff]

中文:
引理 surjectiveOnStalks_iff_对任意_maximal'
  证明: by
  simp only [surjectiveOnStalks_iff_forall_maximal, surjective_localRingHom_iff]

Depends on / 依赖: surjectiveOnStalks_iff_forall_maximal, surjective_localRingHom_iff
-/
lemma surjectiveOnStalks_iff_forall_maximal' :
    f.SurjectiveOnStalks ↔ forall I : Ideal S, I.IsMaximal ->
      forall s : S, exists x r : R, exists c ∉ I, f r ∉ I ∧ c * f r * s = c * f x := by
  simp only [surjectiveOnStalks_iff_forall_maximal, surjective_localRingHom_iff]

/--
lemma `surjectiveOnStalks_of_exists_div` / 引理 `surjectiveOnStalks_of_exists_div`

English:
lemma surjectiveOnStalks_of_exists_div
  given: (h : forall x : S, exists r s : R, IsUnit (f s) ∧ f s * x = f r)
  proof: surjectiveOnStalks_iff_forall_ideal.mpr fun I hI x =>
    let ⟨r, s, hr, hr'⟩ := h x
    ⟨r, s, 1, by simpa [← Ideal.eq_top_iff_one], fun h => hI (I.eq_top_of_isUnit_mem h hr), by simpa⟩

中文:
引理 surjectiveOnStalks_of_存在_div
  条件: (h : 对任意 x : S, 存在 r s : R, 是单位 (f s) ∧ f s * x = f r)
  证明: surjectiveOnStalks_iff_forall_ideal.mpr fun I hI x =>
    let ⟨r, s, hr, hr'⟩ := h x
    ⟨r, s, 1, by simpa [← Ideal.eq_top_iff_one], fun h => hI (I.eq_top_of_isUnit_mem h hr), by simpa⟩

Depends on / 依赖: I.eq_top_of_isUnit_mem, Ideal.eq_top_iff_one, eq_top_iff_one, eq_top_of_isUnit_mem, surjectiveOnStalks_iff_forall_ideal, surjectiveOnStalks_iff_forall_ideal.mpr
-/
lemma surjectiveOnStalks_of_exists_div (h : forall x : S, exists r s : R, IsUnit (f s) ∧ f s * x = f r) :
    SurjectiveOnStalks f :=
  surjectiveOnStalks_iff_forall_ideal.mpr fun I hI x =>
    let ⟨r, s, hr, hr'⟩ := h x
    ⟨r, s, 1, by simpa [← Ideal.eq_top_iff_one], fun h => hI (I.eq_top_of_isUnit_mem h hr), by simpa⟩

/--
lemma `surjectiveOnStalks_of_surjective` / 引理 `surjectiveOnStalks_of_surjective`

English:
lemma surjectiveOnStalks_of_surjective
  given: (h : Function.Surjective f)
  proof: surjectiveOnStalks_iff_forall_ideal.mpr fun _ _ s =>
    let ⟨r, hr⟩ := h s
    ⟨r, 1, 1, by simpa [← Ideal.eq_top_iff_one], by simpa [← Ideal.eq_top_iff_one], by simp [hr]⟩

中文:
引理 surjectiveOnStalks_of_surjective
  条件: (h : 函数.满射 f)
  证明: surjectiveOnStalks_iff_forall_ideal.mpr fun _ _ s =>
    let ⟨r, hr⟩ := h s
    ⟨r, 1, 1, by simpa [← Ideal.eq_top_iff_one], by simpa [← Ideal.eq_top_iff_one], by simp [hr]⟩

Depends on / 依赖: Ideal.eq_top_iff_one, eq_top_iff_one, surjectiveOnStalks_iff_forall_ideal, surjectiveOnStalks_iff_forall_ideal.mpr
-/
lemma surjectiveOnStalks_of_surjective (h : Function.Surjective f) :
    SurjectiveOnStalks f :=
  surjectiveOnStalks_iff_forall_ideal.mpr fun _ _ s =>
    let ⟨r, hr⟩ := h s
    ⟨r, 1, 1, by simpa [← Ideal.eq_top_iff_one], by simpa [← Ideal.eq_top_iff_one], by simp [hr]⟩

/--
lemma `_root_.RingEquiv.surjectiveOnStalks` / 引理 `_root_.RingEquiv.surjectiveOnStalks`

English:
lemma _root_.RingEquiv.surjectiveOnStalks
  given: (e : R ≃+* S)
  proof: RingHom.surjectiveOnStalks_of_surjective e.surjective

中文:
引理 _root_.环等价.surjectiveOnStalks
  条件: (e : R ≃+* S)
  证明: RingHom.surjectiveOnStalks_of_surjective e.surjective

Depends on / 依赖: RingHom, RingHom.surjectiveOnStalks_of_surjective, e.surjective, surjective, surjectiveOnStalks_of_surjective
-/
lemma _root_.RingEquiv.surjectiveOnStalks (e : R ≃+* S) :
    e.toRingHom.SurjectiveOnStalks :=
  RingHom.surjectiveOnStalks_of_surjective e.surjective

/--
lemma `SurjectiveOnStalks.comp` / 引理 `SurjectiveOnStalks.comp`

English:
lemma SurjectiveOnStalks.comp
  given: (hg : SurjectiveOnStalks g) (hf : SurjectiveOnStalks f)
  proof: by
  intro I hI
  have := (hg I hI).comp (hf _ (hI.comap g))
  rwa [← RingHom.coe_comp, ← Localization.localRingHom_comp] at this

中文:
引理 SurjectiveOnStalks.comp
  条件: (hg : SurjectiveOnStalks g) (hf : SurjectiveOnStalks f)
  证明: by
  intro I hI
  have := (hg I hI).comp (hf _ (hI.comap g))
  rwa [← RingHom.coe_comp, ← Localization.localRingHom_comp] at this

Depends on / 依赖: Localization, Localization.localRingHom_comp, RingHom, RingHom.coe_comp, coe_comp, hI.comap, localRingHom_comp
-/
lemma SurjectiveOnStalks.comp (hg : SurjectiveOnStalks g) (hf : SurjectiveOnStalks f) :
    SurjectiveOnStalks (g.comp f) := by
  intro I hI
  have := (hg I hI).comp (hf _ (hI.comap g))
  rwa [← RingHom.coe_comp, ← Localization.localRingHom_comp] at this

/--
lemma `SurjectiveOnStalks.of_comp` / 引理 `SurjectiveOnStalks.of_comp`

English:
lemma SurjectiveOnStalks.of_comp
  given: (hg : SurjectiveOnStalks (g.comp f))
  proof: by
  intro I hI
  have := hg I hI
  rw [Localization.localRingHom_comp (I.comap (g.comp f)) (I.comap g) _ _ rfl _ rfl]; rw [RingHom.coe_comp] at this
  exact this.of_comp

中文:
引理 SurjectiveOnStalks.of_comp
  条件: (hg : SurjectiveOnStalks (g.comp f))
  证明: by
  intro I hI
  have := hg I hI
  rw [Localization.localRingHom_comp (I.comap (g.comp f)) (I.comap g) _ _ rfl _ rfl]; rw [RingHom.coe_comp] at this
  exact this.of_comp

Depends on / 依赖: I.comap, Localization, Localization.localRingHom_comp, RingHom, RingHom.coe_comp, coe_comp, g.comp, localRingHom_comp, of_comp, this.of_comp
-/
lemma SurjectiveOnStalks.of_comp (hg : SurjectiveOnStalks (g.comp f)) :
    SurjectiveOnStalks g := by
  intro I hI
  have := hg I hI
  rw [Localization.localRingHom_comp (I.comap (g.comp f)) (I.comap g) _ _ rfl _ rfl]; rw [RingHom.coe_comp] at this
  exact this.of_comp

/--
lemma `SurjectiveOnStalks.localRingHom_surjective` / 引理 `SurjectiveOnStalks.localRingHom_surjective`

English:
lemma SurjectiveOnStalks.localRingHom_surjective
  statement: (hf : SurjectiveOnStalks f)
  proof: e ▸ hf Q _

中文:
引理 SurjectiveOnStalks.localRingHom_surjective
  结论: (hf : SurjectiveOnStalks f)
  证明: e ▸ hf Q _
-/
lemma SurjectiveOnStalks.localRingHom_surjective (hf : SurjectiveOnStalks f)
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] (e : P = Q.comap f) :
    Function.Surjective (Localization.localRingHom P Q f e) :=
  e ▸ hf Q _

open TensorProduct

variable [Algebra R T] [Algebra R S] in
/--
lemma `SurjectiveOnStalks.exists_mul_eq_tmul` / 引理 `SurjectiveOnStalks.exists_mul_eq_tmul`

English:
lemma SurjectiveOnStalks.exists_mul_eq_tmul
  proof: by
  induction x with
  | zero =>
    exact ⟨1, 1, 0, by rw [one_smul]; exact J.primeCompl.one_mem,
      by rw [mul_zero, TensorProduct.zero_tmul]⟩
  | tmul x₁ x₂ =>
    obtain ⟨y, s, c, hs, hc, e⟩ := (surjective_localRingHom_iff _).mp (hf₂ J hJ) x₂
    simp_rw [Algebra.smul_def]
    refine ⟨c, s, y • x₁, J.primeCompl.mul_mem hc hs, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [mul_comm _ c]; rw [e]; rw [TensorProduct.smul_tmul]; rw [Algebra.smul_def]; rw [mul_comm]
  | add x₁ x₂ hx₁ hx₂ =>
    obtain ⟨t₁, r₁, a₁, hr₁, e₁⟩ := hx₁
    obtain ⟨t₂, r₂, a₂, hr₂, e₂⟩ := hx₂
    have : (r₁ * r₂) • (t₁ * t₂) = (r₁ • t₁) * (r₂ • t₂) := by
      simp_rw [← smul_eq_mul]; rw [smul_smul_smul_comm]
    refine ⟨t₁ * t₂, r₁ * r₂, r₂ • a₁ + r₁ • a₂, this.symm ▸ J.primeCompl.mul_mem hr₁ hr₂, ?_⟩
    rw [this]; rw [← one_mul (1 : S)]; rw [← Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_add]; rw [mul_comm (_ otimesₜ _)]; rw [mul_assoc]; rw [e₁]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [smul_mul_assoc]; rw [← TensorProduct.smul_tmul]; rw [mul_comm (_ otimesₜ _)]; rw [mul_assoc]; rw [e₂]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [smul_mul_assoc]; rw [← TensorProduct.smul_tmul]; rw [TensorProduct.add_tmul]; rw [mul_comm t₁ t₂]

中文:
引理 SurjectiveOnStalks.存在_mul_eq_tmul
  证明: by
  induction x with
  | zero =>
    exact ⟨1, 1, 0, by rw [one_smul]; exact J.primeCompl.one_mem,
      by rw [mul_zero, TensorProduct.zero_tmul]⟩
  | tmul x₁ x₂ =>
    obtain ⟨y, s, c, hs, hc, e⟩ := (surjective_localRingHom_iff _).mp (hf₂ J hJ) x₂
    simp_rw [Algebra.smul_def]
    refine ⟨c, s, y • x₁, J.primeCompl.mul_mem hc hs, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [mul_comm _ c]; rw [e]; rw [TensorProduct.smul_tmul]; rw [Algebra.smul_def]; rw [mul_comm]
  | add x₁ x₂ hx₁ hx₂ =>
    obtain ⟨t₁, r₁, a₁, hr₁, e₁⟩ := hx₁
    obtain ⟨t₂, r₂, a₂, hr₂, e₂⟩ := hx₂
    have : (r₁ * r₂) • (t₁ * t₂) = (r₁ • t₁) * (r₂ • t₂) := by
      simp_rw [← smul_eq_mul]; rw [smul_smul_smul_comm]
    refine ⟨t₁ * t₂, r₁ * r₂, r₂ • a₁ + r₁ • a₂, this.symm ▸ J.primeCompl.mul_mem hr₁ hr₂, ?_⟩
    rw [this]; rw [← one_mul (1 : S)]; rw [← Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_add]; rw [mul_comm (_ otimesₜ _)]; rw [mul_assoc]; rw [e₁]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [smul_mul_assoc]; rw [← TensorProduct.smul_tmul]; rw [mul_comm (_ otimesₜ _)]; rw [mul_assoc]; rw [e₂]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [smul_mul_assoc]; rw [← TensorProduct.smul_tmul]; rw [TensorProduct.add_tmul]; rw [mul_comm t₁ t₂]

Depends on / 依赖: Algebra, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def, J.primeCompl.mul_mem, J.primeCompl.one_mem, TensorProduct, TensorProduct.smul_tmul, TensorProduct.zero_tmul, mul_comm, mul_mem, mul_zero, one_mem, one_mul, one_smul, primeCompl, simp_rw, smul_def, smul_tmul, surjective_localRingHom_iff, tmul_mul_tmul
-/
lemma SurjectiveOnStalks.exists_mul_eq_tmul
    (hf₂ : (algebraMap R T).SurjectiveOnStalks)
    (x : S otimes[R] T) (J : Ideal T) (hJ : J.IsPrime) :
    exists (t : T) (r : R) (a : S), (r • t ∉ J) ∧
      (1 : S) otimesₜ[R] (r • t) * x = a otimesₜ[R] t := by
  induction x with
  | zero =>
    exact ⟨1, 1, 0, by rw [one_smul]; exact J.primeCompl.one_mem,
      by rw [mul_zero, TensorProduct.zero_tmul]⟩
  | tmul x₁ x₂ =>
    obtain ⟨y, s, c, hs, hc, e⟩ := (surjective_localRingHom_iff _).mp (hf₂ J hJ) x₂
    simp_rw [Algebra.smul_def]
    refine ⟨c, s, y • x₁, J.primeCompl.mul_mem hc hs, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [mul_comm _ c]; rw [e]; rw [TensorProduct.smul_tmul]; rw [Algebra.smul_def]; rw [mul_comm]
  | add x₁ x₂ hx₁ hx₂ =>
    obtain ⟨t₁, r₁, a₁, hr₁, e₁⟩ := hx₁
    obtain ⟨t₂, r₂, a₂, hr₂, e₂⟩ := hx₂
    have : (r₁ * r₂) • (t₁ * t₂) = (r₁ • t₁) * (r₂ • t₂) := by
      simp_rw [← smul_eq_mul]; rw [smul_smul_smul_comm]
    refine ⟨t₁ * t₂, r₁ * r₂, r₂ • a₁ + r₁ • a₂, this.symm ▸ J.primeCompl.mul_mem hr₁ hr₂, ?_⟩
    rw [this]; rw [← one_mul (1 : S)]; rw [← Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_add]; rw [mul_comm (_ otimesₜ _)]; rw [mul_assoc]; rw [e₁]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [smul_mul_assoc]; rw [← TensorProduct.smul_tmul]; rw [mul_comm (_ otimesₜ _)]; rw [mul_assoc]; rw [e₂]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [one_mul]; rw [smul_mul_assoc]; rw [← TensorProduct.smul_tmul]; rw [TensorProduct.add_tmul]; rw [mul_comm t₁ t₂]

variable (S) in
/--
lemma `surjectiveOnStalks_of_isLocalization` / 引理 `surjectiveOnStalks_of_isLocalization`

English:
lemma surjectiveOnStalks_of_isLocalization
  proof: by
  refine surjectiveOnStalks_of_exists_div fun s => ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact ⟨x, s, IsLocalization.map_units S s, IsLocalization.mk'_spec' S x s⟩

中文:
引理 surjectiveOnStalks_of_isLocalization
  证明: by
  refine surjectiveOnStalks_of_exists_div fun s => ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact ⟨x, s, IsLocalization.map_units S s, IsLocalization.mk'_spec' S x s⟩

Depends on / 依赖: IsLocalization, IsLocalization.exists_mk, IsLocalization.map_units, IsLocalization.mk, _spec, exists_mk, map_units, surjectiveOnStalks_of_exists_div
-/
lemma surjectiveOnStalks_of_isLocalization
    [Algebra R S] [IsLocalization M S] :
    SurjectiveOnStalks (algebraMap R S) := by
  refine surjectiveOnStalks_of_exists_div fun s => ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact ⟨x, s, IsLocalization.map_units S s, IsLocalization.mk'_spec' S x s⟩

/--
lemma `SurjectiveOnStalks.baseChange` / 引理 `SurjectiveOnStalks.baseChange`

English:
lemma SurjectiveOnStalks.baseChange
  proof: by
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro J hJ
  rw [surjective_localRingHom_iff]
  intro x
  obtain ⟨t, r, a, ht, e⟩ := hf.exists_mul_eq_tmul x (J.comap g) inferInstance
  refine ⟨a, algebraMap _ _ r, 1 otimesₜ (r • t), ht, ?_, ?_⟩
  · intro H
    simp only [Algebra.algebraMap_eq_smul_one (A := S), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, id_apply, smul_tmul, ← Algebra.algebraMap_eq_smul_one (A := T)] at H
    rw [Ideal.mem_comap]; rw [Algebra.smul_def]; rw [g.map_mul] at ht
    exact ht (J.mul_mem_right _ H)
  · simp only [tmul_smul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHomCompTriple.comp_apply, Algebra.smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, id_apply, ← e]
    rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [smul_mul_assoc]

中文:
引理 SurjectiveOnStalks.baseChange
  证明: by
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro J hJ
  rw [surjective_localRingHom_iff]
  intro x
  obtain ⟨t, r, a, ht, e⟩ := hf.exists_mul_eq_tmul x (J.comap g) inferInstance
  refine ⟨a, algebraMap _ _ r, 1 otimesₜ (r • t), ht, ?_, ?_⟩
  · intro H
    simp only [Algebra.algebraMap_eq_smul_one (A := S), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, id_apply, smul_tmul, ← Algebra.algebraMap_eq_smul_one (A := T)] at H
    rw [Ideal.mem_comap]; rw [Algebra.smul_def]; rw [g.map_mul] at ht
    exact ht (J.mul_mem_right _ H)
  · simp only [tmul_smul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHomCompTriple.comp_apply, Algebra.smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, id_apply, ← e]
    rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [smul_mul_assoc]

Depends on / 依赖: Algebra, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight.toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_self, Algebra.s, Ideal.mem_comap, J.comap, TensorProduct, algebraMap, algebraMap_apply, algebraMap_eq_smul_one, algebraMap_self, exists_mul_eq_tmul, hf.exists_mul_eq_tmul, id_apply, includeRight, mem_comap, otimes, smul_tmul
-/
lemma SurjectiveOnStalks.baseChange
    [Algebra R T] [Algebra R S]
    (hf : (algebraMap R T).SurjectiveOnStalks) :
    (algebraMap S (S otimes[R] T)).SurjectiveOnStalks := by
  let g : T ->+* S otimes[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro J hJ
  rw [surjective_localRingHom_iff]
  intro x
  obtain ⟨t, r, a, ht, e⟩ := hf.exists_mul_eq_tmul x (J.comap g) inferInstance
  refine ⟨a, algebraMap _ _ r, 1 otimesₜ (r • t), ht, ?_, ?_⟩
  · intro H
    simp only [Algebra.algebraMap_eq_smul_one (A := S), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, id_apply, smul_tmul, ← Algebra.algebraMap_eq_smul_one (A := T)] at H
    rw [Ideal.mem_comap]; rw [Algebra.smul_def]; rw [g.map_mul] at ht
    exact ht (J.mul_mem_right _ H)
  · simp only [tmul_smul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHomCompTriple.comp_apply, Algebra.smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, id_apply, ← e]
    rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [smul_mul_assoc]

/--
lemma `SurjectiveOnStalks.baseChange'` / 引理 `SurjectiveOnStalks.baseChange'`

English:
lemma SurjectiveOnStalks.baseChange'
  statement: [Algebra R T] [Algebra R S]
  proof: by
  convert!
    (surjectiveOnStalks_of_surjective (Algebra.TensorProduct.comm R T S).surjective).comp
      (hf.baseChange (S := T))
        -- Subsumed by `RingHom.SurjectiveOnStalks.tensorProductMap`.

中文:
引理 SurjectiveOnStalks.baseChange'
  结论: [代数 R T] [代数 R S]
  证明: by
  convert!
    (surjectiveOnStalks_of_surjective (Algebra.TensorProduct.comm R T S).surjective).comp
      (hf.baseChange (S := T))
        -- Subsumed by `RingHom.SurjectiveOnStalks.tensorProductMap`.

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, SurjectiveOnStalks, TensorProduct, baseChange, convert, hf.baseChange, surjective, surjectiveOnStalks_of_surjective
-/
lemma SurjectiveOnStalks.baseChange' [Algebra R T] [Algebra R S]
    (hf : (algebraMap R S).SurjectiveOnStalks) :
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).SurjectiveOnStalks := by
  convert!
    (surjectiveOnStalks_of_surjective (Algebra.TensorProduct.comm R T S).surjective).comp
      (hf.baseChange (S := T))
        -- Subsumed by `RingHom.SurjectiveOnStalks.tensorProductMap`.


-- Subsumed by `RingHom.SurjectiveOnStalks.tensorProductMap`.
/--
lemma `SurjectiveOnStalks.tensorProductMap_id` / 引理 `SurjectiveOnStalks.tensorProductMap_id`

English:
lemma SurjectiveOnStalks.tensorProductMap_id
  proof: by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).SurjectiveOnStalks
  convert_to ((Algebra.TensorProduct.cancelBaseChange R S S S' T).toAlgHom.comp
    Algebra.TensorProduct.includeRight).SurjectiveOnStalks
  · congr; ext; simp
  exact (Algebra.TensorProduct.cancelBaseChange R S S S' T).toRingEquiv.surjectiveOnStalks.comp
    Hf.baseChange'

中文:
引理 SurjectiveOnStalks.tensorProductMap_id
  证明: by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).SurjectiveOnStalks
  convert_to ((Algebra.TensorProduct.cancelBaseChange R S S S' T).toAlgHom.comp
    Algebra.TensorProduct.includeRight).SurjectiveOnStalks
  · congr; ext; simp
  exact (Algebra.TensorProduct.cancelBaseChange R S S S' T).toRingEquiv.surjectiveOnStalks.comp
    Hf.baseChange'
-/
private lemma SurjectiveOnStalks.tensorProductMap_id
    {S' : Type*} [CommRing S'] [Algebra R S] [Algebra R T] [Algebra R S']
    {f : S ->ₐ[R] S'} (Hf : f.SurjectiveOnStalks) :
    (Algebra.TensorProduct.map f (AlgHom.id R T)).SurjectiveOnStalks := by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).SurjectiveOnStalks
  convert_to ((Algebra.TensorProduct.cancelBaseChange R S S S' T).toAlgHom.comp
    Algebra.TensorProduct.includeRight).SurjectiveOnStalks
  · congr; ext; simp
  exact (Algebra.TensorProduct.cancelBaseChange R S S S' T).toRingEquiv.surjectiveOnStalks.comp
    Hf.baseChange'

/--
lemma `SurjectiveOnStalks.tensorProductMap` / 引理 `SurjectiveOnStalks.tensorProductMap`

English:
lemma SurjectiveOnStalks.tensorProductMap
  proof: by
  convert!
.comp RingHom.SurjectiveOnStalks.tensorProductMap_id (T := T') Hf
.comp (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
.comp RingHom.SurjectiveOnStalks.tensorProductMap_id (T := S) Hg
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp

中文:
引理 SurjectiveOnStalks.tensorProductMap
  证明: by
  convert!
.comp RingHom.SurjectiveOnStalks.tensorProductMap_id (T := T') Hf
.comp (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
.comp RingHom.SurjectiveOnStalks.tensorProductMap_id (T := S) Hg
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toRingEquiv_toRingHom, AlgHom, AlgHom.comp_toRingHom, AlgHom.toRingHom_eq_coe, Algebra, Algebra.TensorProduct.comm, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.SurjectiveOnStalks.tensorProductMap_id, SurjectiveOnStalks, TensorProduct, comp_toRingHom, convert, surjectiveOnStalks, tensorProductMap_id, toAlgHom_toRingHom, toRingEquiv
-/
lemma SurjectiveOnStalks.tensorProductMap
    {S' T' : Type*} [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    {f : S ->ₐ[R] S'} (Hf : f.SurjectiveOnStalks) {g : T ->ₐ[R] T'} (Hg : g.SurjectiveOnStalks) :
    (Algebra.TensorProduct.map f g).SurjectiveOnStalks := by
  convert!
.comp RingHom.SurjectiveOnStalks.tensorProductMap_id (T := T') Hf
.comp (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
.comp RingHom.SurjectiveOnStalks.tensorProductMap_id (T := S) Hg
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp

/--
lemma `surjectiveOnStalks_iff_of_isLocalHom` / 引理 `surjectiveOnStalks_iff_of_isLocalHom`

English:
lemma surjectiveOnStalks_iff_of_isLocalHom
  given: [IsLocalRing S] [IsLocalHom f]
  proof: by
  refine ⟨fun H x => ?_, fun h => surjectiveOnStalks_of_surjective h⟩
  obtain ⟨y, r, c, hc, hr, e⟩ :=
    (surjective_localRingHom_iff _).mp (H (IsLocalRing.maximalIdeal _) inferInstance) x
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc hr
  refine ⟨(isUnit_of_map_unit f r hr).unit⁻¹ * y, ?_⟩
  apply hr.mul_right_injective
  apply hc.mul_right_injective
  simp only [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul, e]

中文:
引理 surjectiveOnStalks_iff_of_isLocalHom
  条件: [是局部环 S] [是Local态射 f]
  证明: by
  refine ⟨fun H x => ?_, fun h => surjectiveOnStalks_of_surjective h⟩
  obtain ⟨y, r, c, hc, hr, e⟩ :=
    (surjective_localRingHom_iff _).mp (H (IsLocalRing.maximalIdeal _) inferInstance) x
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc hr
  refine ⟨(isUnit_of_map_unit f r hr).unit⁻¹ * y, ?_⟩
  apply hr.mul_right_injective
  apply hc.mul_right_injective
  simp only [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul, e]

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, IsUnit, IsUnit.mul_val_inv, hc.mul_right_injective, hr.mul_right_injective, isUnit_of_map_unit, map_mul, maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mul_assoc, mul_right_injective, mul_val_inv, not_not, one_mul, surjectiveOnStalks_of_surjective, surjective_localRingHom_iff
-/
lemma surjectiveOnStalks_iff_of_isLocalHom [IsLocalRing S] [IsLocalHom f] :
    f.SurjectiveOnStalks ↔ Function.Surjective f := by
  refine ⟨fun H x => ?_, fun h => surjectiveOnStalks_of_surjective h⟩
  obtain ⟨y, r, c, hc, hr, e⟩ :=
    (surjective_localRingHom_iff _).mp (H (IsLocalRing.maximalIdeal _) inferInstance) x
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc hr
  refine ⟨(isUnit_of_map_unit f r hr).unit⁻¹ * y, ?_⟩
  apply hr.mul_right_injective
  apply hc.mul_right_injective
  simp only [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul, e]

end RingHom
