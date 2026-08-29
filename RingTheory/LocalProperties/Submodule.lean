/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Local properties of modules and submodules

In this file, we show that several conditions on submodules can be checked on stalks.
-/

public section

open scoped nonZeroDivisors

variable {R M M₁ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₁] [Module R M₁]

section maximal

variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : forall (P : Ideal R) [P.IsMaximal], M ->ₗ[R] Mₚ P)
  [forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
  (M₁ₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommMonoid (M₁ₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (M₁ₚ P)]
  (f₁ : forall (P : Ideal R) [P.IsMaximal], M₁ ->ₗ[R] M₁ₚ P)
  [forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f₁ P)]

/--
theorem `Submodule.mem_of_localization_maximal` / 定理 `Submodule.mem_of_localization_maximal`

English:
theorem Submodule.mem_of_localization_maximal
  statement: (m : M) (N : Submodule R M)
  proof: by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  refine Not.imp_symm I.exists_le_maximal fun ⟨P, hP, le⟩ => ?_
  obtain ⟨a, ha, s, e⟩ := h P
  rw [← IsLocalizedModule.mk'_one P.primeCompl]; rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp_rw [smul_smul] at ht
  exact (t * s).2 (le <| by apply ht ▸ smul_mem _ _ ha)

中文:
定理 子模.mem_of_localization_maximal
  结论: (m : M) (N : 子模 R M)
  证明: by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  refine Not.imp_symm I.exists_le_maximal fun ⟨P, hP, le⟩ => ?_
  obtain ⟨a, ha, s, e⟩ := h P
  rw [← IsLocalizedModule.mk'_one P.primeCompl]; rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp_rw [smul_smul] at ht
  exact (t * s).2 (le <| by apply ht ▸ smul_mem _ _ ha)

Depends on / 依赖: I.eq_top_iff_one.mp, I.exists_le_maximal, IsLocalizedModule, IsLocalizedModule.mk, LinearMap, LinearMap.toSpanSingleton, N.comap, Not.imp_symm, P.primeCompl, _eq_mk, _iff, _one, eq_top_iff_one, exists_le_maximal, imp_symm, primeCompl, simp_rw, smul_mem, smul_smul, toSpanSingleton
-/
theorem Submodule.mem_of_localization_maximal (m : M) (N : Submodule R M)
    (h : forall (P : Ideal R) [P.IsMaximal], f P m in N.localized₀ P.primeCompl (f P)) :
    m in N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  refine Not.imp_symm I.exists_le_maximal fun ⟨P, hP, le⟩ => ?_
  obtain ⟨a, ha, s, e⟩ := h P
  rw [← IsLocalizedModule.mk'_one P.primeCompl]; rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp_rw [smul_smul] at ht
  exact (t * s).2 (le <| by apply ht ▸ smul_mem _ _ ha)

/--
theorem `Submodule.le_of_localization_maximal` / 定理 `Submodule.le_of_localization_maximal`

English:
theorem Submodule.le_of_localization_maximal
  statement: {N₁ N₂ : Submodule R M}
  proof: fun m hm => mem_of_localization_maximal _ f _ _ fun P hP => h P ⟨m, hm, 1, by simp⟩

中文:
定理 子模.le_of_localization_maximal
  结论: {N₁ N₂ : 子模 R M}
  证明: fun m hm => mem_of_localization_maximal _ f _ _ fun P hP => h P ⟨m, hm, 1, by simp⟩

Depends on / 依赖: mem_of_localization_maximal
-/
theorem Submodule.le_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : forall (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) <= N₂.localized₀ P.primeCompl (f P)) :
    N₁ <= N₂ :=
  fun m hm => mem_of_localization_maximal _ f _ _ fun P hP => h P ⟨m, hm, 1, by simp⟩

/--
theorem `Submodule.eq_of_localization₀_maximal` / 定理 `Submodule.eq_of_localization₀_maximal`

English:
theorem Submodule.eq_of_localization₀_maximal
  statement: {N₁ N₂ : Submodule R M}
  proof: le_antisymm (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).le)
    (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).ge)

中文:
定理 子模.eq_of_localization₀_maximal
  结论: {N₁ N₂ : 子模 R M}
  证明: le_antisymm (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).le)
    (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).ge)

Depends on / 依赖: Submodule, Submodule.le_of_localization_maximal, le_antisymm, le_of_localization_maximal
-/
theorem Submodule.eq_of_localization₀_maximal {N₁ N₂ : Submodule R M}
    (h : forall (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) = N₂.localized₀ P.primeCompl (f P)) :
    N₁ = N₂ :=
  le_antisymm (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).le)
    (Submodule.le_of_localization_maximal Mₚ f fun P _ => (h P).ge)

/--
theorem `Submodule.eq_bot_of_localization₀_maximal` / 定理 `Submodule.eq_bot_of_localization₀_maximal`

English:
theorem Submodule.eq_bot_of_localization₀_maximal
  statement: (N : Submodule R M)
  proof: Submodule.eq_of_localization₀_maximal Mₚ f fun P hP => by simpa using h P

中文:
定理 子模.eq_bot_of_localization₀_maximal
  结论: (N : 子模 R M)
  证明: Submodule.eq_of_localization₀_maximal Mₚ f fun P hP => by simpa using h P

Depends on / 依赖: Submodule, Submodule.eq_of_localization
-/
theorem Submodule.eq_bot_of_localization₀_maximal (N : Submodule R M)
    (h : forall (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization₀_maximal Mₚ f fun P hP => by simpa using h P

/--
theorem `Submodule.eq_top_of_localization₀_maximal` / 定理 `Submodule.eq_top_of_localization₀_maximal`

English:
theorem Submodule.eq_top_of_localization₀_maximal
  statement: (N : Submodule R M)
  proof: Submodule.eq_of_localization₀_maximal Mₚ f fun P hP => by simpa using h P

中文:
定理 子模.eq_top_of_localization₀_maximal
  结论: (N : 子模 R M)
  证明: Submodule.eq_of_localization₀_maximal Mₚ f fun P hP => by simpa using h P

Depends on / 依赖: Submodule, Submodule.eq_of_localization
-/
theorem Submodule.eq_top_of_localization₀_maximal (N : Submodule R M)
    (h : forall (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊤) :
    N = ⊤ :=
  Submodule.eq_of_localization₀_maximal Mₚ f fun P hP => by simpa using h P

/--
theorem `Module.eq_of_localization_maximal` / 定理 `Module.eq_of_localization_maximal`

English:
theorem Module.eq_of_localization_maximal
  statement: (m m' : M)
  proof: by
  rw [← one_smul R m]; rw [← one_smul R m']
  by_contra ne
  have ⟨P, mP, le⟩ := (eqIdeal R m m').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists P.primeCompl _).mp (h P)
  exact s.2 (le hs)

中文:
定理 模.eq_of_localization_maximal
  结论: (m m' : M)
  证明: by
  rw [← one_smul R m]; rw [← one_smul R m']
  by_contra ne
  have ⟨P, mP, le⟩ := (eqIdeal R m m').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists P.primeCompl _).mp (h P)
  exact s.2 (le hs)

Depends on / 依赖: Ideal.ne_top_iff_one, IsLocalizedModule, IsLocalizedModule.eq_iff_exists, P.primeCompl, eqIdeal, eq_iff_exists, exists_le_maximal, ne_top_iff_one, one_smul, primeCompl
-/
theorem Module.eq_of_localization_maximal (m m' : M)
    (h : forall (P : Ideal R) [P.IsMaximal], f P m = f P m') :
    m = m' := by
  rw [← one_smul R m]; rw [← one_smul R m']
  by_contra ne
  have ⟨P, mP, le⟩ := (eqIdeal R m m').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists P.primeCompl _).mp (h P)
  exact s.2 (le hs)

/--
theorem `Module.eq_zero_of_localization_maximal` / 定理 `Module.eq_zero_of_localization_maximal`

English:
theorem Module.eq_zero_of_localization_maximal
  statement: (m : M)
  proof: eq_of_localization_maximal _ f _ _ fun P _ => by rw [h, map_zero]

中文:
定理 模.eq_zero_of_localization_maximal
  结论: (m : M)
  证明: eq_of_localization_maximal _ f _ _ fun P _ => by rw [h, map_zero]

Depends on / 依赖: eq_of_localization_maximal, map_zero
-/
theorem Module.eq_zero_of_localization_maximal (m : M)
    (h : forall (P : Ideal R) [P.IsMaximal], f P m = 0) :
    m = 0 :=
  eq_of_localization_maximal _ f _ _ fun P _ => by rw [h, map_zero]

/--
theorem `LinearMap.eq_of_localization_maximal` / 定理 `LinearMap.eq_of_localization_maximal`

English:
theorem LinearMap.eq_of_localization_maximal
  statement: (g g' : M ->ₗ[R] M₁)
  proof: ext fun x => Module.eq_of_localization_maximal _ f₁ _ _ fun P _ => by
    simpa only [IsLocalizedModule.map_apply] using DFunLike.congr_fun (h P) (f P x)

include f in

中文:
定理 线性映射.eq_of_localization_maximal
  结论: (g g' : M ->ₗ[R] M₁)
  证明: ext fun x => Module.eq_of_localization_maximal _ f₁ _ _ fun P _ => by
    simpa only [IsLocalizedModule.map_apply] using DFunLike.congr_fun (h P) (f P x)

include f in

Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsLocalizedModule, IsLocalizedModule.map_apply, Module, Module.eq_of_localization_maximal, congr_fun, eq_of_localization_maximal, map_apply
-/
theorem LinearMap.eq_of_localization_maximal (g g' : M ->ₗ[R] M₁)
    (h : forall (P : Ideal R) [P.IsMaximal],
      IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g =
      IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g') :
    g = g' :=
  ext fun x => Module.eq_of_localization_maximal _ f₁ _ _ fun P _ => by
    simpa only [IsLocalizedModule.map_apply] using DFunLike.congr_fun (h P) (f P x)

include f in
/--
theorem `Module.subsingleton_of_localization_maximal` / 定理 `Module.subsingleton_of_localization_maximal`

English:
theorem Module.subsingleton_of_localization_maximal
  proof: by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Mₚ f x 0 fun _ _ => Subsingleton.elim _ _

中文:
定理 模.subsingleton_of_localization_maximal
  证明: by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Mₚ f x 0 fun _ _ => Subsingleton.elim _ _

Depends on / 依赖: Module, Module.eq_of_localization_maximal, Subsingleton, Subsingleton.elim, eq_of_localization_maximal, subsingleton_iff_forall_eq
-/
theorem Module.subsingleton_of_localization_maximal
    (h : forall (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
    Subsingleton M := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Mₚ f x 0 fun _ _ => Subsingleton.elim _ _

/--
theorem `Submodule.eq_of_localization_maximal` / 定理 `Submodule.eq_of_localization_maximal`

English:
theorem Submodule.eq_of_localization_maximal
  statement: {N₁ N₂ : Submodule R M}
  proof: eq_of_localization₀_maximal Mₚ f fun P _ => congr(restrictScalars _ $(h P))

中文:
定理 子模.eq_of_localization_maximal
  结论: {N₁ N₂ : 子模 R M}
  证明: eq_of_localization₀_maximal Mₚ f fun P _ => congr(restrictScalars _ $(h P))

Depends on / 依赖: restrictScalars
-/
theorem Submodule.eq_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : forall (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) = N₂.localized' (Rₚ P) P.primeCompl (f P)) :
    N₁ = N₂ :=
  eq_of_localization₀_maximal Mₚ f fun P _ => congr(restrictScalars _ $(h P))

/--
theorem `Submodule.eq_bot_of_localization_maximal` / 定理 `Submodule.eq_bot_of_localization_maximal`

English:
theorem Submodule.eq_bot_of_localization_maximal
  statement: (N : Submodule R M)
  proof: Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

中文:
定理 子模.eq_bot_of_localization_maximal
  结论: (N : 子模 R M)
  证明: Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

Depends on / 依赖: Submodule, Submodule.eq_of_localization_maximal, eq_of_localization_maximal
-/
theorem Submodule.eq_bot_of_localization_maximal (N : Submodule R M)
    (h : forall (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

/--
theorem `Submodule.eq_top_of_localization_maximal` / 定理 `Submodule.eq_top_of_localization_maximal`

English:
theorem Submodule.eq_top_of_localization_maximal
  statement: (N : Submodule R M)
  proof: Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

中文:
定理 子模.eq_top_of_localization_maximal
  结论: (N : 子模 R M)
  证明: Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

Depends on / 依赖: Submodule, Submodule.eq_of_localization_maximal, eq_of_localization_maximal
-/
theorem Submodule.eq_top_of_localization_maximal (N : Submodule R M)
    (h : forall (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊤) :
    N = ⊤ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

end maximal

section span

open IsLocalizedModule LocalizedModule Ideal

variable (s : Set R) (span_eq : Ideal.span s = ⊤)
include span_eq

variable
  (Rₚ : forall _ : s, Type*)
  [forall r : s, CommSemiring (Rₚ r)]
  [forall r : s, Algebra R (Rₚ r)]
  [forall r : s, IsLocalization.Away r.1 (Rₚ r)]
  (Mₚ : forall _ : s, Type*)
  [forall r : s, AddCommMonoid (Mₚ r)]
  [forall r : s, Module R (Mₚ r)]
  [forall r : s, Module (Rₚ r) (Mₚ r)]
  [forall r : s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (f : forall r : s, M ->ₗ[R] Mₚ r)
  [forall r : s, IsLocalizedModule.Away r.1 (f r)]

/--
theorem `Module.eq_of_isLocalized_span` / 定理 `Module.eq_of_isLocalized_span`

English:
theorem Module.eq_of_isLocalized_span
  given: (x y : M) (h : forall r : s, f r x = f r y)
  statement: x = y
  proof: by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalizedModule.eq_iff_exists (.powers r.1) _).mp (h r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩

中文:
定理 模.eq_of_isLocalized_span
  条件: (x y : M) (h : 对任意 r : s, f r x = f r y)
  结论: x = y
  证明: by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalizedModule.eq_iff_exists (.powers r.1) _).mp (h r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.eq_iff_exists, Module, Module.eqIdeal, Set.disjoint_left.mp, disjoint_left, eqIdeal, eq_iff_exists, eq_top_iff_one, exists_disjoint_powers_of_span_eq_top, powers, span_eq
-/
theorem Module.eq_of_isLocalized_span (x y : M) (h : forall r : s, f r x = f r y) : x = y := by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalizedModule.eq_iff_exists (.powers r.1) _).mp (h r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩

/--
theorem `Module.eq_zero_of_isLocalized_span` / 定理 `Module.eq_zero_of_isLocalized_span`

English:
theorem Module.eq_zero_of_isLocalized_span
  given: (x : M) (h : forall r : s, f r x = 0)
  statement: x = 0
  proof: eq_of_isLocalized_span s span_eq _ f x 0 by simpa only [map_zero] using h

中文:
定理 模.eq_zero_of_isLocalized_span
  条件: (x : M) (h : 对任意 r : s, f r x = 0)
  结论: x = 0
  证明: eq_of_isLocalized_span s span_eq _ f x 0 by simpa only [map_zero] using h

Depends on / 依赖: eq_of_isLocalized_span, map_zero, span_eq
-/
theorem Module.eq_zero_of_isLocalized_span (x : M) (h : forall r : s, f r x = 0) : x = 0 :=
eq_of_isLocalized_span s span_eq _ f x 0 by simpa only [map_zero] using h

/--
theorem `Submodule.mem_of_isLocalized_span` / 定理 `Submodule.mem_of_isLocalized_span`

English:
theorem Submodule.mem_of_isLocalized_span
  statement: {m : M} {N : Submodule R M}
  proof: by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  by_contra! ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  obtain ⟨a, ha, t, e⟩ := h r
  rw [← IsLocalizedModule.mk'_one (.powers r.1)]; rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  have ⟨u, hu⟩ := e
  simp_rw [smul_smul] at hu
  exact Set.disjoint_right.mp disj (u * t).2 (by apply hu ▸ smul_mem _ _ ha)

中文:
定理 子模.mem_of_isLocalized_span
  结论: {m : M} {N : 子模 R M}
  证明: by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  by_contra! ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  obtain ⟨a, ha, t, e⟩ := h r
  rw [← IsLocalizedModule.mk'_one (.powers r.1)]; rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  have ⟨u, hu⟩ := e
  simp_rw [smul_smul] at hu
  exact Set.disjoint_right.mp disj (u * t).2 (by apply hu ▸ smul_mem _ _ ha)

Depends on / 依赖: I.eq_top_iff_one.mp, IsLocalizedModule, IsLocalizedModule.mk, LinearMap, LinearMap.toSpanSingleton, N.comap, Set.disjoint_right.mp, _eq_mk, _iff, _one, disjoint_right, eq_top_iff_one, exists_disjoint_powers_of_span_eq_top, powers, simp_rw, smul_mem, smul_smul, span_eq, toSpanSingleton
-/
theorem Submodule.mem_of_isLocalized_span {m : M} {N : Submodule R M}
    (h : forall r : s, f r m in N.localized₀ (.powers r.1) (f r)) : m in N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  by_contra! ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  obtain ⟨a, ha, t, e⟩ := h r
  rw [← IsLocalizedModule.mk'_one (.powers r.1)]; rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  have ⟨u, hu⟩ := e
  simp_rw [smul_smul] at hu
  exact Set.disjoint_right.mp disj (u * t).2 (by apply hu ▸ smul_mem _ _ ha)

/--
theorem `Submodule.le_of_isLocalized_span` / 定理 `Submodule.le_of_isLocalized_span`

English:
theorem Submodule.le_of_isLocalized_span
  statement: {N P : Submodule R M}
  proof: fun m hm => mem_of_isLocalized_span s span_eq _ f fun r => h r ⟨m, hm, 1, by simp⟩

中文:
定理 子模.le_of_isLocalized_span
  结论: {N P : 子模 R M}
  证明: fun m hm => mem_of_isLocalized_span s span_eq _ f fun r => h r ⟨m, hm, 1, by simp⟩

Depends on / 依赖: mem_of_isLocalized_span, span_eq
-/
theorem Submodule.le_of_isLocalized_span {N P : Submodule R M}
    (h : forall r : s, N.localized₀ (.powers r.1) (f r) <= P.localized₀ (.powers r.1) (f r)) : N <= P :=
  fun m hm => mem_of_isLocalized_span s span_eq _ f fun r => h r ⟨m, hm, 1, by simp⟩

/--
theorem `Submodule.eq_of_isLocalized₀_span` / 定理 `Submodule.eq_of_isLocalized₀_span`

English:
theorem Submodule.eq_of_isLocalized₀_span
  statement: {N P : Submodule R M}
  proof: le_antisymm (le_of_isLocalized_span s span_eq _ _ fun r => (h r).le)
    (le_of_isLocalized_span s span_eq _ _ fun r => (h r).ge)

中文:
定理 子模.eq_of_isLocalized₀_span
  结论: {N P : 子模 R M}
  证明: le_antisymm (le_of_isLocalized_span s span_eq _ _ fun r => (h r).le)
    (le_of_isLocalized_span s span_eq _ _ fun r => (h r).ge)

Depends on / 依赖: le_antisymm, le_of_isLocalized_span, span_eq
-/
theorem Submodule.eq_of_isLocalized₀_span {N P : Submodule R M}
    (h : forall r : s, N.localized₀ (.powers r.1) (f r) = P.localized₀ (.powers r.1) (f r)) : N = P :=
  le_antisymm (le_of_isLocalized_span s span_eq _ _ fun r => (h r).le)
    (le_of_isLocalized_span s span_eq _ _ fun r => (h r).ge)

/--
theorem `Submodule.eq_bot_of_isLocalized₀_span` / 定理 `Submodule.eq_bot_of_isLocalized₀_span`

English:
theorem Submodule.eq_bot_of_isLocalized₀_span
  statement: {N : Submodule R M}
  proof: eq_of_isLocalized₀_span s span_eq Mₚ f fun _ => by simp only [h, Submodule.localized₀_bot]

中文:
定理 子模.eq_bot_of_isLocalized₀_span
  结论: {N : 子模 R M}
  证明: eq_of_isLocalized₀_span s span_eq Mₚ f fun _ => by simp only [h, Submodule.localized₀_bot]

Depends on / 依赖: Submodule, Submodule.localized, span_eq
-/
theorem Submodule.eq_bot_of_isLocalized₀_span {N : Submodule R M}
    (h : forall r : s, N.localized₀ (.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_isLocalized₀_span s span_eq Mₚ f fun _ => by simp only [h, Submodule.localized₀_bot]

/--
theorem `Submodule.eq_top_of_isLocalized₀_span` / 定理 `Submodule.eq_top_of_isLocalized₀_span`

English:
theorem Submodule.eq_top_of_isLocalized₀_span
  statement: {N : Submodule R M}
  proof: eq_of_isLocalized₀_span s span_eq Mₚ f fun _ => by simp only [h, Submodule.localized₀_top]

中文:
定理 子模.eq_top_of_isLocalized₀_span
  结论: {N : 子模 R M}
  证明: eq_of_isLocalized₀_span s span_eq Mₚ f fun _ => by simp only [h, Submodule.localized₀_top]

Depends on / 依赖: Submodule, Submodule.localized, span_eq
-/
theorem Submodule.eq_top_of_isLocalized₀_span {N : Submodule R M}
    (h : forall r : s, N.localized₀ (.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_isLocalized₀_span s span_eq Mₚ f fun _ => by simp only [h, Submodule.localized₀_top]

/--
theorem `Submodule.eq_of_isLocalized'_span` / 定理 `Submodule.eq_of_isLocalized'_span`

English:
theorem Submodule.eq_of_isLocalized'_span
  statement: {N P : Submodule R M}
  proof: eq_of_isLocalized₀_span s span_eq _ f fun r => congr(restrictScalars _ $(h r))

中文:
定理 子模.eq_of_isLocalized'_span
  结论: {N P : 子模 R M}
  证明: eq_of_isLocalized₀_span s span_eq _ f fun r => congr(restrictScalars _ $(h r))

Depends on / 依赖: restrictScalars, span_eq
-/
theorem Submodule.eq_of_isLocalized'_span {N P : Submodule R M}
    (h : forall r, N.localized' (Rₚ r) (.powers r.1) (f r) = P.localized' (Rₚ r) (.powers r.1) (f r)) :
    N = P :=
  eq_of_isLocalized₀_span s span_eq _ f fun r => congr(restrictScalars _ $(h r))

/--
theorem `Submodule.eq_bot_of_isLocalized'_span` / 定理 `Submodule.eq_bot_of_isLocalized'_span`

English:
theorem Submodule.eq_bot_of_isLocalized'_span
  statement: {N : Submodule R M}
  proof: eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ => by simp only [h, Submodule.localized'_bot]

中文:
定理 子模.eq_bot_of_isLocalized'_span
  结论: {N : 子模 R M}
  证明: eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ => by simp only [h, Submodule.localized'_bot]

Depends on / 依赖: Submodule, Submodule.localized, _bot, _span, continuous_apply, continuous_fst, continuous_fst.prodMk, continuous_fst.smul, continuous_pi, continuous_snd, eq_of_isLocalized, localized, prodMk, span_eq
-/
theorem Submodule.eq_bot_of_isLocalized'_span {N : Submodule R M}
    (h : forall r : s, N.localized' (Rₚ r) (.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ => by simp only [h, Submodule.localized'_bot]

/--
theorem `Submodule.eq_top_of_isLocalized'_span` / 定理 `Submodule.eq_top_of_isLocalized'_span`

English:
theorem Submodule.eq_top_of_isLocalized'_span
  statement: {N : Submodule R M}
  proof: eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ => by simp only [h, Submodule.localized'_top]

中文:
定理 子模.eq_top_of_isLocalized'_span
  结论: {N : 子模 R M}
  证明: eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ => by simp only [h, Submodule.localized'_top]

Depends on / 依赖: Submodule, Submodule.localized, _span, _top, continuous_apply, continuous_id, continuous_pi, eq_of_isLocalized, localized, span_eq
-/
theorem Submodule.eq_top_of_isLocalized'_span {N : Submodule R M}
    (h : forall r : s, N.localized' (Rₚ r) (.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ => by simp only [h, Submodule.localized'_top]

end span
