/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Boundedness and vanishing at cusps

We define the notions of "bounded at c" and "vanishing at c" for functions on `ℍ`, where `c` is
an element of `OnePoint ℝ`.
-/

@[expose] public section

open Matrix SpecialLinearGroup UpperHalfPlane Filter Polynomial OnePoint

open scoped MatrixGroups LinearAlgebra.Projectivization ModularForm

namespace UpperHalfPlane

variable {g : GL (Fin 2) Real} {f : ℍ -> Complex} (k : Int)

/--
lemma `IsZeroAtImInfty.slash` / 引理 `IsZeroAtImInfty.slash`

English:
lemma IsZeroAtImInfty.slash
  given: (hg : g 1 0 = 0) (hf : IsZeroAtImInfty f)
  proof: by
  rw [IsZeroAtImInfty]; rw [ZeroAtFilter]; rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  simpa [ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _

中文:
引理 IsZeroAtImInfty.slash
  条件: (hg : g 1 0 = 0) (hf : IsZeroAtImInfty f)
  证明: by
  rw [IsZeroAtImInfty]; rw [ZeroAtFilter]; rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  simpa [ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _

Depends on / 依赖: IsZeroAtImInfty, ModularForm, ModularForm.slash_def, ZeroAtFilter, hf.comp, mul_assoc, mul_const, slash_def, tendsto_smul_atImInfty, tendsto_zero_iff_norm_tendsto_zero
-/
lemma IsZeroAtImInfty.slash (hg : g 1 0 = 0) (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [IsZeroAtImInfty]; rw [ZeroAtFilter]; rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  simpa [ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _

/--
lemma `IsBoundedAtImInfty.slash` / 引理 `IsBoundedAtImInfty.slash`

English:
lemma IsBoundedAtImInfty.slash
  given: (hg : g 1 0 = 0) (hf : IsBoundedAtImInfty f)
  proof: by
  rw [IsBoundedAtImInfty]; rw [BoundedAtFilter]; rw [← Asymptotics.isBigO_norm_left] at hf ⊢
  suffices (fun x => (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • x)‖) =O[atImInfty] 1 by
    simpa [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  apply (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left

中文:
引理 IsBoundedAtImInfty.slash
  条件: (hg : g 1 0 = 0) (hf : IsBoundedAtImInfty f)
  证明: by
  rw [IsBoundedAtImInfty]; rw [BoundedAtFilter]; rw [← Asymptotics.isBigO_norm_left] at hf ⊢
  suffices (fun x => (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • x)‖) =O[atImInfty] 1 by
    simpa [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  apply (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_norm_left, BoundedAtFilter, IsBoundedAtImInfty, ModularForm, ModularForm.slash_def, atImInfty, comp_tendsto, const_mul_left, g.det.val, hf.comp_tendsto, isBigO_norm_left, mul_assoc, mul_comm, slash_def, tendsto_smul_atImInfty
-/
lemma IsBoundedAtImInfty.slash (hg : g 1 0 = 0) (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [IsBoundedAtImInfty]; rw [BoundedAtFilter]; rw [← Asymptotics.isBigO_norm_left] at hf ⊢
  suffices (fun x => (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • x)‖) =O[atImInfty] 1 by
    simpa [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  apply (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left

end UpperHalfPlane

namespace OnePoint

variable (c : OnePoint Real) (f : ℍ -> Complex) (k : Int)

/--
Definition of `IsBoundedAt` / `IsBoundedAt` 的定义

English:
definition IsBoundedAt
  signature: : Prop
  body: forall g : GL (Fin 2) Real, g • ∞ = c -> IsBoundedAtImInfty (f ∣[k] g)

中文:
定义 IsBoundedAt
  签名: : 命题
  定义体: forall g : GL (Fin 2) Real, g • ∞ = c -> IsBoundedAtImInfty (f ∣[k] g)

Depends on / 依赖: IsBoundedAtImInfty
-/
def IsBoundedAt : Prop := forall g : GL (Fin 2) Real, g • ∞ = c -> IsBoundedAtImInfty (f ∣[k] g)

/--
Definition of `IsZeroAt` / `IsZeroAt` 的定义

English:
definition IsZeroAt
  signature: : Prop
  body: forall g : GL (Fin 2) Real, g • ∞ = c -> IsZeroAtImInfty (f ∣[k] g)

中文:
定义 IsZeroAt
  签名: : 命题
  定义体: forall g : GL (Fin 2) Real, g • ∞ = c -> IsZeroAtImInfty (f ∣[k] g)

Depends on / 依赖: IsZeroAtImInfty
-/
def IsZeroAt : Prop := forall g : GL (Fin 2) Real, g • ∞ = c -> IsZeroAtImInfty (f ∣[k] g)

variable {c f k} {g : GL (Fin 2) Real}

/--
lemma `IsBoundedAt.smul_iff` / 引理 `IsBoundedAt.smul_iff`

English:
lemma IsBoundedAt.smul_iff
  statement: IsBoundedAt (g • c) f k ↔ IsBoundedAt c (f ∣[k] g) k
  proof: by
  rw [IsBoundedAt]; rw [IsBoundedAt]; rw [(Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

中文:
引理 IsBoundedAt.smul_iff
  结论: IsBoundedAt (g • c) f k ↔ IsBoundedAt c (f ∣[k] g) k
  证明: by
  rw [IsBoundedAt]; rw [IsBoundedAt]; rw [(Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

Depends on / 依赖: Equiv.mulLeft, IsBoundedAt, SlashAction, SlashAction.slash_mul, forall_congr_left, mulLeft, mul_smul, slash_mul
-/
lemma IsBoundedAt.smul_iff : IsBoundedAt (g • c) f k ↔ IsBoundedAt c (f ∣[k] g) k := by
  rw [IsBoundedAt]; rw [IsBoundedAt]; rw [(Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

/--
lemma `IsZeroAt.smul_iff` / 引理 `IsZeroAt.smul_iff`

English:
lemma IsZeroAt.smul_iff
  statement: IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k
  proof: by
  rw [IsZeroAt]; rw [IsZeroAt]; rw [(Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

中文:
引理 IsZeroAt.smul_iff
  结论: IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k
  证明: by
  rw [IsZeroAt]; rw [IsZeroAt]; rw [(Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

Depends on / 依赖: Equiv.mulLeft, IsZeroAt, SlashAction, SlashAction.slash_mul, forall_congr_left, mulLeft, mul_smul, slash_mul
-/
lemma IsZeroAt.smul_iff : IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k := by
  rw [IsZeroAt]; rw [IsZeroAt]; rw [(Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

/--
lemma `IsBoundedAt.add` / 引理 `IsBoundedAt.add`

English:
lemma IsBoundedAt.add
  given: {f' : ℍ -> Complex} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k)
  proof: fun g hg => by simpa using! (hf g hg).add (hf' g hg)

中文:
引理 IsBoundedAt.add
  条件: {f' : ℍ -> 复形} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k)
  证明: fun g hg => by simpa using! (hf g hg).add (hf' g hg)
-/
lemma IsBoundedAt.add {f' : ℍ -> Complex} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k) :
    IsBoundedAt c (f + f') k :=
  fun g hg => by simpa using! (hf g hg).add (hf' g hg)

/--
lemma `IsZeroAt.add` / 引理 `IsZeroAt.add`

English:
lemma IsZeroAt.add
  given: {f' : ℍ -> Complex} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k)
  proof: fun g hg => by simpa using! (hf g hg).add (hf' g hg)

中文:
引理 IsZeroAt.add
  条件: {f' : ℍ -> 复形} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k)
  证明: fun g hg => by simpa using! (hf g hg).add (hf' g hg)
-/
lemma IsZeroAt.add {f' : ℍ -> Complex} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k) :
    IsZeroAt c (f + f') k :=
  fun g hg => by simpa using! (hf g hg).add (hf' g hg)

/--
lemma `isBoundedAt_infty_iff` / 引理 `isBoundedAt_infty_iff`

English:
lemma isBoundedAt_infty_iff
  statement: IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f
  proof: ⟨fun h => by simpa using h 1 (by simp), fun h _ hg => h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

中文:
引理 isBoundedAt_infty_iff
  结论: IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f
  证明: ⟨fun h => by simpa using h 1 (by simp), fun h _ hg => h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

Depends on / 依赖: h.slash, smul_infty_eq_self_iff, smul_infty_eq_self_iff.mp
-/
lemma isBoundedAt_infty_iff : IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f :=
  ⟨fun h => by simpa using h 1 (by simp), fun h _ hg => h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

/--
lemma `isZeroAt_infty_iff` / 引理 `isZeroAt_infty_iff`

English:
lemma isZeroAt_infty_iff
  statement: IsZeroAt ∞ f k ↔ IsZeroAtImInfty f
  proof: ⟨fun h => by simpa using h 1 (by simp), fun h _ hg => h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

中文:
引理 isZeroAt_infty_iff
  结论: IsZeroAt ∞ f k ↔ IsZeroAtImInfty f
  证明: ⟨fun h => by simpa using h 1 (by simp), fun h _ hg => h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

Depends on / 依赖: h.slash, smul_infty_eq_self_iff, smul_infty_eq_self_iff.mp
-/
lemma isZeroAt_infty_iff : IsZeroAt ∞ f k ↔ IsZeroAtImInfty f :=
  ⟨fun h => by simpa using h 1 (by simp), fun h _ hg => h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

/--
lemma `isBoundedAt_iff` / 引理 `isBoundedAt_iff`

English:
lemma isBoundedAt_iff
  given: (hg : g • ∞ = c)
  statement: IsBoundedAt c f k ↔ IsBoundedAtImInfty (f ∣[k] g)
  proof: ⟨fun hc => hc g hg , by simp [← hg, IsBoundedAt.smul_iff, isBoundedAt_infty_iff]⟩

中文:
引理 isBoundedAt_iff
  条件: (hg : g • ∞ = c)
  结论: IsBoundedAt c f k ↔ IsBoundedAtImInfty (f ∣[k] g)
  证明: ⟨fun hc => hc g hg , by simp [← hg, IsBoundedAt.smul_iff, isBoundedAt_infty_iff]⟩

Depends on / 依赖: IsBoundedAt, IsBoundedAt.smul_iff, isBoundedAt_infty_iff, smul_iff
-/
lemma isBoundedAt_iff (hg : g • ∞ = c) : IsBoundedAt c f k ↔ IsBoundedAtImInfty (f ∣[k] g) :=
  ⟨fun hc => hc g hg , by simp [← hg, IsBoundedAt.smul_iff, isBoundedAt_infty_iff]⟩

/--
lemma `isZeroAt_iff` / 引理 `isZeroAt_iff`

English:
lemma isZeroAt_iff
  given: (hg : g • ∞ = c)
  statement: IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g)
  proof: ⟨fun hc => hc g hg , by simp [← hg, IsZeroAt.smul_iff, isZeroAt_infty_iff]⟩

中文:
引理 isZeroAt_iff
  条件: (hg : g • ∞ = c)
  结论: IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g)
  证明: ⟨fun hc => hc g hg , by simp [← hg, IsZeroAt.smul_iff, isZeroAt_infty_iff]⟩

Depends on / 依赖: IsZeroAt, IsZeroAt.smul_iff, isZeroAt_infty_iff, smul_iff
-/
lemma isZeroAt_iff (hg : g • ∞ = c) : IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g) :=
  ⟨fun hc => hc g hg , by simp [← hg, IsZeroAt.smul_iff, isZeroAt_infty_iff]⟩

section SL2Z

variable {c : OnePoint Real} {f : ℍ -> Complex} {k : Int}

/--
lemma `isBoundedAt_iff_exists_SL2Z` / 引理 `isBoundedAt_iff_exists_SL2Z`

English:
lemma isBoundedAt_iff_exists_SL2Z
  given: (hc : IsCusp c 𝒮ℒ)
  proof: by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! fun hfc => ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! b

中文:
引理 isBoundedAt_iff_存在_SL2Z
  条件: (hc : IsCusp c 𝒮ℒ)
  证明: by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! fun hfc => ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! b

Depends on / 依赖: IsBoundedAt, IsBoundedAt.smul_iff, isBoundedAt_infty_iff, isCusp_SL2Z_iff, smul_iff
-/
lemma isBoundedAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsBoundedAt c f k ↔ exists γ : SL(2, Int), mapGL Real γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! fun hfc => ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! b

/--
lemma `isZeroAt_iff_exists_SL2Z` / 引理 `isZeroAt_iff_exists_SL2Z`

English:
lemma isZeroAt_iff_exists_SL2Z
  given: (hc : IsCusp c 𝒮ℒ)
  proof: by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! fun hfc => ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! b

中文:
引理 isZeroAt_iff_存在_SL2Z
  条件: (hc : IsCusp c 𝒮ℒ)
  证明: by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! fun hfc => ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! b

Depends on / 依赖: IsZeroAt, IsZeroAt.smul_iff, isCusp_SL2Z_iff, isZeroAt_infty_iff, smul_iff
-/
lemma isZeroAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsZeroAt c f k ↔ exists γ : SL(2, Int), mapGL Real γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! fun hfc => ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! b

/--
lemma `isBoundedAt_iff_forall_SL2Z` / 引理 `isBoundedAt_iff_forall_SL2Z`

English:
lemma isBoundedAt_iff_forall_SL2Z
  given: (hc : IsCusp c 𝒮ℒ)
  proof: by
  refine ⟨fun hc _ hγ => by simpa using! hc _ hγ, fun h => ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! h γ rfl

中文:
引理 isBoundedAt_iff_对任意_SL2Z
  条件: (hc : IsCusp c 𝒮ℒ)
  证明: by
  refine ⟨fun hc _ hγ => by simpa using! hc _ hγ, fun h => ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! h γ rfl

Depends on / 依赖: IsBoundedAt, IsBoundedAt.smul_iff, isBoundedAt_infty_iff, isCusp_SL2Z_iff, smul_iff
-/
lemma isBoundedAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsBoundedAt c f k ↔ forall γ : SL(2, Int), mapGL Real γ • ∞ = c -> IsBoundedAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ => by simpa using! hc _ hγ, fun h => ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! h γ rfl

/--
lemma `isZeroAt_iff_forall_SL2Z` / 引理 `isZeroAt_iff_forall_SL2Z`

English:
lemma isZeroAt_iff_forall_SL2Z
  given: (hc : IsCusp c 𝒮ℒ)
  proof: by
  refine ⟨fun hc _ hγ => by simpa using! hc _ hγ, fun h => ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! h γ rfl

中文:
引理 isZeroAt_iff_对任意_SL2Z
  条件: (hc : IsCusp c 𝒮ℒ)
  证明: by
  refine ⟨fun hc _ hγ => by simpa using! hc _ hγ, fun h => ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! h γ rfl

Depends on / 依赖: IsZeroAt, IsZeroAt.smul_iff, isCusp_SL2Z_iff, isZeroAt_infty_iff, smul_iff
-/
lemma isZeroAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsZeroAt c f k ↔ forall γ : SL(2, Int), mapGL Real γ • ∞ = c -> IsZeroAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ => by simpa using! hc _ hγ, fun h => ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! h γ rfl

end SL2Z

end OnePoint
