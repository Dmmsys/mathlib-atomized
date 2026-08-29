/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
  `Function.Exact f g` says that `Set.range f = Set.preimage g {0}`

* For two maps `f : M → N` and `g : N → P`, with `One P`,
  `Function.MulExact f g` says that `Set.range f = Set.preimage g {1}`

* For additive maps `f : M →+ N` and `g : N →+ P`,
  `Exact f g` says that `range f = ker g`

* For multiplicative maps `f : M →* N` and `g : N →* P`,
  `MulExact f g` says that `range f = ker g`

* For linear maps `f : M →ₗ[R] N` and `g : N →ₗ[R] P`,
  `Exact f g` says that `range f = ker g`

## TODO :

* generalize to `SemilinearMap`, even `SemilinearMapClass`
-/

@[expose] public section

variable {R M M' N N' P P' : Type*}

namespace Function

variable (f : M -> N) (g : N -> P) (g' : P -> P')

/-- The maps `f` and `g` form an exact pair: `g y = 1` iff `y` belongs to the image of `f`. -/
@[to_additive /-- The maps `f` and `g` form an exact pair:
  `g y = 0` iff `y` belongs to the image of `f`. -/]
/--
Definition of `MulExact` / `MulExact` 的定义

English:
definition MulExact
  signature: [One P]
  body: forall y, g y = 1 ↔ y in Set.range f

中文:
定义 MulExact
  签名: [幺 P]
  定义体: forall y, g y = 1 ↔ y in Set.range f

Depends on / 依赖: Set.range
-/
def MulExact [One P] : Prop := forall y, g y = 1 ↔ y in Set.range f

variable {f g}

namespace MulExact

@[to_additive]
/--
lemma `apply_apply_eq_one` / 引理 `apply_apply_eq_one`

English:
lemma apply_apply_eq_one
  given: [One P] (h : MulExact f g) (x : M)
  proof: (h _).mpr Set.mem_range_self _

@[to_additive]

中文:
引理 apply_apply_eq_one
  条件: [幺 P] (h : MulExact f g) (x : M)
  证明: (h _).mpr Set.mem_range_self _

@[to_additive]

Depends on / 依赖: Set.mem_range_self, mem_range_self
-/
lemma apply_apply_eq_one [One P] (h : MulExact f g) (x : M) :
g (f x) = 1 := (h _).mpr Set.mem_range_self _

@[to_additive]
/--
lemma `comp_eq_one` / 引理 `comp_eq_one`

English:
lemma comp_eq_one
  given: [One P] (h : MulExact f g)
  statement: g.comp f = 1
  proof: funext h.apply_apply_eq_one

@[to_additive]

中文:
引理 comp_eq_one
  条件: [幺 P] (h : MulExact f g)
  结论: g.comp f = 1
  证明: funext h.apply_apply_eq_one

@[to_additive]

Depends on / 依赖: apply_apply_eq_one, h.apply_apply_eq_one
-/
lemma comp_eq_one [One P] (h : MulExact f g) : g.comp f = 1 :=
  funext h.apply_apply_eq_one

@[to_additive]
/--
lemma `of_comp_of_mem_range` / 引理 `of_comp_of_mem_range`

English:
lemma of_comp_of_mem_range
  statement: [One P] (h1 : g ∘ f = 1)
  proof: fun y => Iff.intro (h2 y)
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 1))).mpr (congrFun h1) y)

@[to_additive]

中文:
引理 of_comp_of_mem_range
  结论: [幺 P] (h1 : g ∘ f = 1)
  证明: fun y => Iff.intro (h2 y)
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 1))).mpr (congrFun h1) y)

@[to_additive]

Depends on / 依赖: Exists, Exists.rec, Iff.intro, forall_apply_eq_imp_iff
-/
lemma of_comp_of_mem_range [One P] (h1 : g ∘ f = 1)
    (h2 : forall x, g x = 1 -> x in Set.range f) : MulExact f g :=
fun y => Iff.intro (h2 y)
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 1))).mpr (congrFun h1) y)

@[to_additive]
/--
lemma `comp_injective` / 引理 `comp_injective`

English:
lemma comp_injective
  statement: [One P] [One P'] (mulExact : MulExact f g)
  proof: by
  intro x
.mp inj h0 ▸ H, ?_⟩ refine ⟨fun H => mulExact x
  intro H
  rw [Function.comp_apply]; rw [mulExact x |>.mpr H]; rw [h0]

@[to_additive]

中文:
引理 comp_injective
  结论: [幺 P] [幺 P'] (mulExact : MulExact f g)
  证明: by
  intro x
.mp inj h0 ▸ H, ?_⟩ refine ⟨fun H => mulExact x
  intro H
  rw [Function.comp_apply]; rw [mulExact x |>.mpr H]; rw [h0]

@[to_additive]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, mulExact
-/
lemma comp_injective [One P] [One P'] (mulExact : MulExact f g)
    (inj : Function.Injective g') (h0 : g' 1 = 1) :
    MulExact f (g' ∘ g) := by
  intro x
.mp inj h0 ▸ H, ?_⟩ refine ⟨fun H => mulExact x
  intro H
  rw [Function.comp_apply]; rw [mulExact x |>.mpr H]; rw [h0]

@[to_additive]
/--
lemma `of_comp_eq_one_of_ker_in_range` / 引理 `of_comp_eq_one_of_ker_in_range`

English:
lemma of_comp_eq_one_of_ker_in_range
  statement: [One P] (hc : g.comp f = 1)
  proof: fun y => ⟨hr y, fun ⟨x, hx⟩ => hx ▸ congrFun hc x⟩

中文:
引理 of_comp_eq_one_of_ker_in_range
  结论: [幺 P] (hc : g.comp f = 1)
  证明: fun y => ⟨hr y, fun ⟨x, hx⟩ => hx ▸ congrFun hc x⟩
-/
lemma of_comp_eq_one_of_ker_in_range [One P] (hc : g.comp f = 1)
    (hr : forall y, g y = 1 -> y in Set.range f) :
    MulExact f g :=
  fun y => ⟨hr y, fun ⟨x, hx⟩ => hx ▸ congrFun hc x⟩

/-- Two maps `f : M → N` and `g : N → P` are exact if and only if the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[One (Set.range g)]` (which is unlikely) this lemma
may not apply if the one of `Set.range g` is not definitionally equal to `⟨1, hg⟩`. -/
@[to_additive /-- Two maps `f : M → N` and `g : N → P` are exact if and only if the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[Zero (Set.range g)]` (which is unlikely) this lemma
may not apply if the zero of `Set.range g` is not definitionally equal to `⟨0, hg⟩`. -/]
/--
lemma `iff_rangeFactorization` / 引理 `iff_rangeFactorization`

English:
lemma iff_rangeFactorization
  given: [One P] (hg : 1 in Set.range g)
  proof: ⟨⟨1, hg⟩⟩
    MulExact f g ↔ MulExact ((↑) : Set.range f -> N) (Set.rangeFactorization g) := by
  let : One (Set.range g) := ⟨⟨1, hg⟩⟩
  have : ((1 : Set.range g) : P) = 1 := rfl
  simp [MulExact, Subtype.ext_iff, this]

中文:
引理 iff_rangeFactorization
  条件: [幺 P] (hg : 1 in 集合.range g)
  证明: ⟨⟨1, hg⟩⟩
    MulExact f g ↔ MulExact ((↑) : Set.range f -> N) (Set.rangeFactorization g) := by
  let : One (Set.range g) := ⟨⟨1, hg⟩⟩
  have : ((1 : Set.range g) : P) = 1 := rfl
  simp [MulExact, Subtype.ext_iff, this]
-/
lemma iff_rangeFactorization [One P] (hg : 1 in Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    MulExact f g ↔ MulExact ((↑) : Set.range f -> N) (Set.rangeFactorization g) := by
  let : One (Set.range g) := ⟨⟨1, hg⟩⟩
  have : ((1 : Set.range g) : P) = 1 := rfl
  simp [MulExact, Subtype.ext_iff, this]

/-- If two maps `f : M → N` and `g : N → P` are exact, then the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[One (Set.range g)]` (which is unlikely) this lemma
may not apply if the one of `Set.range g` is not definitionally equal to `⟨1, hg⟩`. -/
@[to_additive /-- If two maps `f : M → N` and `g : N → P` are exact, then the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[Zero (Set.range g)]` (which is unlikely) this lemma
may not apply if the zero of `Set.range g` is not definitionally equal to `⟨0, hg⟩`. -/]
/--
lemma `rangeFactorization` / 引理 `rangeFactorization`

English:
lemma rangeFactorization
  given: [One P] (h : MulExact f g) (hg : 1 in Set.range g)
  proof: ⟨⟨1, hg⟩⟩
    MulExact ((↑) : Set.range f -> N) (Set.rangeFactorization g) :=
  (iff_rangeFactorization hg).1 h

中文:
引理 rangeFactorization
  条件: [幺 P] (h : MulExact f g) (hg : 1 in 集合.range g)
  证明: ⟨⟨1, hg⟩⟩
    MulExact ((↑) : Set.range f -> N) (Set.rangeFactorization g) :=
  (iff_rangeFactorization hg).1 h
-/
lemma rangeFactorization [One P] (h : MulExact f g) (hg : 1 in Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    MulExact ((↑) : Set.range f -> N) (Set.rangeFactorization g) :=
  (iff_rangeFactorization hg).1 h

end MulExact

end Function

section MonoidHom

variable [Group M] [Group N] [Group P] {f : M ->* N} {g : N ->* P}

namespace MonoidHom

open Function

@[to_additive]
/--
lemma `mulExact_iff` / 引理 `mulExact_iff`

English:
lemma mulExact_iff
  proof: Iff.symm SetLike.ext_iff

@[to_additive]

中文:
引理 mulExact_iff
  证明: Iff.symm SetLike.ext_iff

@[to_additive]

Depends on / 依赖: Iff.symm, SetLike, SetLike.ext_iff, ext_iff
-/
lemma mulExact_iff :
    MulExact f g ↔ ker g = range f :=
  Iff.symm SetLike.ext_iff

@[to_additive]
/--
lemma `mulExact_of_comp_eq_one_of_ker_le_range` / 引理 `mulExact_of_comp_eq_one_of_ker_le_range`

English:
lemma mulExact_of_comp_eq_one_of_ker_le_range
  proof: MulExact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

@[to_additive]

中文:
引理 mulExact_of_comp_eq_one_of_ker_le_range
  证明: MulExact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, MulExact, MulExact.of_comp_of_mem_range, of_comp_of_mem_range
-/
lemma mulExact_of_comp_eq_one_of_ker_le_range
    (h1 : g.comp f = 1) (h2 : ker g <= range f) : MulExact f g :=
  MulExact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

@[to_additive]
/--
lemma `mulExact_of_comp_of_mem_range` / 引理 `mulExact_of_comp_of_mem_range`

English:
lemma mulExact_of_comp_of_mem_range
  proof: mulExact_of_comp_eq_one_of_ker_le_range h1 h2

中文:
引理 mulExact_of_comp_of_mem_range
  证明: mulExact_of_comp_eq_one_of_ker_le_range h1 h2

Depends on / 依赖: mulExact_of_comp_eq_one_of_ker_le_range
-/
lemma mulExact_of_comp_of_mem_range
    (h1 : g.comp f = 1) (h2 : forall x, g x = 1 -> x in range f) : MulExact f g :=
  mulExact_of_comp_eq_one_of_ker_le_range h1 h2

/-- When we have a commutative diagram from a sequence of two maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/
@[to_additive /-- When we have a commutative diagram from a sequence of two maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/]
/--
lemma `mulExact_iff_of_surjective_of_bijective_of_injective` / 引理 `mulExact_iff_of_surjective_of_bijective_of_injective`

English:
lemma mulExact_iff_of_surjective_of_bijective_of_injective
  proof: by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_one, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃]; rw [(h x₂).2 _]; rw [map_one]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_one])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, h.apply_apply_eq_one (τ₁ x₁), map_one]

中文:
引理 mulExact_iff_of_surjective_of_bijective_of_injective
  证明: by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_one, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃]; rw [(h x₂).2 _]; rw [map_one]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_one])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, h.apply_apply_eq_one (τ₁ x₁), map_one]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_one, replace
-/
lemma mulExact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommMonoid M₁] [CommMonoid M₂] [CommMonoid M₃]
    [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]
    (f : M₁ ->* M₂) (g : M₂ ->* M₃) (f' : N₁ ->* N₂) (g' : N₂ ->* N₃)
    (τ₁ : M₁ ->* N₁) (τ₂ : M₂ ->* N₂) (τ₃ : M₃ ->* N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
    (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    MulExact f g ↔ MulExact f' g' := by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_one, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃]; rw [(h x₂).2 _]; rw [map_one]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_one])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, h.apply_apply_eq_one (τ₁ x₁), map_one]

end MonoidHom

namespace Function.MulExact

open MonoidHom

@[to_additive]
/--
lemma `monoidHom_ker_eq` / 引理 `monoidHom_ker_eq`

English:
lemma monoidHom_ker_eq
  given: (hfg : MulExact f g)
  proof: SetLike.ext hfg

@[to_additive]

中文:
引理 monoidHom_ker_eq
  条件: (hfg : MulExact f g)
  证明: SetLike.ext hfg

@[to_additive]

Depends on / 依赖: SetLike, SetLike.ext
-/
lemma monoidHom_ker_eq (hfg : MulExact f g) :
    ker g = range f :=
  SetLike.ext hfg

@[to_additive]
/--
lemma `monoidHom_comp_eq_zero` / 引理 `monoidHom_comp_eq_zero`

English:
lemma monoidHom_comp_eq_zero
  given: (h : MulExact f g)
  statement: g.comp f = 1
  proof: DFunLike.coe_injective h.comp_eq_one

中文:
引理 monoidHom_comp_eq_zero
  条件: (h : MulExact f g)
  结论: g.comp f = 1
  证明: DFunLike.coe_injective h.comp_eq_one

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, comp_eq_one, h.comp_eq_one
-/
lemma monoidHom_comp_eq_zero (h : MulExact f g) : g.comp f = 1 :=
  DFunLike.coe_injective h.comp_eq_one

section

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ ->* X₂} {f₂₃ : X₂ ->* X₃} {g₁₂ : Y₁ ->* Y₂} {g₂₃ : Y₂ ->* Y₃}

@[to_additive]
/--
lemma `iff_of_ladder_mulEquiv` / 引理 `iff_of_ladder_mulEquiv`

English:
lemma iff_of_ladder_mulEquiv
  statement: (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
  proof: (mulExact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

@[to_additive]

中文:
引理 iff_of_ladder_mulEquiv
  结论: (comm₁₂ : g₁₂.comp e₁ = 幺半群态射.comp e₂ f₁₂)
  证明: (mulExact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

@[to_additive]

Depends on / 依赖: bijective, injective, mulExact_iff_of_surjective_of_bijective_of_injective, surjective
-/
lemma iff_of_ladder_mulEquiv (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) : MulExact g₁₂ g₂₃ ↔ MulExact f₁₂ f₂₃ :=
  (mulExact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

@[to_additive]
/--
lemma `of_ladder_mulEquiv_of_mulExact` / 引理 `of_ladder_mulEquiv_of_mulExact`

English:
lemma of_ladder_mulEquiv_of_mulExact
  statement: (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
  proof: (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).2 H

@[to_additive]

中文:
引理 of_ladder_mulEquiv_of_mulExact
  结论: (comm₁₂ : g₁₂.comp e₁ = 幺半群态射.comp e₂ f₁₂)
  证明: (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).2 H

@[to_additive]

Depends on / 依赖: iff_of_ladder_mulEquiv
-/
lemma of_ladder_mulEquiv_of_mulExact (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : MulExact f₁₂ f₂₃) : MulExact g₁₂ g₂₃ :=
  (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).2 H

@[to_additive]
/--
lemma `of_ladder_mulEquiv_of_mulExact'` / 引理 `of_ladder_mulEquiv_of_mulExact'`

English:
lemma of_ladder_mulEquiv_of_mulExact'
  statement: (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
  proof: (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).1 H

中文:
引理 of_ladder_mulEquiv_of_mulExact'
  结论: (comm₁₂ : g₁₂.comp e₁ = 幺半群态射.comp e₂ f₁₂)
  证明: (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).1 H

Depends on / 依赖: iff_of_ladder_mulEquiv
-/
lemma of_ladder_mulEquiv_of_mulExact' (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : MulExact g₁₂ g₂₃) : MulExact f₁₂ f₂₃ :=
  (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).1 H

end

/-- Two maps `f : M →* N` and `g : N →* P` are exact if and only if the induced maps
`MonoidHom.range f → N → MonoidHom.range g` are exact. -/
@[to_additive /-- Two maps `f : M →+ N` and `g : N →+ P` are exact if and only if the induced maps
`AddMonoidHom.range f → N → AddMonoidHom.range g` are exact. -/]
/--
lemma `iff_monoidHom_rangeRestrict` / 引理 `iff_monoidHom_rangeRestrict`

English:
lemma iff_monoidHom_rangeRestrict
  proof: iff_rangeFactorization (one_mem g.range)

@[to_additive]
alias ⟨monoidHom_rangeRestrict, _⟩ := iff_monoidHom_rangeRestrict

中文:
引理 iff_monoidHom_rangeRestrict
  证明: iff_rangeFactorization (one_mem g.range)

@[to_additive]
alias ⟨monoidHom_rangeRestrict, _⟩ := iff_monoidHom_rangeRestrict

Depends on / 依赖: g.range, iff_rangeFactorization, one_mem
-/
lemma iff_monoidHom_rangeRestrict :
    MulExact f g ↔ MulExact f.range.subtype g.rangeRestrict :=
  iff_rangeFactorization (one_mem g.range)

@[to_additive]
alias ⟨monoidHom_rangeRestrict, _⟩ := iff_monoidHom_rangeRestrict

end Function.MulExact

end MonoidHom

section LinearMap

open Function

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}

namespace LinearMap

/--
lemma `exact_iff` / 引理 `exact_iff`

English:
lemma exact_iff
  proof: Iff.symm SetLike.ext_iff

中文:
引理 exact_iff
  证明: Iff.symm SetLike.ext_iff

Depends on / 依赖: Iff.symm, SetLike, SetLike.ext_iff, ext_iff
-/
lemma exact_iff :
    Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm SetLike.ext_iff

/--
lemma `exact_of_comp_eq_zero_of_ker_le_range` / 引理 `exact_of_comp_eq_zero_of_ker_le_range`

English:
lemma exact_of_comp_eq_zero_of_ker_le_range
  proof: Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

中文:
引理 exact_of_comp_eq_zero_of_ker_le_range
  证明: Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

Depends on / 依赖: DFunLike, DFunLike.coe, Exact.of_comp_of_mem_range, of_comp_of_mem_range
-/
lemma exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g ∘ₗ f = 0) (h2 : ker g <= range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

/--
lemma `exact_of_comp_of_mem_range` / 引理 `exact_of_comp_of_mem_range`

English:
lemma exact_of_comp_of_mem_range
  proof: exact_of_comp_eq_zero_of_ker_le_range h1 h2

中文:
引理 exact_of_comp_of_mem_range
  证明: exact_of_comp_eq_zero_of_ker_le_range h1 h2

Depends on / 依赖: exact_of_comp_eq_zero_of_ker_le_range
-/
lemma exact_of_comp_of_mem_range
    (h1 : g ∘ₗ f = 0) (h2 : forall x, g x = 0 -> x in range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

section Ring

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

/--
lemma `exact_subtype_mkQ` / 引理 `exact_subtype_mkQ`

English:
lemma exact_subtype_mkQ
  given: (Q : Submodule R N)
  proof: by
  rw [exact_iff]; rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype Q]

中文:
引理 exact_subtype_mkQ
  条件: (Q : 子模 R N)
  证明: by
  rw [exact_iff]; rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype Q]

Depends on / 依赖: Submodule, Submodule.ker_mkQ, Submodule.range_subtype, exact_iff, ker_mkQ, range_subtype
-/
lemma exact_subtype_mkQ (Q : Submodule R N) :
    Exact (Submodule.subtype Q) (Submodule.mkQ Q) := by
  rw [exact_iff]; rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype Q]

/--
lemma `exact_map_mkQ_range` / 引理 `exact_map_mkQ_range`

English:
lemma exact_map_mkQ_range
  given: (f : M ->ₗ[R] N)
  proof: exact_iff.mpr Submodule.ker_mkQ _

中文:
引理 exact_map_mkQ_range
  条件: (f : M ->ₗ[R] N)
  证明: exact_iff.mpr Submodule.ker_mkQ _

Depends on / 依赖: Submodule, Submodule.ker_mkQ, exact_iff, exact_iff.mpr, ker_mkQ
-/
lemma exact_map_mkQ_range (f : M ->ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) :=
exact_iff.mpr Submodule.ker_mkQ _

/--
lemma `exact_subtype_ker_map` / 引理 `exact_subtype_ker_map`

English:
lemma exact_subtype_ker_map
  given: (g : N ->ₗ[R] P)
  proof: exact_iff.mpr (Submodule.range_subtype _).symm

@[simp]

中文:
引理 exact_subtype_ker_map
  条件: (g : N ->ₗ[R] P)
  证明: exact_iff.mpr (Submodule.range_subtype _).symm

@[simp]

Depends on / 依赖: Submodule, Submodule.range_subtype, exact_iff, exact_iff.mpr, range_subtype
-/
lemma exact_subtype_ker_map (g : N ->ₗ[R] P) :
    Exact (Submodule.subtype (ker g)) g :=
exact_iff.mpr (Submodule.range_subtype _).symm

@[simp]
/--
lemma `exact_zero_iff_injective` / 引理 `exact_zero_iff_injective`

English:
lemma exact_zero_iff_injective
  statement: {M N : Type*} (P : Type*)
  proof: by
  simp [← ker_eq_bot, exact_iff]

中文:
引理 exact_zero_iff_injective
  结论: {M N : 类型} (P : 类型)
  证明: by
  simp [← ker_eq_bot, exact_iff]

Depends on / 依赖: exact_iff, ker_eq_bot
-/
lemma exact_zero_iff_injective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M ->ₗ[R] N) :
    Function.Exact (0 : P ->ₗ[R] M) f ↔ Function.Injective f := by
  simp [← ker_eq_bot, exact_iff]

end Ring

@[simp]
/--
lemma `exact_zero_iff_surjective` / 引理 `exact_zero_iff_surjective`

English:
lemma exact_zero_iff_surjective
  statement: {M N : Type*} (P : Type*)
  proof: by
  simp [range_eq_top, exact_iff, eqComm]

中文:
引理 exact_zero_iff_surjective
  结论: {M N : 类型} (P : 类型)
  证明: by
  simp [range_eq_top, exact_iff, eqComm]

Depends on / 依赖: eqComm, exact_iff, range_eq_top
-/
lemma exact_zero_iff_surjective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M ->ₗ[R] N) :
    Function.Exact f (0 : N ->ₗ[R] P) ↔ Function.Surjective f := by
  simp [range_eq_top, exact_iff, eqComm]

end LinearMap

variable (f g) in
/--
lemma `LinearEquiv.conj_exact_iff_exact` / 引理 `LinearEquiv.conj_exact_iff_exact`

English:
lemma LinearEquiv.conj_exact_iff_exact
  given: (e : N ≃ₗ[R] N')
  proof: by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← Submodule.map_equiv_eq_comap_symm,
    LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

中文:
引理 线性等价.conj_exact_iff_exact
  条件: (e : N ≃ₗ[R] N')
  证明: by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← Submodule.map_equiv_eq_comap_symm,
    LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

Depends on / 依赖: LinearMap, LinearMap.exact_iff, LinearMap.ker_comp, LinearMap.range_comp, Submodule, Submodule.map_equiv_eq_comap_symm, Submodule.map_injective_of_injective, e.injective, eq_iff, exact_iff, injective, ker_comp, map_equiv_eq_comap_symm, map_injective_of_injective, range_comp, simp_rw
-/
lemma LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') :
    Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' ->ₗ[R] N)) ↔ Exact f g := by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← Submodule.map_equiv_eq_comap_symm,
    LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

variable (f g) in
/--
lemma `LinearEquiv.conj_symm_exact_iff_exact` / 引理 `LinearEquiv.conj_symm_exact_iff_exact`

English:
lemma LinearEquiv.conj_symm_exact_iff_exact
  given: (e : N' ≃ₗ[R] N)
  proof: LinearEquiv.conj_exact_iff_exact _ _ e.symm

中文:
引理 线性等价.conj_symm_exact_iff_exact
  条件: (e : N' ≃ₗ[R] N)
  证明: LinearEquiv.conj_exact_iff_exact _ _ e.symm

Depends on / 依赖: LinearEquiv, LinearEquiv.conj_exact_iff_exact, conj_exact_iff_exact, e.symm
-/
lemma LinearEquiv.conj_symm_exact_iff_exact (e : N' ≃ₗ[R] N) :
    Function.Exact (e.symm ∘ₗ f) (g ∘ₗ (e : N' ->ₗ[R] N)) ↔ Exact f g :=
  LinearEquiv.conj_exact_iff_exact _ _ e.symm

namespace Function

open LinearMap

/--
lemma `Exact.linearMap_ker_eq` / 引理 `Exact.linearMap_ker_eq`

English:
lemma Exact.linearMap_ker_eq
  given: (hfg : Exact f g)
  statement: ker g = range f
  proof: SetLike.ext hfg

中文:
引理 正合.linearMap_ker_eq
  条件: (hfg : 正合 f g)
  结论: ker g = range f
  证明: SetLike.ext hfg

Depends on / 依赖: SetLike, SetLike.ext
-/
lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

/--
lemma `Exact.linearMap_comp_eq_zero` / 引理 `Exact.linearMap_comp_eq_zero`

English:
lemma Exact.linearMap_comp_eq_zero
  given: (h : Exact f g)
  statement: g.comp f = 0
  proof: DFunLike.coe_injective h.comp_eq_zero

中文:
引理 正合.linearMap_comp_eq_zero
  条件: (h : 正合 f g)
  结论: g.comp f = 0
  证明: DFunLike.coe_injective h.comp_eq_zero

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, comp_eq_zero, h.comp_eq_zero
-/
lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

/--
lemma `Surjective.comp_exact_iff_exact` / 引理 `Surjective.comp_exact_iff_exact`

English:
lemma Surjective.comp_exact_iff_exact
  given: {p : M' ->ₗ[R] M} (h : Surjective p)
  proof: iff_of_eq forall_congr fun x =>
    congrArg (g x = 0 ↔ x in ·) (h.range_comp f)

中文:
引理 满射.comp_exact_iff_exact
  条件: {p : M' ->ₗ[R] M} (h : 满射 p)
  证明: iff_of_eq forall_congr fun x =>
    congrArg (g x = 0 ↔ x in ·) (h.range_comp f)

Depends on / 依赖: forall_congr, h.range_comp, iff_of_eq, range_comp
-/
lemma Surjective.comp_exact_iff_exact {p : M' ->ₗ[R] M} (h : Surjective p) :
    Exact (f ∘ₗ p) g ↔ Exact f g :=
iff_of_eq forall_congr fun x =>
    congrArg (g x = 0 ↔ x in ·) (h.range_comp f)

/--
lemma `_root_.LinearEquiv.precomp_exact_iff_exact` / 引理 `_root_.LinearEquiv.precomp_exact_iff_exact`

English:
lemma _root_.LinearEquiv.precomp_exact_iff_exact
  given: {e : M' ≃ₗ[R] M}
  proof: e.surjective.comp_exact_iff_exact

中文:
引理 _root_.线性等价.precomp_exact_iff_exact
  条件: {e : M' ≃ₗ[R] M}
  证明: e.surjective.comp_exact_iff_exact

Depends on / 依赖: comp_exact_iff_exact, e.surjective.comp_exact_iff_exact, surjective
-/
lemma _root_.LinearEquiv.precomp_exact_iff_exact {e : M' ≃ₗ[R] M} :
    Exact (f ∘ₗ (e : M' ->ₗ[R] M)) g ↔ Exact f g :=
  e.surjective.comp_exact_iff_exact

/--
lemma `Injective.comp_exact_iff_exact` / 引理 `Injective.comp_exact_iff_exact`

English:
lemma Injective.comp_exact_iff_exact
  given: {i : P ->ₗ[R] P'} (h : Injective i)
  proof: forall_congr' fun _ => iff_congr (map_eq_zero_iff _ h) Iff.rfl

中文:
引理 单射.comp_exact_iff_exact
  条件: {i : P ->ₗ[R] P'} (h : 单射 i)
  证明: forall_congr' fun _ => iff_congr (map_eq_zero_iff _ h) Iff.rfl

Depends on / 依赖: Iff.rfl, forall_congr, iff_congr, map_eq_zero_iff
-/
lemma Injective.comp_exact_iff_exact {i : P ->ₗ[R] P'} (h : Injective i) :
    Exact f (i ∘ₗ g) ↔ Exact f g :=
  forall_congr' fun _ => iff_congr (map_eq_zero_iff _ h) Iff.rfl

/--
lemma `_root_.LinearEquiv.postcomp_exact_iff_exact` / 引理 `_root_.LinearEquiv.postcomp_exact_iff_exact`

English:
lemma _root_.LinearEquiv.postcomp_exact_iff_exact
  given: {e : P ≃ₗ[R] P'}
  proof: e.injective.comp_exact_iff_exact

中文:
引理 _root_.线性等价.postcomp_exact_iff_exact
  条件: {e : P ≃ₗ[R] P'}
  证明: e.injective.comp_exact_iff_exact

Depends on / 依赖: comp_exact_iff_exact, e.injective.comp_exact_iff_exact, injective
-/
lemma _root_.LinearEquiv.postcomp_exact_iff_exact {e : P ≃ₗ[R] P'} :
    Exact f ((e : P ->ₗ[R] P') ∘ₗ g) ↔ Exact f g :=
  e.injective.comp_exact_iff_exact

namespace Exact

variable
    {f₁₂ : M ->ₗ[R] N} {f₂₃ : N ->ₗ[R] P} {g₁₂ : M' ->ₗ[R] N'}
    {g₂₃ : N' ->ₗ[R] P'} {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₃ : P ≃ₗ[R] P'}

/--
lemma `iff_of_ladder_linearEquiv` / 引理 `iff_of_ladder_linearEquiv`

English:
lemma iff_of_ladder_linearEquiv
  proof: iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)

中文:
引理 iff_of_ladder_linearEquiv
  证明: iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom, congr_arg, iff_of_ladder_addEquiv, toAddEquiv, toAddMonoidHom
-/
lemma iff_of_ladder_linearEquiv
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ :=
  iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)

/--
lemma `of_ladder_linearEquiv_of_exact` / 引理 `of_ladder_linearEquiv_of_exact`

English:
lemma of_ladder_linearEquiv_of_exact
  proof: by
  rwa [iff_of_ladder_linearEquiv h₁₂ h₂₃]

中文:
引理 of_ladder_linearEquiv_of_exact
  证明: by
  rwa [iff_of_ladder_linearEquiv h₁₂ h₂₃]

Depends on / 依赖: iff_of_ladder_linearEquiv
-/
lemma of_ladder_linearEquiv_of_exact
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃)
    (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ := by
  rwa [iff_of_ladder_linearEquiv h₁₂ h₂₃]

/--
lemma `iff_linearMap_rangeRestrict` / 引理 `iff_linearMap_rangeRestrict`

English:
lemma iff_linearMap_rangeRestrict
  proof: iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

中文:
引理 iff_linearMap_rangeRestrict
  证明: iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

Depends on / 依赖: LinearMap, LinearMap.range, iff_rangeFactorization, zero_mem
-/
lemma iff_linearMap_rangeRestrict :
    Exact f g ↔ Exact (LinearMap.range f).subtype g.rangeRestrict :=
  iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

end Exact

end Function

end LinearMap

namespace Function

section split

variable [Semiring R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
variable {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}

open LinearMap

set_option backward.isDefEq.respectTransparency.types false in
/-- Given an exact sequence `0 → M → N → P`, giving a section `P → N` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
/--
Definition of `Exact.splitSurjectiveEquiv` / `Exact.splitSurjectiveEquiv` 的定义

English:
definition Exact.splitSurjectiveEquiv
  signature: (h : Function.Exact f g) (hf : Function.Injective f)
  body: by
  refine
  { toFun := fun l => ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e => ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : forall x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : forall x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

中文:
定义 正合.splitSurjectiveEquiv
  签名: (h : 函数.正合 f g) (hf : 函数.单射 f)
  定义体: by
  refine
  { toFun := fun l => ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e => ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : forall x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : forall x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.congr_fun, Prod.ext, add_apply, add_left_inj, coe_comp, comp_apply, comp_eq_zero, congr_fun, fst_apply, h.comp_eq_zero, invFun, left_inv, ofBijective, right_inv, snd_apply
-/
def Exact.splitSurjectiveEquiv (h : Function.Exact f g) (hf : Function.Injective f) :
    { l // g ∘ₗ l = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l => ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e => ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : forall x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : forall x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Given an exact sequence `M → N → P → 0`, giving a retraction `N → M` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
/--
Definition of `Exact.splitInjectiveEquiv` / `Exact.splitInjectiveEquiv` 的定义

English:
definition Exact.splitInjectiveEquiv
  body: by
  refine
  { toFun := fun l => ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e => ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : forall x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      rw [← sub_eq_zero]; rw [← hz]; rw [← h₁ z]; rw [hz]; rw [map_sub]; rw [e.1]; rw [sub_self]; rw [map_zero]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : forall x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp

中文:
定义 正合.splitInjectiveEquiv
  定义体: by
  refine
  { toFun := fun l => ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e => ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : forall x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      rw [← sub_eq_zero]; rw [← hz]; rw [← h₁ z]; rw [hz]; rw [map_sub]; rw [e.1]; rw [sub_self]; rw [map_zero]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : forall x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp

Depends on / 依赖: Function, Function.prod_apply, LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.congr_fun, LinearMap.prod_apply, Prod.mk.injEq, comp_eq_zero, congr_fun, h.comp_eq_zero, invFun, left_inv, ofBijective, prod_apply, right_inv, sub_eq_zero
-/
def Exact.splitInjectiveEquiv
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    { l // l ∘ₗ f = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l => ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e => ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : forall x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      rw [← sub_eq_zero]; rw [← hz]; rw [← h₁ z]; rw [hz]; rw [map_sub]; rw [e.1]; rw [sub_self]; rw [map_zero]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : forall x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : forall x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp

/--
theorem `Exact.split_tfae'` / 定理 `Exact.split_tfae'`

English:
theorem Exact.split_tfae'
  given: (h : Function.Exact f g)
  proof: by
  tfae_have 1 -> 3
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 -> 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 -> 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 -> 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

中文:
定理 正合.split_tfae'
  条件: (h : 函数.正合 f g)
  证明: by
  tfae_have 1 -> 3
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 -> 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 -> 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 -> 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

Depends on / 依赖: Function, Function.Injective, Function.Surjective, Injective, LinearMap, LinearMap.inl_injective, Prod.snd_surjective.comp, Surjective, e.surjective, e.symm.injective.comp, h.splitInjectiveEquiv, h.splitSurjectiveEquiv, injective, inl_injective, snd_surjective, splitInjectiveEquiv, splitSurjectiveEquiv, surjective, tfae_have
-/
theorem Exact.split_tfae' (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ exists l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ exists l, l ∘ₗ f = LinearMap.id,
      exists e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 -> 3
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 -> 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 -> 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 -> 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

/--
theorem `Exact.split_tfae` / 定理 `Exact.split_tfae`

English:
theorem Exact.split_tfae
  proof: by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

中文:
定理 正合.split_tfae
  证明: by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

Depends on / 依赖: h.splitInjectiveEquiv, h.splitSurjectiveEquiv, nonempty_congr, splitInjectiveEquiv, splitSurjectiveEquiv, tfae_finish, tfae_have
-/
theorem Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      exists l, g ∘ₗ l = LinearMap.id,
      exists l, l ∘ₗ f = LinearMap.id,
      exists e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

end split

section Prod

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/--
lemma `Exact.inr_fst` / 引理 `Exact.inr_fst`

English:
lemma Exact.inr_fst
  statement: Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N)
  proof: by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

中文:
引理 正合.inr_fst
  结论: 函数.正合 (线性映射.inr R M N) (线性映射.fst R M N)
  证明: by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

Depends on / 依赖: LinearMap, LinearMap.coe_inr, LinearMap.fst_apply, Prod.mk.injEq, Set.mem_range, coe_inr, eq_comm, exists_eq_right, fst_apply, mem_range
-/
lemma Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

/--
lemma `Exact.inl_snd` / 引理 `Exact.inl_snd`

English:
lemma Exact.inl_snd
  statement: Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N)
  proof: by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

中文:
引理 正合.inl_snd
  结论: 函数.正合 (线性映射.inl R M N) (线性映射.snd R M N)
  证明: by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

Depends on / 依赖: LinearMap, LinearMap.coe_inl, LinearMap.snd_apply, Prod.mk.injEq, Set.mem_range, coe_inl, eq_comm, exists_eq_left, mem_range, snd_apply
-/
lemma Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

end Prod

end Function

section Ring

open LinearMap Submodule

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}

namespace Function

/--
lemma `Exact.exact_mapQ_iff` / 引理 `Exact.exact_mapQ_iff`

English:
lemma Exact.exact_mapQ_iff
  proof: by
  rw [exact_iff]; rw [← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp]; rw [range_liftQ]; rw [liftQ_mkQ]; rw [ker_comp]; rw [range_comp]; rw [comap_map_eq]; rw [ker_mkQ]; rw [ker_mkQ]; rw [← hfg.linearMap_ker_eq]; rw [sup_comm]; rw [← (sup_le hqr (ker_le_comap g)).ge_iff_eq']; rw [← comap_map_eq]; rw [← map_le_iff_le_comap]; rw [map_comap_eq]

中文:
引理 正合.exact_mapQ_iff
  证明: by
  rw [exact_iff]; rw [← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp]; rw [range_liftQ]; rw [liftQ_mkQ]; rw [ker_comp]; rw [range_comp]; rw [comap_map_eq]; rw [ker_mkQ]; rw [ker_mkQ]; rw [← hfg.linearMap_ker_eq]; rw [sup_comm]; rw [← (sup_le hqr (ker_le_comap g)).ge_iff_eq']; rw [← comap_map_eq]; rw [← map_le_iff_le_comap]; rw [map_comap_eq]

Depends on / 依赖: comap_injective_of_surjective, comap_map_eq, eq_iff, exact_iff, ge_iff_eq, hfg.linearMap_ker_eq, ker_comp, ker_le_comap, ker_mkQ, liftQ_mkQ, linearMap_ker_eq, map_comap_eq, map_le_iff_le_comap, mkQ_surjective, range_comp, range_liftQ, sup_comm, sup_le
-/
lemma Exact.exact_mapQ_iff
    (hfg : Exact f g) {p q r} (hpq : p <= comap f q) (hqr : q <= comap g r) :
    Exact (mapQ p q f hpq) (mapQ q r g hqr) ↔ range g ⊓ r <= map g q := by
  rw [exact_iff]; rw [← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp]; rw [range_liftQ]; rw [liftQ_mkQ]; rw [ker_comp]; rw [range_comp]; rw [comap_map_eq]; rw [ker_mkQ]; rw [ker_mkQ]; rw [← hfg.linearMap_ker_eq]; rw [sup_comm]; rw [← (sup_le hqr (ker_le_comap g)).ge_iff_eq']; rw [← comap_map_eq]; rw [← map_le_iff_le_comap]; rw [map_comap_eq]

end Function

namespace LinearMap

/--
lemma `exact_iff_of_surjective_of_bijective_of_injective` / 引理 `exact_iff_of_surjective_of_bijective_of_injective`

English:
lemma exact_iff_of_surjective_of_bijective_of_injective
  proof: AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

中文:
引理 exact_iff_of_surjective_of_bijective_of_injective
  证明: AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

Depends on / 依赖: AddMonoidHom, AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective, DFunLike, DFunLike.congr_fun, congr_fun, exact_iff_of_surjective_of_bijective_of_injective, f.toAddMonoidHom, g.toAddMonoidHom, toAddMonoidHom
-/
lemma exact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f : M₁ ->ₗ[R] M₂) (g : M₂ ->ₗ[R] M₃) (f' : N₁ ->ₗ[R] N₂) (g' : N₂ ->ₗ[R] N₃)
    (τ₁ : M₁ ->ₗ[R] N₁) (τ₂ : M₂ ->ₗ[R] N₂) (τ₃ : M₃ ->ₗ[R] N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.Exact f g ↔ Function.Exact f' g' :=
  AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

/--
lemma `surjective_range_liftQ` / 引理 `surjective_range_liftQ`

English:
lemma surjective_range_liftQ
  given: (h : range f <= ker g) (hg : Function.Surjective g)
  proof: by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩

中文:
引理 surjective_range_liftQ
  条件: (h : range f <= ker g) (hg : 函数.满射 g)
  证明: by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk
-/
lemma surjective_range_liftQ (h : range f <= ker g) (hg : Function.Surjective g) :
    Function.Surjective ((range f).liftQ g h) := by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩

/--
lemma `ker_eq_bot_range_liftQ_iff` / 引理 `ker_eq_bot_range_liftQ_iff`

English:
lemma ker_eq_bot_range_liftQ_iff
  given: (h : range f <= ker g)
  proof: by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

中文:
引理 ker_eq_bot_range_liftQ_iff
  条件: (h : range f <= ker g)
  证明: by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk, Submodule.Quotient.mk_surjective, Submodule.ext_iff, Submodule.mem_bot, ext_iff, mem_bot, mem_ker, mem_range, mk_surjective
-/
lemma ker_eq_bot_range_liftQ_iff (h : range f <= ker g) :
    ker ((range f).liftQ g h) = ⊥ ↔ ker g = range f := by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `injective_range_liftQ_of_exact` / 引理 `injective_range_liftQ_of_exact`

English:
lemma injective_range_liftQ_of_exact
  given: (h : Function.Exact f g)
  proof: by
  simpa only [← LinearMap.ker_eq_bot, ker_eq_bot_range_liftQ_iff, exact_iff] using h

中文:
引理 injective_range_liftQ_of_exact
  条件: (h : 函数.正合 f g)
  证明: by
  simpa only [← LinearMap.ker_eq_bot, ker_eq_bot_range_liftQ_iff, exact_iff] using h

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, exact_iff, ker_eq_bot, ker_eq_bot_range_liftQ_iff
-/
lemma injective_range_liftQ_of_exact (h : Function.Exact f g) :
    Function.Injective ((range f).liftQ g (h · |>.mpr)) := by
  simpa only [← LinearMap.ker_eq_bot, ker_eq_bot_range_liftQ_iff, exact_iff] using h

/--
lemma `surjective_iff_eq_zero_of_exact` / 引理 `surjective_iff_eq_zero_of_exact`

English:
lemma surjective_iff_eq_zero_of_exact
  given: (h : Function.Exact f g)
  proof: by
  rw [← LinearMap.ker_eq_top]; rw [h.linearMap_ker_eq]; rw [LinearMap.range_eq_top]

中文:
引理 surjective_iff_eq_zero_of_exact
  条件: (h : 函数.正合 f g)
  证明: by
  rw [← LinearMap.ker_eq_top]; rw [h.linearMap_ker_eq]; rw [LinearMap.range_eq_top]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_top, LinearMap.range_eq_top, h.linearMap_ker_eq, ker_eq_top, linearMap_ker_eq, range_eq_top
-/
lemma surjective_iff_eq_zero_of_exact (h : Function.Exact f g) :
    Function.Surjective f ↔ g = 0 := by
  rw [← LinearMap.ker_eq_top]; rw [h.linearMap_ker_eq]; rw [LinearMap.range_eq_top]

/--
lemma `injective_iff_eq_zero_of_exact` / 引理 `injective_iff_eq_zero_of_exact`

English:
lemma injective_iff_eq_zero_of_exact
  given: (h : Function.Exact f g)
  proof: by
  rw [← LinearMap.ker_eq_bot]; rw [h.linearMap_ker_eq]; rw [LinearMap.range_eq_bot]

中文:
引理 injective_iff_eq_zero_of_exact
  条件: (h : 函数.正合 f g)
  证明: by
  rw [← LinearMap.ker_eq_bot]; rw [h.linearMap_ker_eq]; rw [LinearMap.range_eq_bot]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, LinearMap.range_eq_bot, h.linearMap_ker_eq, ker_eq_bot, linearMap_ker_eq, range_eq_bot
-/
lemma injective_iff_eq_zero_of_exact (h : Function.Exact f g) :
    Function.Injective g ↔ f = 0 := by
  rw [← LinearMap.ker_eq_bot]; rw [h.linearMap_ker_eq]; rw [LinearMap.range_eq_bot]

end LinearMap

/-- The linear equivalence `(N ⧸ LinearMap.range f) ≃ₗ[A] P` associated to
an exact sequence `M → N → P → 0` of `R`-modules. -/
@[simps! apply]
/--
Definition of `Function.Exact.linearEquivOfSurjective` / `Function.Exact.linearEquivOfSurjective` 的定义

English:
definition Function.Exact.linearEquivOfSurjective
  signature: (h : Function.Exact f g)
  body: LinearEquiv.ofBijective ((LinearMap.range f).liftQ g (h · |>.mpr))
    ⟨LinearMap.injective_range_liftQ_of_exact h, LinearMap.surjective_range_liftQ _ hg⟩

中文:
定义 函数.正合.linearEquivOfSurjective
  签名: (h : 函数.正合 f g)
  定义体: LinearEquiv.ofBijective ((LinearMap.range f).liftQ g (h · |>.mpr))
    ⟨LinearMap.injective_range_liftQ_of_exact h, LinearMap.surjective_range_liftQ _ hg⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.injective_range_liftQ_of_exact, LinearMap.range, LinearMap.surjective_range_liftQ, injective_range_liftQ_of_exact, ofBijective, surjective_range_liftQ
-/
noncomputable def Function.Exact.linearEquivOfSurjective (h : Function.Exact f g)
    (hg : Function.Surjective g) : (N ⧸ LinearMap.range f) ≃ₗ[R] P :=
  LinearEquiv.ofBijective ((LinearMap.range f).liftQ g (h · |>.mpr))
    ⟨LinearMap.injective_range_liftQ_of_exact h, LinearMap.surjective_range_liftQ _ hg⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Function.Exact.linearEquivOfSurjective_symm_apply` / 引理 `Function.Exact.linearEquivOfSurjective_symm_apply`

English:
lemma Function.Exact.linearEquivOfSurjective_symm_apply
  statement: (h : Function.Exact f g)
  proof: by
  simp [LinearEquiv.symm_apply_eq]

中文:
引理 函数.正合.linearEquivOfSurjective_symm_apply
  结论: (h : 函数.正合 f g)
  证明: by
  simp [LinearEquiv.symm_apply_eq]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
lemma Function.Exact.linearEquivOfSurjective_symm_apply (h : Function.Exact f g)
    (hg : Function.Surjective g) (x : N) :
    (h.linearEquivOfSurjective hg).symm (g x) = Submodule.Quotient.mk x := by
  simp [LinearEquiv.symm_apply_eq]

end Ring
