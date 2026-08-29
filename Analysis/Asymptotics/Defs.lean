/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Asymptotics

We introduce these relations:

* `IsBigOWith c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =Θ[l] g` : "f is big O of g along l and vice versa";
* `f =o[l] g` : "f is little o of g along l";
* `f ~[l] g` : `f` and `g` are equivalent, i.e., `f - g =o[l] g`.

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed is that there is a norm associated
with these types, and it is the norm that is compared asymptotically.

The relation `IsBigOWith c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `IsBigO` and `IsLittleO`. Usually proofs outside of this file should use
`IsBigO` instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (fun x ↦ ‖f x‖) =O[l] (fun x ↦ ‖g x‖)`,

and similarly for `IsLittleO`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ Tendsto (fun x ↦ f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)

Sometimes Landau notation may be embedded in more complex expressions, such as
$f(n) = n ^ {1 + O(g(n))}$. This can be expressed using the existential pattern, for example:

  `∃ (e : ℕ → ℝ) (he : e =O[l] g), f =ᶠ[l] fun n ↦ n ^ (1 + e n)`.

-/

set_option linter.style.longFile 1600

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Set Topology Filter NNReal

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable {S : Type*} [NormedRing S] [NormMulClass S]
variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : Real} {f : α -> E} {g : α -> F} {k : α -> G}
variable {f' : α -> E'} {g' : α -> F'} {k' : α -> G'}
variable {f'' : α -> E''} {g'' : α -> F''} {k'' : α -> G''}
variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


/-- This version of the Landau notation `IsBigOWith C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `IsBigO` instead of this relation. -/
irreducible_def IsBigOWith (c : Real) (l : Filter α) (f : α -> E) (g : α -> F) : Prop :=
  forallᶠ x in l, ‖f x‖ <= c * ‖g x‖

/--
theorem `isBigOWith_iff` / 定理 `isBigOWith_iff`

English:
theorem isBigOWith_iff
  statement: IsBigOWith c l f g ↔ forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
  proof: by rw [IsBigOWith_def]

alias ⟨IsBigOWith.bound, IsBigOWith.of_bound⟩ := isBigOWith_iff

中文:
定理 isBigOWith_iff
  结论: IsBigOWith c l f g ↔ 对任意ᶠ x in l, ‖f x‖ <= c * ‖g x‖
  证明: by rw [IsBigOWith_def]

alias ⟨IsBigOWith.bound, IsBigOWith.of_bound⟩ := isBigOWith_iff

Depends on / 依赖: IsBigOWith_def
-/
theorem isBigOWith_iff : IsBigOWith c l f g ↔ forallᶠ x in l, ‖f x‖ <= c * ‖g x‖ := by rw [IsBigOWith_def]

alias ⟨IsBigOWith.bound, IsBigOWith.of_bound⟩ := isBigOWith_iff

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsBigO (l : Filter α) (f : α -> E) (g : α -> F) : Prop :=
  exists c : Real, IsBigOWith c l f g

@[inherit_doc]
notation:100 f " =O[" l "] " g:100 => IsBigO l f g

/--
theorem `isBigO_iff_isBigOWith` / 定理 `isBigO_iff_isBigOWith`

English:
theorem isBigO_iff_isBigOWith
  statement: f =O[l] g ↔ exists c : Real, IsBigOWith c l f g
  proof: by rw [IsBigO_def]

中文:
定理 isBigO_iff_isBigOWith
  结论: f =O[l] g ↔ 存在 c : 实数, IsBigOWith c l f g
  证明: by rw [IsBigO_def]

Depends on / 依赖: IsBigO_def
-/
theorem isBigO_iff_isBigOWith : f =O[l] g ↔ exists c : Real, IsBigOWith c l f g := by rw [IsBigO_def]

/--
theorem `isBigO_iff` / 定理 `isBigO_iff`

English:
theorem isBigO_iff
  statement: f =O[l] g ↔ exists c : Real, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
  proof: by
  simp only [IsBigO_def, IsBigOWith_def]

中文:
定理 isBigO_iff
  结论: f =O[l] g ↔ 存在 c : 实数, 对任意ᶠ x in l, ‖f x‖ <= c * ‖g x‖
  证明: by
  simp only [IsBigO_def, IsBigOWith_def]

Depends on / 依赖: IsBigOWith_def, IsBigO_def
-/
theorem isBigO_iff : f =O[l] g ↔ exists c : Real, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖ := by
  simp only [IsBigO_def, IsBigOWith_def]

/--
theorem `isBigO_iff'` / 定理 `isBigO_iff'`

English:
theorem isBigO_iff'
  given: {g : α -> E'''}
  proof: by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    filter_upwards [hc] with x hx
    apply hx.trans
    gcongr
    exact le_max_left _ _
  case mpr =>
    rw [isBigO_iff]
    ob

中文:
定理 isBigO_iff'
  条件: {g : α -> E'''}
  证明: by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    filter_upwards [hc] with x hx
    apply hx.trans
    gcongr
    exact le_max_left _ _
  case mpr =>
    rw [isBigO_iff]
    ob

Depends on / 依赖: filter_upwards, hx.trans, isBigO_iff, le_max_left, le_max_right, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem isBigO_iff' {g : α -> E'''} :
    f =O[l] g ↔ exists c > 0, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    filter_upwards [hc] with x hx
    apply hx.trans
    gcongr
    exact le_max_left _ _
  case mpr =>
    rw [isBigO_iff]
    obtain ⟨c, ⟨_, hc⟩⟩ := h
    exact ⟨c, hc⟩

/--
theorem `isBigO_iff''` / 定理 `isBigO_iff''`

English:
theorem isBigO_iff''
  given: {g : α -> E'''}
  proof: by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff'] at h
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [inv_mul_le_iff₀ (by positivity)]
  case mpr =>
    rw [isBigO_iff']
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
  

中文:
定理 isBigO_iff''
  条件: {g : α -> E'''}
  证明: by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff'] at h
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [inv_mul_le_iff₀ (by positivity)]
  case mpr =>
    rw [isBigO_iff']
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
  

Depends on / 依赖: filter_upwards, hc_pos, inv_inv, isBigO_iff
-/
theorem isBigO_iff'' {g : α -> E'''} :
    f =O[l] g ↔ exists c > 0, forallᶠ x in l, c * ‖f x‖ <= ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff'] at h
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [inv_mul_le_iff₀ (by positivity)]
  case mpr =>
    rw [isBigO_iff']
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [← inv_inv c, inv_mul_le_iff₀ (by positivity)] at hx

/--
theorem `IsBigO.of_bound` / 定理 `IsBigO.of_bound`

English:
theorem IsBigO.of_bound
  given: (c : Real) (h : forallᶠ x in l, ‖f x‖ <= c * ‖g x‖)
  statement: f =O[l] g
  proof: isBigO_iff.2 ⟨c, h⟩

中文:
定理 IsBigO.of_bound
  条件: (c : 实数) (h : 对任意ᶠ x in l, ‖f x‖ <= c * ‖g x‖)
  结论: f =O[l] g
  证明: isBigO_iff.2 ⟨c, h⟩

Depends on / 依赖: isBigO_iff
-/
theorem IsBigO.of_bound (c : Real) (h : forallᶠ x in l, ‖f x‖ <= c * ‖g x‖) : f =O[l] g :=
  isBigO_iff.2 ⟨c, h⟩

/--
theorem `IsBigO.of_bound'` / 定理 `IsBigO.of_bound'`

English:
theorem IsBigO.of_bound'
  given: (h : forallᶠ x in l, ‖f x‖ <= ‖g x‖)
  statement: f =O[l] g
  proof: .of_bound 1 by simpa only [one_mul] using h

中文:
定理 IsBigO.of_bound'
  条件: (h : 对任意ᶠ x in l, ‖f x‖ <= ‖g x‖)
  结论: f =O[l] g
  证明: .of_bound 1 by simpa only [one_mul] using h

Depends on / 依赖: of_bound, one_mul
-/
theorem IsBigO.of_bound' (h : forallᶠ x in l, ‖f x‖ <= ‖g x‖) : f =O[l] g :=
.of_bound 1 by simpa only [one_mul] using h

/--
theorem `IsBigO.bound` / 定理 `IsBigO.bound`

English:
theorem IsBigO.bound
  statement: f =O[l] g -> exists c : Real, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
  proof: isBigO_iff.1

中文:
定理 IsBigO.bound
  结论: f =O[l] g -> 存在 c : 实数, 对任意ᶠ x in l, ‖f x‖ <= c * ‖g x‖
  证明: isBigO_iff.1

Depends on / 依赖: isBigO_iff
-/
theorem IsBigO.bound : f =O[l] g -> exists c : Real, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖ :=
  isBigO_iff.1

/--
theorem `IsBigO.of_norm_eventuallyLE` / 定理 `IsBigO.of_norm_eventuallyLE`

English:
theorem IsBigO.of_norm_eventuallyLE
  given: {g : α -> Real} (h : (‖f ·‖) <=ᶠ[l] g)
  statement: f =O[l] g
  proof: .of_bound' h.mono fun _ h => h.trans le_abs_self _

中文:
定理 IsBigO.of_norm_eventuallyLE
  条件: {g : α -> 实数} (h : (‖f ·‖) <=ᶠ[l] g)
  结论: f =O[l] g
  证明: .of_bound' h.mono fun _ h => h.trans le_abs_self _

Depends on / 依赖: h.mono, h.trans, le_abs_self, of_bound
-/
theorem IsBigO.of_norm_eventuallyLE {g : α -> Real} (h : (‖f ·‖) <=ᶠ[l] g) : f =O[l] g :=
.of_bound' h.mono fun _ h => h.trans le_abs_self _

/--
theorem `IsBigO.of_norm_le` / 定理 `IsBigO.of_norm_le`

English:
theorem IsBigO.of_norm_le
  given: {g : α -> Real} (h : forall x, ‖f x‖ <= g x)
  statement: f =O[l] g
  proof: .of_norm_eventuallyLE .of_forall h

中文:
定理 IsBigO.of_norm_le
  条件: {g : α -> 实数} (h : 对任意 x, ‖f x‖ <= g x)
  结论: f =O[l] g
  证明: .of_norm_eventuallyLE .of_forall h

Depends on / 依赖: of_forall, of_norm_eventuallyLE
-/
theorem IsBigO.of_norm_le {g : α -> Real} (h : forall x, ‖f x‖ <= g x) : f =O[l] g :=
.of_norm_eventuallyLE .of_forall h

/--
Definition of `IsTheta` / `IsTheta` 的定义

English:
definition IsTheta
  signature: (l : Filter α) (f : α -> E) (g : α -> F)
  body: IsBigO l f g ∧ IsBigO l g f

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g

中文:
定义 IsTheta
  签名: (l : 滤子 α) (f : α -> E) (g : α -> F)
  定义体: IsBigO l f g ∧ IsBigO l g f

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g

Depends on / 依赖: IsBigO
-/
def IsTheta (l : Filter α) (f : α -> E) (g : α -> F) : Prop :=
  IsBigO l f g ∧ IsBigO l g f

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g

/--
theorem `IsBigO.antisymm` / 定理 `IsBigO.antisymm`

English:
theorem IsBigO.antisymm
  given: (h₁ : f =O[l] g) (h₂ : g =O[l] f)
  statement: f =Θ[l] g
  proof: ⟨h₁, h₂⟩

中文:
定理 IsBigO.antisymm
  条件: (h₁ : f =O[l] g) (h₂ : g =O[l] f)
  结论: f =Θ[l] g
  证明: ⟨h₁, h₂⟩
-/
theorem IsBigO.antisymm (h₁ : f =O[l] g) (h₂ : g =O[l] f) : f =Θ[l] g :=
  ⟨h₁, h₂⟩

/--
lemma `IsTheta.isBigO` / 引理 `IsTheta.isBigO`

English:
lemma IsTheta.isBigO
  given: (h : f =Θ[l] g)
  statement: f =O[l] g
  proof: h.1

中文:
引理 IsTheta.isBigO
  条件: (h : f =Θ[l] g)
  结论: f =O[l] g
  证明: h.1
-/
lemma IsTheta.isBigO (h : f =Θ[l] g) : f =O[l] g := h.1

/--
lemma `IsTheta.isBigO_symm` / 引理 `IsTheta.isBigO_symm`

English:
lemma IsTheta.isBigO_symm
  given: (h : f =Θ[l] g)
  statement: g =O[l] f
  proof: h.2

中文:
引理 IsTheta.isBigO_symm
  条件: (h : f =Θ[l] g)
  结论: g =O[l] f
  证明: h.2
-/
lemma IsTheta.isBigO_symm (h : f =Θ[l] g) : g =O[l] f := h.2

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α -> E) (g : α -> F) : Prop :=
  forall ⦃c : Real⦄, 0 < c -> IsBigOWith c l f g

@[inherit_doc]
notation:100 f " =o[" l "] " g:100 => IsLittleO l f g

/--
theorem `isLittleO_iff_forall_isBigOWith` / 定理 `isLittleO_iff_forall_isBigOWith`

English:
theorem isLittleO_iff_forall_isBigOWith
  statement: f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> IsBigOWith c l f g
  proof: by
  rw [IsLittleO_def]

alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith

中文:
定理 isLittleO_iff_对任意_isBigOWith
  结论: f =o[l] g ↔ 对任意 ⦃c : 实数⦄, 0 < c -> IsBigOWith c l f g
  证明: by
  rw [IsLittleO_def]

alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith

Depends on / 依赖: IsLittleO_def
-/
theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> IsBigOWith c l f g := by
  rw [IsLittleO_def]

alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith

/--
theorem `isLittleO_iff` / 定理 `isLittleO_iff`

English:
theorem isLittleO_iff
  statement: f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
  proof: by
  simp only [IsLittleO_def, IsBigOWith_def]

alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff

中文:
定理 isLittleO_iff
  结论: f =o[l] g ↔ 对任意 ⦃c : 实数⦄, 0 < c -> 对任意ᶠ x in l, ‖f x‖ <= c * ‖g x‖
  证明: by
  simp only [IsLittleO_def, IsBigOWith_def]

alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff

Depends on / 依赖: IsBigOWith_def, IsLittleO_def
-/
theorem isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖ := by
  simp only [IsLittleO_def, IsBigOWith_def]

alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff

/--
theorem `IsLittleO.def` / 定理 `IsLittleO.def`

English:
theorem IsLittleO.def
  given: (h : f =o[l] g) (hc : 0 < c)
  statement: forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
  proof: isLittleO_iff.1 h hc

中文:
定理 IsLittleO.def
  条件: (h : f =o[l] g) (hc : 0 < c)
  结论: 对任意ᶠ x in l, ‖f x‖ <= c * ‖g x‖
  证明: isLittleO_iff.1 h hc

Depends on / 依赖: isLittleO_iff
-/
theorem IsLittleO.def (h : f =o[l] g) (hc : 0 < c) : forallᶠ x in l, ‖f x‖ <= c * ‖g x‖ :=
  isLittleO_iff.1 h hc

/--
theorem `IsLittleO.def'` / 定理 `IsLittleO.def'`

English:
theorem IsLittleO.def'
  given: (h : f =o[l] g) (hc : 0 < c)
  statement: IsBigOWith c l f g
  proof: isBigOWith_iff.2 isLittleO_iff.1 h hc

中文:
定理 IsLittleO.def'
  条件: (h : f =o[l] g) (hc : 0 < c)
  结论: IsBigOWith c l f g
  证明: isBigOWith_iff.2 isLittleO_iff.1 h hc

Depends on / 依赖: isBigOWith_iff, isLittleO_iff
-/
theorem IsLittleO.def' (h : f =o[l] g) (hc : 0 < c) : IsBigOWith c l f g :=
isBigOWith_iff.2 isLittleO_iff.1 h hc

/--
theorem `IsLittleO.eventuallyLE` / 定理 `IsLittleO.eventuallyLE`

English:
theorem IsLittleO.eventuallyLE
  given: (h : f =o[l] g)
  statement: forallᶠ x in l, ‖f x‖ <= ‖g x‖
  proof: by
  simpa using h.def zero_lt_one

中文:
定理 IsLittleO.eventuallyLE
  条件: (h : f =o[l] g)
  结论: 对任意ᶠ x in l, ‖f x‖ <= ‖g x‖
  证明: by
  simpa using h.def zero_lt_one

Depends on / 依赖: h.def, zero_lt_one
-/
theorem IsLittleO.eventuallyLE (h : f =o[l] g) : forallᶠ x in l, ‖f x‖ <= ‖g x‖ := by
  simpa using h.def zero_lt_one

/--
theorem `IsLittleO.eventuallyLT_norm_of_eventually_pos` / 定理 `IsLittleO.eventuallyLT_norm_of_eventually_pos`

English:
theorem IsLittleO.eventuallyLT_norm_of_eventually_pos
  given: (h : f =o[l] g) (hg : forallᶠ x in l, 0 < ‖g x‖)
  proof: by
  refine ((h.def (show 0 < 2⁻¹ by simp)).and hg).mono fun x ⟨hx₁, hx₂⟩ => hx₁.trans_lt ?_
  rw [mul_lt_iff_lt_one_left hx₂]
  norm_num

中文:
定理 IsLittleO.eventuallyLT_norm_of_eventually_pos
  条件: (h : f =o[l] g) (hg : 对任意ᶠ x in l, 0 < ‖g x‖)
  证明: by
  refine ((h.def (show 0 < 2⁻¹ by simp)).and hg).mono fun x ⟨hx₁, hx₂⟩ => hx₁.trans_lt ?_
  rw [mul_lt_iff_lt_one_left hx₂]
  norm_num

Depends on / 依赖: h.def, mul_lt_iff_lt_one_left, trans_lt
-/
theorem IsLittleO.eventuallyLT_norm_of_eventually_pos (h : f =o[l] g) (hg : forallᶠ x in l, 0 < ‖g x‖) :
    forallᶠ x in l, ‖f x‖ < ‖g x‖ := by
  refine ((h.def (show 0 < 2⁻¹ by simp)).and hg).mono fun x ⟨hx₁, hx₂⟩ => hx₁.trans_lt ?_
  rw [mul_lt_iff_lt_one_left hx₂]
  norm_num

/--
Definition of `IsEquivalent` / `IsEquivalent` 的定义

English:
definition IsEquivalent
  signature: (l : Filter α) (u v : α -> E')
  body: (u - v) =o[l] v

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

中文:
定义 IsEquivalent
  签名: (l : 滤子 α) (u v : α -> E')
  定义体: (u - v) =o[l] v

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v
-/
def IsEquivalent (l : Filter α) (u v : α -> E') :=
  (u - v) =o[l] v

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

end Defs



/--
theorem `IsBigOWith.isBigO` / 定理 `IsBigOWith.isBigO`

English:
theorem IsBigOWith.isBigO
  given: (h : IsBigOWith c l f g)
  statement: f =O[l] g
  proof: by rw [IsBigO_def]; exact ⟨c, h⟩

中文:
定理 IsBigOWith.isBigO
  条件: (h : IsBigOWith c l f g)
  结论: f =O[l] g
  证明: by rw [IsBigO_def]; exact ⟨c, h⟩

Depends on / 依赖: IsBigO_def
-/
theorem IsBigOWith.isBigO (h : IsBigOWith c l f g) : f =O[l] g := by rw [IsBigO_def]; exact ⟨c, h⟩

/--
theorem `IsLittleO.isBigOWith` / 定理 `IsLittleO.isBigOWith`

English:
theorem IsLittleO.isBigOWith
  given: (hgf : f =o[l] g)
  statement: IsBigOWith 1 l f g
  proof: hgf.def' zero_lt_one

中文:
定理 IsLittleO.isBigOWith
  条件: (hgf : f =o[l] g)
  结论: IsBigOWith 1 l f g
  证明: hgf.def' zero_lt_one

Depends on / 依赖: hgf.def, zero_lt_one
-/
theorem IsLittleO.isBigOWith (hgf : f =o[l] g) : IsBigOWith 1 l f g :=
  hgf.def' zero_lt_one

/--
theorem `IsLittleO.isBigO` / 定理 `IsLittleO.isBigO`

English:
theorem IsLittleO.isBigO
  given: (hgf : f =o[l] g)
  statement: f =O[l] g
  proof: hgf.isBigOWith.isBigO

中文:
定理 IsLittleO.isBigO
  条件: (hgf : f =o[l] g)
  结论: f =O[l] g
  证明: hgf.isBigOWith.isBigO

Depends on / 依赖: hgf.isBigOWith.isBigO, isBigO, isBigOWith
-/
theorem IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.isBigOWith.isBigO

/--
theorem `IsBigO.isBigOWith` / 定理 `IsBigO.isBigOWith`

English:
theorem IsBigO.isBigOWith
  statement: f =O[l] g -> exists c : Real, IsBigOWith c l f g
  proof: isBigO_iff_isBigOWith.1

中文:
定理 IsBigO.isBigOWith
  结论: f =O[l] g -> 存在 c : 实数, IsBigOWith c l f g
  证明: isBigO_iff_isBigOWith.1

Depends on / 依赖: isBigO_iff_isBigOWith
-/
theorem IsBigO.isBigOWith : f =O[l] g -> exists c : Real, IsBigOWith c l f g :=
  isBigO_iff_isBigOWith.1

/--
theorem `IsBigOWith.weaken` / 定理 `IsBigOWith.weaken`

English:
theorem IsBigOWith.weaken
  given: (h : IsBigOWith c l f g') (hc : c <= c')
  statement: IsBigOWith c' l f g'
  proof: IsBigOWith.of_bound
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ <= c * ‖g' x‖ := hx
        _ <= _ := by gcongr

中文:
定理 IsBigOWith.weaken
  条件: (h : IsBigOWith c l f g') (hc : c <= c')
  结论: IsBigOWith c' l f g'
  证明: IsBigOWith.of_bound
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ <= c * ‖g' x‖ := hx
        _ <= _ := by gcongr

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, h.bound, mem_of_superset, of_bound
-/
theorem IsBigOWith.weaken (h : IsBigOWith c l f g') (hc : c <= c') : IsBigOWith c' l f g' :=
IsBigOWith.of_bound
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ <= c * ‖g' x‖ := hx
        _ <= _ := by gcongr

/--
theorem `IsBigOWith.exists_pos` / 定理 `IsBigOWith.exists_pos`

English:
theorem IsBigOWith.exists_pos
  given: (h : IsBigOWith c l f g')
  proof: ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken le_max_left c 1⟩

中文:
定理 IsBigOWith.存在_pos
  条件: (h : IsBigOWith c l f g')
  证明: ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken le_max_left c 1⟩

Depends on / 依赖: h.weaken, le_max_left, le_max_right, lt_of_lt_of_le, weaken, zero_lt_one
-/
theorem IsBigOWith.exists_pos (h : IsBigOWith c l f g') :
    exists c' > 0, IsBigOWith c' l f g' :=
⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken le_max_left c 1⟩

/--
theorem `IsBigO.exists_pos` / 定理 `IsBigO.exists_pos`

English:
theorem IsBigO.exists_pos
  given: (h : f =O[l] g')
  statement: exists c > 0, IsBigOWith c l f g'
  proof: let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_pos

中文:
定理 IsBigO.存在_pos
  条件: (h : f =O[l] g')
  结论: 存在 c > 0, IsBigOWith c l f g'
  证明: let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_pos

Depends on / 依赖: exists_pos, h.isBigOWith, hc.exists_pos, isBigOWith
-/
theorem IsBigO.exists_pos (h : f =O[l] g') : exists c > 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_pos

/--
theorem `IsBigOWith.exists_nonneg` / 定理 `IsBigOWith.exists_nonneg`

English:
theorem IsBigOWith.exists_nonneg
  given: (h : IsBigOWith c l f g')
  proof: let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩

中文:
定理 IsBigOWith.存在_nonneg
  条件: (h : IsBigOWith c l f g')
  证明: let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩

Depends on / 依赖: exists_pos, h.exists_pos, le_of_lt
-/
theorem IsBigOWith.exists_nonneg (h : IsBigOWith c l f g') :
    exists c' >= 0, IsBigOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩

/--
theorem `IsBigO.exists_nonneg` / 定理 `IsBigO.exists_nonneg`

English:
theorem IsBigO.exists_nonneg
  given: (h : f =O[l] g')
  statement: exists c >= 0, IsBigOWith c l f g'
  proof: let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_nonneg

中文:
定理 IsBigO.存在_nonneg
  条件: (h : f =O[l] g')
  结论: 存在 c >= 0, IsBigOWith c l f g'
  证明: let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_nonneg

Depends on / 依赖: exists_nonneg, h.isBigOWith, hc.exists_nonneg, isBigOWith
-/
theorem IsBigO.exists_nonneg (h : f =O[l] g') : exists c >= 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_nonneg

/--
theorem `isBigO_iff_eventually_isBigOWith` / 定理 `isBigO_iff_eventually_isBigOWith`

English:
theorem isBigO_iff_eventually_isBigOWith
  statement: f =O[l] g' ↔ forallᶠ c in atTop, IsBigOWith c l f g'
  proof: isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

中文:
定理 isBigO_iff_eventually_isBigOWith
  结论: f =O[l] g' ↔ 对任意ᶠ c in atTop, IsBigOWith c l f g'
  证明: isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

Depends on / 依赖: h.exists, hc.weaken, isBigO_iff_isBigOWith, isBigO_iff_isBigOWith.trans, mem_atTop_sets, weaken
-/
theorem isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ forallᶠ c in atTop, IsBigOWith c l f g' :=
  isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

/--
theorem `isBigO_iff_eventually` / 定理 `isBigO_iff_eventually`

English:
theorem isBigO_iff_eventually
  statement: f =O[l] g' ↔ forallᶠ c in atTop, forallᶠ x in l, ‖f x‖ <= c * ‖g' x‖
  proof: isBigO_iff_eventually_isBigOWith.trans by simp only [IsBigOWith_def]

中文:
定理 isBigO_iff_eventually
  结论: f =O[l] g' ↔ 对任意ᶠ c in atTop, 对任意ᶠ x in l, ‖f x‖ <= c * ‖g' x‖
  证明: isBigO_iff_eventually_isBigOWith.trans by simp only [IsBigOWith_def]

Depends on / 依赖: IsBigOWith_def, isBigO_iff_eventually_isBigOWith, isBigO_iff_eventually_isBigOWith.trans
-/
theorem isBigO_iff_eventually : f =O[l] g' ↔ forallᶠ c in atTop, forallᶠ x in l, ‖f x‖ <= c * ‖g' x‖ :=
isBigO_iff_eventually_isBigOWith.trans by simp only [IsBigOWith_def]

/--
theorem `IsBigO.exists_mem_basis` / 定理 `IsBigO.exists_mem_basis`

English:
theorem IsBigO.exists_mem_basis
  statement: {ι} {p : ι -> Prop} {s : ι -> Set α} (h : f =O[l] g')
  proof: flip Exists.imp h.exists_pos fun c h => by
    simpa only [isBigOWith_iff, hb.eventually_iff, exists_prop] using h

中文:
定理 IsBigO.存在_mem_basis
  结论: {ι} {p : ι -> 命题} {s : ι -> 集合 α} (h : f =O[l] g')
  证明: flip Exists.imp h.exists_pos fun c h => by
    simpa only [isBigOWith_iff, hb.eventually_iff, exists_prop] using h

Depends on / 依赖: Exists, Exists.imp, eventually_iff, exists_pos, exists_prop, h.exists_pos, hb.eventually_iff, isBigOWith_iff
-/
theorem IsBigO.exists_mem_basis {ι} {p : ι -> Prop} {s : ι -> Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) :
    exists c > 0, exists i : ι, p i ∧ forall x in s i, ‖f x‖ <= c * ‖g' x‖ :=
  flip Exists.imp h.exists_pos fun c h => by
    simpa only [isBigOWith_iff, hb.eventually_iff, exists_prop] using h

/--
theorem `isBigOWith_inv` / 定理 `isBigOWith_inv`

English:
theorem isBigOWith_inv
  given: (hc : 0 < c)
  statement: IsBigOWith c⁻¹ l f g ↔ forallᶠ x in l, c * ‖f x‖ <= ‖g x‖
  proof: by
  simp only [IsBigOWith_def, ← div_eq_inv_mul, le_div_iff₀' hc]

中文:
定理 isBigOWith_inv
  条件: (hc : 0 < c)
  结论: IsBigOWith c⁻¹ l f g ↔ 对任意ᶠ x in l, c * ‖f x‖ <= ‖g x‖
  证明: by
  simp only [IsBigOWith_def, ← div_eq_inv_mul, le_div_iff₀' hc]

Depends on / 依赖: IsBigOWith_def, div_eq_inv_mul
-/
theorem isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ forallᶠ x in l, c * ‖f x‖ <= ‖g x‖ := by
  simp only [IsBigOWith_def, ← div_eq_inv_mul, le_div_iff₀' hc]

-- We prove this lemma with strange assumptions to get two lemmas below automatically
/--
theorem `isLittleO_iff_nat_mul_le_aux` / 定理 `isLittleO_iff_nat_mul_le_aux`

English:
theorem isLittleO_iff_nat_mul_le_aux
  given: (h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <= ‖g x‖)
  proof: by
  constructor
  · rintro H (_ | n)
    · refine (H.def one_pos).mono fun x h₀' => ?_
      rw [Nat.cast_zero]; rw [zero_mul]
      refine h₀.elim (fun hf => (hf x).trans ?_) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : Real) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (isBigO

中文:
定理 isLittleO_iff_nat_mul_le_aux
  条件: (h₀ : (对任意 x, 0 <= ‖f x‖) ∨ 对任意 x, 0 <= ‖g x‖)
  证明: by
  constructor
  · rintro H (_ | n)
    · refine (H.def one_pos).mono fun x h₀' => ?_
      rw [Nat.cast_zero]; rw [zero_mul]
      refine h₀.elim (fun hf => (hf x).trans ?_) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : Real) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (isBigO

Depends on / 依赖: H.def, Nat.cast_pos, Nat.cast_zero, bound.mono, cast_pos, cast_zero, exists_nat_gt, inv_pos, isBigOWith_inv, isLittleO_iff, n.succ, n.succ_pos, one_mul, one_pos, succ_pos, zero_mul
-/
theorem isLittleO_iff_nat_mul_le_aux (h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <= ‖g x‖) :
    f =o[l] g ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖f x‖ <= ‖g x‖ := by
  constructor
  · rintro H (_ | n)
    · refine (H.def one_pos).mono fun x h₀' => ?_
      rw [Nat.cast_zero]; rw [zero_mul]
      refine h₀.elim (fun hf => (hf x).trans ?_) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : Real) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (isBigOWith_inv this).1 (H.def' <| inv_pos.2 this)
  · refine fun H => isLittleO_iff.2 fun ε ε0 => ?_
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : Real) < n := (inv_pos.2 ε0).trans hn
    refine ((isBigOWith_inv hn₀).2 (H n)).bound.mono fun x hfg => ?_
    refine hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le₀ ε0 hn.le) ?_)
    refine h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) ?_) fun h => h x
    exact inv_pos.2 hn₀

/--
theorem `isLittleO_iff_nat_mul_le` / 定理 `isLittleO_iff_nat_mul_le`

English:
theorem isLittleO_iff_nat_mul_le
  statement: f =o[l] g' ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖f x‖ <= ‖g' x‖
  proof: isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)

中文:
定理 isLittleO_iff_nat_mul_le
  结论: f =o[l] g' ↔ 对任意 n : 自然数, 对任意ᶠ x in l, ↑n * ‖f x‖ <= ‖g' x‖
  证明: isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)

Depends on / 依赖: Or.inr, isLittleO_iff_nat_mul_le_aux, norm_nonneg
-/
theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖f x‖ <= ‖g' x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)

/--
theorem `isLittleO_iff_nat_mul_le'` / 定理 `isLittleO_iff_nat_mul_le'`

English:
theorem isLittleO_iff_nat_mul_le'
  statement: f' =o[l] g ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖f' x‖ <= ‖g x‖
  proof: isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)

中文:
定理 isLittleO_iff_nat_mul_le'
  结论: f' =o[l] g ↔ 对任意 n : 自然数, 对任意ᶠ x in l, ↑n * ‖f' x‖ <= ‖g x‖
  证明: isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)

Depends on / 依赖: Or.inl, isLittleO_iff_nat_mul_le_aux, norm_nonneg
-/
theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖f' x‖ <= ‖g x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)

/-! ### Subsingleton -/


@[nontriviality]
/--
theorem `isLittleO_of_subsingleton` / 定理 `isLittleO_of_subsingleton`

English:
theorem isLittleO_of_subsingleton
  given: [Subsingleton E']
  statement: f' =o[l] g'
  proof: IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality]

中文:
定理 isLittleO_of_subsingleton
  条件: [子单例 E']
  结论: f' =o[l] g'
  证明: IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality]

Depends on / 依赖: IsLittleO, IsLittleO.of_bound, Subsingleton, Subsingleton.elim, hc.le, mul_nonneg, of_bound
-/
theorem isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality]
/--
theorem `isBigO_of_subsingleton` / 定理 `isBigO_of_subsingleton`

English:
theorem isBigO_of_subsingleton
  given: [Subsingleton E']
  statement: f' =O[l] g'
  proof: isLittleO_of_subsingleton.isBigO

中文:
定理 isBigO_of_subsingleton
  条件: [子单例 E']
  结论: f' =O[l] g'
  证明: isLittleO_of_subsingleton.isBigO

Depends on / 依赖: isBigO, isLittleO_of_subsingleton, isLittleO_of_subsingleton.isBigO
-/
theorem isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isLittleO_of_subsingleton.isBigO

section congr

variable {f₁ f₂ : α -> E} {g₁ g₂ : α -> F}



/--
theorem `isBigOWith_congr` / 定理 `isBigOWith_congr`

English:
theorem isBigOWith_congr
  given: (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  proof: by
  simp only [IsBigOWith_def]
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁]; rw [e₂]

中文:
定理 isBigOWith_congr
  条件: (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  证明: by
  simp only [IsBigOWith_def]
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁]; rw [e₂]

Depends on / 依赖: Filter, Filter.eventually_congr, IsBigOWith_def, eventually_congr, filter_upwards
-/
theorem isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂ := by
  simp only [IsBigOWith_def]
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁]; rw [e₂]

/--
theorem `IsBigOWith.congr'` / 定理 `IsBigOWith.congr'`

English:
theorem IsBigOWith.congr'
  statement: (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
  proof: (isBigOWith_congr hc hf hg).mp h

中文:
定理 IsBigOWith.congr'
  结论: (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
  证明: (isBigOWith_congr hc hf hg).mp h

Depends on / 依赖: isBigOWith_congr
-/
theorem IsBigOWith.congr' (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₂ l f₂ g₂ :=
  (isBigOWith_congr hc hf hg).mp h

/--
theorem `IsBigOWith.congr` / 定理 `IsBigOWith.congr`

English:
theorem IsBigOWith.congr
  statement: (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : forall x, f₁ x = f₂ x)
  proof: h.congr' hc (univ_mem' hf) (univ_mem' hg)

中文:
定理 IsBigOWith.congr
  结论: (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : 对任意 x, f₁ x = f₂ x)
  证明: h.congr' hc (univ_mem' hf) (univ_mem' hg)

Depends on / 依赖: h.congr, univ_mem
-/
theorem IsBigOWith.congr (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : forall x, f₁ x = f₂ x)
    (hg : forall x, g₁ x = g₂ x) : IsBigOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)

/--
theorem `IsBigOWith.congr_left` / 定理 `IsBigOWith.congr_left`

English:
theorem IsBigOWith.congr_left
  given: (h : IsBigOWith c l f₁ g) (hf : forall x, f₁ x = f₂ x)
  proof: h.congr rfl hf fun _ => rfl

中文:
定理 IsBigOWith.congr_left
  条件: (h : IsBigOWith c l f₁ g) (hf : 对任意 x, f₁ x = f₂ x)
  证明: h.congr rfl hf fun _ => rfl

Depends on / 依赖: h.congr
-/
theorem IsBigOWith.congr_left (h : IsBigOWith c l f₁ g) (hf : forall x, f₁ x = f₂ x) :
    IsBigOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl

/--
theorem `IsBigOWith.congr_right` / 定理 `IsBigOWith.congr_right`

English:
theorem IsBigOWith.congr_right
  given: (h : IsBigOWith c l f g₁) (hg : forall x, g₁ x = g₂ x)
  proof: h.congr rfl (fun _ => rfl) hg

中文:
定理 IsBigOWith.congr_right
  条件: (h : IsBigOWith c l f g₁) (hg : 对任意 x, g₁ x = g₂ x)
  证明: h.congr rfl (fun _ => rfl) hg

Depends on / 依赖: h.congr
-/
theorem IsBigOWith.congr_right (h : IsBigOWith c l f g₁) (hg : forall x, g₁ x = g₂ x) :
    IsBigOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg

/--
theorem `IsBigOWith.congr_const` / 定理 `IsBigOWith.congr_const`

English:
theorem IsBigOWith.congr_const
  given: (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂)
  statement: IsBigOWith c₂ l f g
  proof: h.congr hc (fun _ => rfl) fun _ => rfl

中文:
定理 IsBigOWith.congr_const
  条件: (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂)
  结论: IsBigOWith c₂ l f g
  证明: h.congr hc (fun _ => rfl) fun _ => rfl

Depends on / 依赖: h.congr
-/
theorem IsBigOWith.congr_const (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂) : IsBigOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl

/--
theorem `isBigO_congr` / 定理 `isBigO_congr`

English:
theorem isBigO_congr
  given: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  statement: f₁ =O[l] g₁ ↔ f₂ =O[l] g₂
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun c => isBigOWith_congr rfl hf hg

中文:
定理 isBigO_congr
  条件: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  结论: f₁ =O[l] g₁ ↔ f₂ =O[l] g₂
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun c => isBigOWith_congr rfl hf hg

Depends on / 依赖: IsBigO_def, exists_congr, isBigOWith_congr
-/
theorem isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  simp only [IsBigO_def]
  exact exists_congr fun c => isBigOWith_congr rfl hf hg

/--
theorem `IsBigO.congr'` / 定理 `IsBigO.congr'`

English:
theorem IsBigO.congr'
  given: (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  statement: f₂ =O[l] g₂
  proof: (isBigO_congr hf hg).mp h

中文:
定理 IsBigO.congr'
  条件: (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  结论: f₂ =O[l] g₂
  证明: (isBigO_congr hf hg).mp h

Depends on / 依赖: isBigO_congr
-/
theorem IsBigO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isBigO_congr hf hg).mp h

/--
theorem `IsBigO.congr` / 定理 `IsBigO.congr`

English:
theorem IsBigO.congr
  given: (h : f₁ =O[l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x)
  proof: h.congr' (univ_mem' hf) (univ_mem' hg)

中文:
定理 IsBigO.congr
  条件: (h : f₁ =O[l] g₁) (hf : 对任意 x, f₁ x = f₂ x) (hg : 对任意 x, g₁ x = g₂ x)
  证明: h.congr' (univ_mem' hf) (univ_mem' hg)

Depends on / 依赖: h.congr, univ_mem
-/
theorem IsBigO.congr (h : f₁ =O[l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x) :
    f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

/--
theorem `IsBigO.congr_left` / 定理 `IsBigO.congr_left`

English:
theorem IsBigO.congr_left
  given: (h : f₁ =O[l] g) (hf : forall x, f₁ x = f₂ x)
  statement: f₂ =O[l] g
  proof: h.congr hf fun _ => rfl

中文:
定理 IsBigO.congr_left
  条件: (h : f₁ =O[l] g) (hf : 对任意 x, f₁ x = f₂ x)
  结论: f₂ =O[l] g
  证明: h.congr hf fun _ => rfl

Depends on / 依赖: h.congr
-/
theorem IsBigO.congr_left (h : f₁ =O[l] g) (hf : forall x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl

/--
theorem `IsBigO.congr_right` / 定理 `IsBigO.congr_right`

English:
theorem IsBigO.congr_right
  given: (h : f =O[l] g₁) (hg : forall x, g₁ x = g₂ x)
  statement: f =O[l] g₂
  proof: h.congr (fun _ => rfl) hg

中文:
定理 IsBigO.congr_right
  条件: (h : f =O[l] g₁) (hg : 对任意 x, g₁ x = g₂ x)
  结论: f =O[l] g₂
  证明: h.congr (fun _ => rfl) hg

Depends on / 依赖: h.congr
-/
theorem IsBigO.congr_right (h : f =O[l] g₁) (hg : forall x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg

/--
theorem `isLittleO_congr` / 定理 `isLittleO_congr`

English:
theorem isLittleO_congr
  given: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  statement: f₁ =o[l] g₁ ↔ f₂ =o[l] g₂
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => isBigOWith_congr (Eq.refl c) hf hg

中文:
定理 isLittleO_congr
  条件: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  结论: f₁ =o[l] g₁ ↔ f₂ =o[l] g₂
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => isBigOWith_congr (Eq.refl c) hf hg

Depends on / 依赖: Eq.refl, IsLittleO_def, isBigOWith_congr
-/
theorem isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => isBigOWith_congr (Eq.refl c) hf hg

/--
theorem `IsLittleO.congr'` / 定理 `IsLittleO.congr'`

English:
theorem IsLittleO.congr'
  given: (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  statement: f₂ =o[l] g₂
  proof: (isLittleO_congr hf hg).mp h

中文:
定理 IsLittleO.congr'
  条件: (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  结论: f₂ =o[l] g₂
  证明: (isLittleO_congr hf hg).mp h

Depends on / 依赖: isLittleO_congr
-/
theorem IsLittleO.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isLittleO_congr hf hg).mp h

/--
theorem `IsLittleO.congr` / 定理 `IsLittleO.congr`

English:
theorem IsLittleO.congr
  given: (h : f₁ =o[l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x)
  proof: h.congr' (univ_mem' hf) (univ_mem' hg)

中文:
定理 IsLittleO.congr
  条件: (h : f₁ =o[l] g₁) (hf : 对任意 x, f₁ x = f₂ x) (hg : 对任意 x, g₁ x = g₂ x)
  证明: h.congr' (univ_mem' hf) (univ_mem' hg)

Depends on / 依赖: h.congr, univ_mem
-/
theorem IsLittleO.congr (h : f₁ =o[l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

/--
theorem `IsLittleO.congr_left` / 定理 `IsLittleO.congr_left`

English:
theorem IsLittleO.congr_left
  given: (h : f₁ =o[l] g) (hf : forall x, f₁ x = f₂ x)
  statement: f₂ =o[l] g
  proof: h.congr hf fun _ => rfl

中文:
定理 IsLittleO.congr_left
  条件: (h : f₁ =o[l] g) (hf : 对任意 x, f₁ x = f₂ x)
  结论: f₂ =o[l] g
  证明: h.congr hf fun _ => rfl

Depends on / 依赖: h.congr
-/
theorem IsLittleO.congr_left (h : f₁ =o[l] g) (hf : forall x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl

/--
theorem `IsLittleO.congr_right` / 定理 `IsLittleO.congr_right`

English:
theorem IsLittleO.congr_right
  given: (h : f =o[l] g₁) (hg : forall x, g₁ x = g₂ x)
  statement: f =o[l] g₂
  proof: h.congr (fun _ => rfl) hg

@[trans]

中文:
定理 IsLittleO.congr_right
  条件: (h : f =o[l] g₁) (hg : 对任意 x, g₁ x = g₂ x)
  结论: f =o[l] g₂
  证明: h.congr (fun _ => rfl) hg

@[trans]

Depends on / 依赖: h.congr
-/
theorem IsLittleO.congr_right (h : f =o[l] g₁) (hg : forall x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg

@[trans]
/--
theorem `_root_.Filter.EventuallyEq.trans_isBigO` / 定理 `_root_.Filter.EventuallyEq.trans_isBigO`

English:
theorem _root_.Filter.EventuallyEq.trans_isBigO
  statement: {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
  proof: h.congr' hf.symm EventuallyEq.rfl

中文:
定理 _root_.滤子.EventuallyEq.trans_isBigO
  结论: {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
  证明: h.congr' hf.symm EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h.congr, hf.symm
-/
theorem _root_.Filter.EventuallyEq.trans_isBigO {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl

/--
Instance `transEventuallyEqIsBigO` / 实例 `transEventuallyEqIsBigO`

English:
instance transEventuallyEqIsBigO
  signature: :
  body: Filter.EventuallyEq.trans_isBigO

@[trans]

中文:
实例 transEventuallyEqIsBigO
  签名: :
  定义体: Filter.EventuallyEq.trans_isBigO

@[trans]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.trans_isBigO, trans_isBigO
-/
instance transEventuallyEqIsBigO :
    @Trans (α -> E) (α -> E) (α -> F) (· =ᶠ[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := Filter.EventuallyEq.trans_isBigO

@[trans]
/--
theorem `_root_.Filter.EventuallyEq.trans_isLittleO` / 定理 `_root_.Filter.EventuallyEq.trans_isLittleO`

English:
theorem _root_.Filter.EventuallyEq.trans_isLittleO
  statement: {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
  proof: h.congr' hf.symm EventuallyEq.rfl

中文:
定理 _root_.滤子.EventuallyEq.trans_isLittleO
  结论: {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
  证明: h.congr' hf.symm EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h.congr, hf.symm
-/
theorem _root_.Filter.EventuallyEq.trans_isLittleO {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl

/--
Instance `transEventuallyEqIsLittleO` / 实例 `transEventuallyEqIsLittleO`

English:
instance transEventuallyEqIsLittleO
  signature: :
  body: Filter.EventuallyEq.trans_isLittleO

@[trans]

中文:
实例 transEventuallyEqIsLittleO
  签名: :
  定义体: Filter.EventuallyEq.trans_isLittleO

@[trans]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.trans_isLittleO, trans_isLittleO
-/
instance transEventuallyEqIsLittleO :
    @Trans (α -> E) (α -> E) (α -> F) (· =ᶠ[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Filter.EventuallyEq.trans_isLittleO

@[trans]
/--
theorem `IsBigO.trans_eventuallyEq` / 定理 `IsBigO.trans_eventuallyEq`

English:
theorem IsBigO.trans_eventuallyEq
  given: {f : α -> E} {g₁ g₂ : α -> F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂)
  proof: h.congr' EventuallyEq.rfl hg

中文:
定理 IsBigO.trans_eventuallyEq
  条件: {f : α -> E} {g₁ g₂ : α -> F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂)
  证明: h.congr' EventuallyEq.rfl hg

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h.congr
-/
theorem IsBigO.trans_eventuallyEq {f : α -> E} {g₁ g₂ : α -> F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg

/--
Instance `transIsBigOEventuallyEq` / 实例 `transIsBigOEventuallyEq`

English:
instance transIsBigOEventuallyEq
  signature: :
  body: IsBigO.trans_eventuallyEq

@[trans]

中文:
实例 transIsBigOEventuallyEq
  签名: :
  定义体: IsBigO.trans_eventuallyEq

@[trans]

Depends on / 依赖: IsBigO, IsBigO.trans_eventuallyEq, trans_eventuallyEq
-/
instance transIsBigOEventuallyEq :
    @Trans (α -> E) (α -> F) (α -> F) (· =O[l] ·) (· =ᶠ[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans_eventuallyEq

@[trans]
/--
theorem `IsLittleO.trans_eventuallyEq` / 定理 `IsLittleO.trans_eventuallyEq`

English:
theorem IsLittleO.trans_eventuallyEq
  statement: {f : α -> E} {g₁ g₂ : α -> F} (h : f =o[l] g₁)
  proof: h.congr' EventuallyEq.rfl hg

中文:
定理 IsLittleO.trans_eventuallyEq
  结论: {f : α -> E} {g₁ g₂ : α -> F} (h : f =o[l] g₁)
  证明: h.congr' EventuallyEq.rfl hg

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h.congr
-/
theorem IsLittleO.trans_eventuallyEq {f : α -> E} {g₁ g₂ : α -> F} (h : f =o[l] g₁)
    (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg

/--
Instance `transIsLittleOEventuallyEq` / 实例 `transIsLittleOEventuallyEq`

English:
instance transIsLittleOEventuallyEq
  signature: :
  body: IsLittleO.trans_eventuallyEq

中文:
实例 transIsLittleOEventuallyEq
  签名: :
  定义体: IsLittleO.trans_eventuallyEq

Depends on / 依赖: IsLittleO, IsLittleO.trans_eventuallyEq, trans_eventuallyEq
-/
instance transIsLittleOEventuallyEq :
    @Trans (α -> E) (α -> F) (α -> F) (· =o[l] ·) (· =ᶠ[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_eventuallyEq

end congr



/--
theorem `IsBigOWith.comp_tendsto` / 定理 `IsBigOWith.comp_tendsto`

English:
theorem IsBigOWith.comp_tendsto
  statement: (hcfg : IsBigOWith c l f g) {k : β -> α} {l' : Filter β}
  proof: IsBigOWith.of_bound hk hcfg.bound

中文:
定理 IsBigOWith.comp_tendsto
  结论: (hcfg : IsBigOWith c l f g) {k : β -> α} {l' : 滤子 β}
  证明: IsBigOWith.of_bound hk hcfg.bound

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, hcfg.bound, of_bound
-/
theorem IsBigOWith.comp_tendsto (hcfg : IsBigOWith c l f g) {k : β -> α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsBigOWith c l' (f ∘ k) (g ∘ k) :=
IsBigOWith.of_bound hk hcfg.bound

/--
theorem `IsBigO.comp_tendsto` / 定理 `IsBigO.comp_tendsto`

English:
theorem IsBigO.comp_tendsto
  given: (hfg : f =O[l] g) {k : β -> α} {l' : Filter β} (hk : Tendsto k l' l)
  proof: isBigO_iff_isBigOWith.2 hfg.isBigOWith.imp fun _c h => h.comp_tendsto hk

中文:
定理 IsBigO.comp_tendsto
  条件: (hfg : f =O[l] g) {k : β -> α} {l' : 滤子 β} (hk : 收敛 k l' l)
  证明: isBigO_iff_isBigOWith.2 hfg.isBigOWith.imp fun _c h => h.comp_tendsto hk

Depends on / 依赖: comp_tendsto, h.comp_tendsto, hfg.isBigOWith.imp, isBigOWith, isBigO_iff_isBigOWith
-/
theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β -> α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
isBigO_iff_isBigOWith.2 hfg.isBigOWith.imp fun _c h => h.comp_tendsto hk

/--
lemma `IsBigO.comp_neg_int` / 引理 `IsBigO.comp_neg_int`

English:
lemma IsBigO.comp_neg_int
  given: {f : Int -> E} {g : Int -> F} (hf : f =O[cofinite] g)
  proof: by
  rw [← Equiv.neg_apply]
  exact hf.comp_tendsto (Equiv.neg Int).injective.tendsto_cofinite

中文:
引理 IsBigO.comp_neg_int
  条件: {f : 整数 -> E} {g : 整数 -> F} (hf : f =O[cofinite] g)
  证明: by
  rw [← Equiv.neg_apply]
  exact hf.comp_tendsto (Equiv.neg Int).injective.tendsto_cofinite

Depends on / 依赖: Equiv.neg, Equiv.neg_apply, comp_tendsto, hf.comp_tendsto, injective, injective.tendsto_cofinite, neg_apply, tendsto_cofinite
-/
lemma IsBigO.comp_neg_int {f : Int -> E} {g : Int -> F} (hf : f =O[cofinite] g) :
    (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  exact hf.comp_tendsto (Equiv.neg Int).injective.tendsto_cofinite

/--
theorem `IsLittleO.comp_tendsto` / 定理 `IsLittleO.comp_tendsto`

English:
theorem IsLittleO.comp_tendsto
  given: (hfg : f =o[l] g) {k : β -> α} {l' : Filter β} (hk : Tendsto k l' l)
  proof: IsLittleO.of_isBigOWith fun _c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk

@[simp]

中文:
定理 IsLittleO.comp_tendsto
  条件: (hfg : f =o[l] g) {k : β -> α} {l' : 滤子 β} (hk : 收敛 k l' l)
  证明: IsLittleO.of_isBigOWith fun _c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk

@[simp]

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, comp_tendsto, forall_isBigOWith, hfg.forall_isBigOWith, of_isBigOWith
-/
theorem IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β -> α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsLittleO.of_isBigOWith fun _c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk

@[simp]
/--
theorem `isBigOWith_map` / 定理 `isBigOWith_map`

English:
theorem isBigOWith_map
  given: {k : β -> α} {l : Filter β}
  proof: by
  simp only [IsBigOWith_def]
  exact eventually_map

@[simp]

中文:
定理 isBigOWith_map
  条件: {k : β -> α} {l : 滤子 β}
  证明: by
  simp only [IsBigOWith_def]
  exact eventually_map

@[simp]

Depends on / 依赖: IsBigOWith_def, eventually_map
-/
theorem isBigOWith_map {k : β -> α} {l : Filter β} :
    IsBigOWith c (map k l) f g ↔ IsBigOWith c l (f ∘ k) (g ∘ k) := by
  simp only [IsBigOWith_def]
  exact eventually_map

@[simp]
/--
theorem `isBigO_map` / 定理 `isBigO_map`

English:
theorem isBigO_map
  given: {k : β -> α} {l : Filter β}
  statement: f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k)
  proof: by
  simp only [IsBigO_def, isBigOWith_map]

@[simp]

中文:
定理 isBigO_map
  条件: {k : β -> α} {l : 滤子 β}
  结论: f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k)
  证明: by
  simp only [IsBigO_def, isBigOWith_map]

@[simp]

Depends on / 依赖: IsBigO_def, isBigOWith_map
-/
theorem isBigO_map {k : β -> α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [IsBigO_def, isBigOWith_map]

@[simp]
/--
theorem `isLittleO_map` / 定理 `isLittleO_map`

English:
theorem isLittleO_map
  given: {k : β -> α} {l : Filter β}
  statement: f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k)
  proof: by
  simp only [IsLittleO_def, isBigOWith_map]

中文:
定理 isLittleO_map
  条件: {k : β -> α} {l : 滤子 β}
  结论: f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k)
  证明: by
  simp only [IsLittleO_def, isBigOWith_map]

Depends on / 依赖: IsLittleO_def, isBigOWith_map
-/
theorem isLittleO_map {k : β -> α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [IsLittleO_def, isBigOWith_map]

/--
theorem `IsBigOWith.mono` / 定理 `IsBigOWith.mono`

English:
theorem IsBigOWith.mono
  given: (h : IsBigOWith c l' f g) (hl : l <= l')
  statement: IsBigOWith c l f g
  proof: IsBigOWith.of_bound hl h.bound

中文:
定理 IsBigOWith.mono
  条件: (h : IsBigOWith c l' f g) (hl : l <= l')
  结论: IsBigOWith c l f g
  证明: IsBigOWith.of_bound hl h.bound

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, h.bound, of_bound
-/
theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l <= l') : IsBigOWith c l f g :=
IsBigOWith.of_bound hl h.bound

/--
theorem `IsBigO.mono` / 定理 `IsBigO.mono`

English:
theorem IsBigO.mono
  given: (h : f =O[l'] g) (hl : l <= l')
  statement: f =O[l] g
  proof: isBigO_iff_isBigOWith.2 h.isBigOWith.imp fun _c h => h.mono hl

中文:
定理 IsBigO.mono
  条件: (h : f =O[l'] g) (hl : l <= l')
  结论: f =O[l] g
  证明: isBigO_iff_isBigOWith.2 h.isBigOWith.imp fun _c h => h.mono hl

Depends on / 依赖: h.isBigOWith.imp, h.mono, isBigOWith, isBigO_iff_isBigOWith
-/
theorem IsBigO.mono (h : f =O[l'] g) (hl : l <= l') : f =O[l] g :=
isBigO_iff_isBigOWith.2 h.isBigOWith.imp fun _c h => h.mono hl

/--
theorem `IsLittleO.mono` / 定理 `IsLittleO.mono`

English:
theorem IsLittleO.mono
  given: (h : f =o[l'] g) (hl : l <= l')
  statement: f =o[l] g
  proof: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).mono hl

中文:
定理 IsLittleO.mono
  条件: (h : f =o[l'] g) (hl : l <= l')
  结论: f =o[l] g
  证明: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).mono hl

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, forall_isBigOWith, h.forall_isBigOWith, of_isBigOWith
-/
theorem IsLittleO.mono (h : f =o[l'] g) (hl : l <= l') : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).mono hl

/--
theorem `IsBigOWith.trans` / 定理 `IsBigOWith.trans`

English:
theorem IsBigOWith.trans
  given: (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 <= c)
  proof: by
  simp only [IsBigOWith_def] at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc
    ‖f x‖ <= c * ‖g x‖ := hx
    _ <= c * (c' * ‖k x‖) := by gcongr
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm

@[trans]

中文:
定理 IsBigOWith.trans
  条件: (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 <= c)
  证明: by
  simp only [IsBigOWith_def] at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc
    ‖f x‖ <= c * ‖g x‖ := hx
    _ <= c * (c' * ‖k x‖) := by gcongr
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm

@[trans]

Depends on / 依赖: IsBigOWith_def, filter_upwards, mul_assoc
-/
theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 <= c) :
    IsBigOWith (c * c') l f k := by
  simp only [IsBigOWith_def] at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc
    ‖f x‖ <= c * ‖g x‖ := hx
    _ <= c * (c' * ‖k x‖) := by gcongr
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm

@[trans]
/--
theorem `IsBigO.trans` / 定理 `IsBigO.trans`

English:
theorem IsBigO.trans
  given: {f : α -> E} {g : α -> F'} {k : α -> G} (hfg : f =O[l] g) (hgk : g =O[l] k)
  proof: let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.isBigOWith
  (hc.trans hc' cnonneg).isBigO

中文:
定理 IsBigO.trans
  条件: {f : α -> E} {g : α -> F'} {k : α -> G} (hfg : f =O[l] g) (hgk : g =O[l] k)
  证明: let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.isBigOWith
  (hc.trans hc' cnonneg).isBigO

Depends on / 依赖: cnonneg, exists_nonneg, hc.trans, hfg.exists_nonneg, hgk.isBigOWith, isBigO, isBigOWith
-/
theorem IsBigO.trans {f : α -> E} {g : α -> F'} {k : α -> G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.isBigOWith
  (hc.trans hc' cnonneg).isBigO

/--
Instance `transIsBigOIsBigO` / 实例 `transIsBigOIsBigO`

English:
instance transIsBigOIsBigO
  signature: :
  body: IsBigO.trans

中文:
实例 transIsBigOIsBigO
  签名: :
  定义体: IsBigO.trans

Depends on / 依赖: IsBigO, IsBigO.trans
-/
instance transIsBigOIsBigO :
    @Trans (α -> E) (α -> F') (α -> G) (· =O[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans

/--
theorem `IsLittleO.trans_isBigOWith` / 定理 `IsLittleO.trans_isBigOWith`

English:
theorem IsLittleO.trans_isBigOWith
  given: (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c)
  proof: by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel₀ _ hc.ne')

@[trans]

中文:
定理 IsLittleO.trans_isBigOWith
  条件: (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c)
  证明: by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel₀ _ hc.ne')

@[trans]

Depends on / 依赖: IsLittleO_def, congr_const, div_pos, hc.ne, this.le
-/
theorem IsLittleO.trans_isBigOWith (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel₀ _ hc.ne')

@[trans]
/--
theorem `IsLittleO.trans_isBigO` / 定理 `IsLittleO.trans_isBigO`

English:
theorem IsLittleO.trans_isBigO
  statement: {f : α -> E} {g : α -> F} {k : α -> G'} (hfg : f =o[l] g)
  proof: let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos

中文:
定理 IsLittleO.trans_isBigO
  结论: {f : α -> E} {g : α -> F} {k : α -> G'} (hfg : f =o[l] g)
  证明: let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos

Depends on / 依赖: exists_pos, hfg.trans_isBigOWith, hgk.exists_pos, trans_isBigOWith
-/
theorem IsLittleO.trans_isBigO {f : α -> E} {g : α -> F} {k : α -> G'} (hfg : f =o[l] g)
    (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos

/--
Instance `transIsLittleOIsBigO` / 实例 `transIsLittleOIsBigO`

English:
instance transIsLittleOIsBigO
  signature: :
  body: IsLittleO.trans_isBigO

中文:
实例 transIsLittleOIsBigO
  签名: :
  定义体: IsLittleO.trans_isBigO

Depends on / 依赖: IsLittleO, IsLittleO.trans_isBigO, trans_isBigO
-/
instance transIsLittleOIsBigO :
    @Trans (α -> E) (α -> F) (α -> G') (· =o[l] ·) (· =O[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_isBigO

/--
theorem `IsBigOWith.trans_isLittleO` / 定理 `IsBigOWith.trans_isLittleO`

English:
theorem IsBigOWith.trans_isLittleO
  given: (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c)
  proof: by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel₀ _ hc.ne')

@[trans]

中文:
定理 IsBigOWith.trans_isLittleO
  条件: (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c)
  证明: by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel₀ _ hc.ne')

@[trans]

Depends on / 依赖: IsLittleO_def, congr_const, div_pos, hc.le, hc.ne, hfg.trans
-/
theorem IsBigOWith.trans_isLittleO (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel₀ _ hc.ne')

@[trans]
/--
theorem `IsBigO.trans_isLittleO` / 定理 `IsBigO.trans_isLittleO`

English:
theorem IsBigO.trans_isLittleO
  statement: {f : α -> E} {g : α -> F'} {k : α -> G} (hfg : f =O[l] g)
  proof: let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos

中文:
定理 IsBigO.trans_isLittleO
  结论: {f : α -> E} {g : α -> F'} {k : α -> G} (hfg : f =O[l] g)
  证明: let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos

Depends on / 依赖: exists_pos, hc.trans_isLittleO, hfg.exists_pos, trans_isLittleO
-/
theorem IsBigO.trans_isLittleO {f : α -> E} {g : α -> F'} {k : α -> G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos

/--
Instance `transIsBigOIsLittleO` / 实例 `transIsBigOIsLittleO`

English:
instance transIsBigOIsLittleO
  signature: :
  body: IsBigO.trans_isLittleO

@[trans]

中文:
实例 transIsBigOIsLittleO
  签名: :
  定义体: IsBigO.trans_isLittleO

@[trans]

Depends on / 依赖: IsBigO, IsBigO.trans_isLittleO, trans_isLittleO
-/
instance transIsBigOIsLittleO :
    @Trans (α -> E) (α -> F') (α -> G) (· =O[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsBigO.trans_isLittleO

@[trans]
/--
theorem `IsLittleO.trans` / 定理 `IsLittleO.trans`

English:
theorem IsLittleO.trans
  given: {f : α -> E} {g : α -> F} {k : α -> G} (hfg : f =o[l] g) (hgk : g =o[l] k)
  proof: hfg.trans_isBigOWith hgk.isBigOWith one_pos

中文:
定理 IsLittleO.trans
  条件: {f : α -> E} {g : α -> F} {k : α -> G} (hfg : f =o[l] g) (hgk : g =o[l] k)
  证明: hfg.trans_isBigOWith hgk.isBigOWith one_pos

Depends on / 依赖: hfg.trans_isBigOWith, hgk.isBigOWith, isBigOWith, one_pos, trans_isBigOWith
-/
theorem IsLittleO.trans {f : α -> E} {g : α -> F} {k : α -> G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isBigOWith hgk.isBigOWith one_pos

/--
Instance `transIsLittleOIsLittleO` / 实例 `transIsLittleOIsLittleO`

English:
instance transIsLittleOIsLittleO
  signature: :
  body: IsLittleO.trans

中文:
实例 transIsLittleOIsLittleO
  签名: :
  定义体: IsLittleO.trans

Depends on / 依赖: IsLittleO, IsLittleO.trans
-/
instance transIsLittleOIsLittleO :
    @Trans (α -> E) (α -> F) (α -> G) (· =o[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans

/--
theorem `_root_.Filter.Eventually.trans_isBigO` / 定理 `_root_.Filter.Eventually.trans_isBigO`

English:
theorem _root_.Filter.Eventually.trans_isBigO
  statement: {f : α -> E} {g : α -> F'} {k : α -> G}
  proof: (IsBigO.of_bound' hfg).trans hgk

中文:
定理 _root_.滤子.Eventually.trans_isBigO
  结论: {f : α -> E} {g : α -> F'} {k : α -> G}
  证明: (IsBigO.of_bound' hfg).trans hgk

Depends on / 依赖: IsBigO, IsBigO.of_bound, of_bound
-/
theorem _root_.Filter.Eventually.trans_isBigO {f : α -> E} {g : α -> F'} {k : α -> G}
    (hfg : forallᶠ x in l, ‖f x‖ <= ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsBigO.of_bound' hfg).trans hgk

/--
theorem `_root_.Filter.Eventually.isBigO` / 定理 `_root_.Filter.Eventually.isBigO`

English:
theorem _root_.Filter.Eventually.isBigO
  statement: {f : α -> E} {g : α -> Real} {l : Filter α}
  proof: .of_norm_eventuallyLE hfg

中文:
定理 _root_.滤子.Eventually.isBigO
  结论: {f : α -> E} {g : α -> 实数} {l : 滤子 α}
  证明: .of_norm_eventuallyLE hfg

Depends on / 依赖: of_norm_eventuallyLE
-/
theorem _root_.Filter.Eventually.isBigO {f : α -> E} {g : α -> Real} {l : Filter α}
    (hfg : forallᶠ x in l, ‖f x‖ <= g x) : f =O[l] g :=
  .of_norm_eventuallyLE hfg

section

variable (l)

/--
theorem `isBigOWith_of_le'` / 定理 `isBigOWith_of_le'`

English:
theorem isBigOWith_of_le'
  given: (hfg : forall x, ‖f x‖ <= c * ‖g x‖)
  statement: IsBigOWith c l f g
  proof: IsBigOWith.of_bound univ_mem' hfg

中文:
定理 isBigOWith_of_le'
  条件: (hfg : 对任意 x, ‖f x‖ <= c * ‖g x‖)
  结论: IsBigOWith c l f g
  证明: IsBigOWith.of_bound univ_mem' hfg

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, of_bound, univ_mem
-/
theorem isBigOWith_of_le' (hfg : forall x, ‖f x‖ <= c * ‖g x‖) : IsBigOWith c l f g :=
IsBigOWith.of_bound univ_mem' hfg

/--
theorem `isBigOWith_of_le` / 定理 `isBigOWith_of_le`

English:
theorem isBigOWith_of_le
  given: (hfg : forall x, ‖f x‖ <= ‖g x‖)
  statement: IsBigOWith 1 l f g
  proof: isBigOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x

中文:
定理 isBigOWith_of_le
  条件: (hfg : 对任意 x, ‖f x‖ <= ‖g x‖)
  结论: IsBigOWith 1 l f g
  证明: isBigOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x

Depends on / 依赖: isBigOWith_of_le, one_mul
-/
theorem isBigOWith_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) : IsBigOWith 1 l f g :=
  isBigOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x

/--
theorem `isBigO_of_le'` / 定理 `isBigO_of_le'`

English:
theorem isBigO_of_le'
  given: (hfg : forall x, ‖f x‖ <= c * ‖g x‖)
  statement: f =O[l] g
  proof: (isBigOWith_of_le' l hfg).isBigO

中文:
定理 isBigO_of_le'
  条件: (hfg : 对任意 x, ‖f x‖ <= c * ‖g x‖)
  结论: f =O[l] g
  证明: (isBigOWith_of_le' l hfg).isBigO

Depends on / 依赖: isBigO, isBigOWith_of_le
-/
theorem isBigO_of_le' (hfg : forall x, ‖f x‖ <= c * ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le' l hfg).isBigO

/--
theorem `isBigO_of_le` / 定理 `isBigO_of_le`

English:
theorem isBigO_of_le
  given: (hfg : forall x, ‖f x‖ <= ‖g x‖)
  statement: f =O[l] g
  proof: (isBigOWith_of_le l hfg).isBigO

中文:
定理 isBigO_of_le
  条件: (hfg : 对任意 x, ‖f x‖ <= ‖g x‖)
  结论: f =O[l] g
  证明: (isBigOWith_of_le l hfg).isBigO

Depends on / 依赖: isBigO, isBigOWith_of_le
-/
theorem isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le l hfg).isBigO

end

@[refl]
/--
theorem `isBigOWith_refl` / 定理 `isBigOWith_refl`

English:
theorem isBigOWith_refl
  given: (f : α -> E) (l : Filter α)
  statement: IsBigOWith 1 l f f
  proof: isBigOWith_of_le l fun _ => le_rfl

@[refl]

中文:
定理 isBigOWith_refl
  条件: (f : α -> E) (l : 滤子 α)
  结论: IsBigOWith 1 l f f
  证明: isBigOWith_of_le l fun _ => le_rfl

@[refl]

Depends on / 依赖: isBigOWith_of_le, le_rfl
-/
theorem isBigOWith_refl (f : α -> E) (l : Filter α) : IsBigOWith 1 l f f :=
  isBigOWith_of_le l fun _ => le_rfl

@[refl]
/--
theorem `isBigO_refl` / 定理 `isBigO_refl`

English:
theorem isBigO_refl
  given: (f : α -> E) (l : Filter α)
  statement: f =O[l] f
  proof: (isBigOWith_refl f l).isBigO

中文:
定理 isBigO_refl
  条件: (f : α -> E) (l : 滤子 α)
  结论: f =O[l] f
  证明: (isBigOWith_refl f l).isBigO

Depends on / 依赖: isBigO, isBigOWith_refl
-/
theorem isBigO_refl (f : α -> E) (l : Filter α) : f =O[l] f :=
  (isBigOWith_refl f l).isBigO

/--
theorem `_root_.Filter.EventuallyEq.isBigO` / 定理 `_root_.Filter.EventuallyEq.isBigO`

English:
theorem _root_.Filter.EventuallyEq.isBigO
  given: {f₁ f₂ : α -> E} (hf : f₁ =ᶠ[l] f₂)
  statement: f₁ =O[l] f₂
  proof: hf.trans_isBigO (isBigO_refl _ _)

中文:
定理 _root_.滤子.EventuallyEq.isBigO
  条件: {f₁ f₂ : α -> E} (hf : f₁ =ᶠ[l] f₂)
  结论: f₁ =O[l] f₂
  证明: hf.trans_isBigO (isBigO_refl _ _)

Depends on / 依赖: hf.trans_isBigO, isBigO_refl, trans_isBigO
-/
theorem _root_.Filter.EventuallyEq.isBigO {f₁ f₂ : α -> E} (hf : f₁ =ᶠ[l] f₂) : f₁ =O[l] f₂ :=
  hf.trans_isBigO (isBigO_refl _ _)

/--
theorem `IsBigOWith.trans_le` / 定理 `IsBigOWith.trans_le`

English:
theorem IsBigOWith.trans_le
  given: (hfg : IsBigOWith c l f g) (hgk : forall x, ‖g x‖ <= ‖k x‖) (hc : 0 <= c)
  proof: (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const mul_one c

中文:
定理 IsBigOWith.trans_le
  条件: (hfg : IsBigOWith c l f g) (hgk : 对任意 x, ‖g x‖ <= ‖k x‖) (hc : 0 <= c)
  证明: (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const mul_one c

Depends on / 依赖: congr_const, hfg.trans, isBigOWith_of_le, mul_one
-/
theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : forall x, ‖g x‖ <= ‖k x‖) (hc : 0 <= c) :
    IsBigOWith c l f k :=
(hfg.trans (isBigOWith_of_le l hgk) hc).congr_const mul_one c

/--
theorem `IsBigO.trans_le` / 定理 `IsBigO.trans_le`

English:
theorem IsBigO.trans_le
  given: (hfg : f =O[l] g') (hgk : forall x, ‖g' x‖ <= ‖k x‖)
  statement: f =O[l] k
  proof: hfg.trans (isBigO_of_le l hgk)

中文:
定理 IsBigO.trans_le
  条件: (hfg : f =O[l] g') (hgk : 对任意 x, ‖g' x‖ <= ‖k x‖)
  结论: f =O[l] k
  证明: hfg.trans (isBigO_of_le l hgk)

Depends on / 依赖: hfg.trans, isBigO_of_le
-/
theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : forall x, ‖g' x‖ <= ‖k x‖) : f =O[l] k :=
  hfg.trans (isBigO_of_le l hgk)

/--
theorem `IsLittleO.trans_le` / 定理 `IsLittleO.trans_le`

English:
theorem IsLittleO.trans_le
  given: (hfg : f =o[l] g) (hgk : forall x, ‖g x‖ <= ‖k x‖)
  statement: f =o[l] k
  proof: hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one

中文:
定理 IsLittleO.trans_le
  条件: (hfg : f =o[l] g) (hgk : 对任意 x, ‖g x‖ <= ‖k x‖)
  结论: f =o[l] k
  证明: hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one

Depends on / 依赖: hfg.trans_isBigOWith, isBigOWith_of_le, trans_isBigOWith, zero_lt_one
-/
theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : forall x, ‖g x‖ <= ‖k x‖) : f =o[l] k :=
  hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one

/--
theorem `isLittleO_irrefl'` / 定理 `isLittleO_irrefl'`

English:
theorem isLittleO_irrefl'
  given: (h : existsᶠ x in l, ‖f' x‖ != 0)
  statement: ¬f' =o[l] f'
  proof: by
  intro ho
  rcases ((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div]; rw [← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_ge hle

中文:
定理 isLittleO_irrefl'
  条件: (h : 存在ᶠ x in l, ‖f' x‖ != 0)
  结论: ¬f' =o[l] f'
  证明: by
  intro ho
  rcases ((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div]; rw [← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_ge hle

Depends on / 依赖: and_frequently, div_eq_inv_mul, half_lt_self, hne.symm, ho.bound, lt_of_le_of_ne, norm_nonneg, not_ge, one_div, one_half_pos
-/
theorem isLittleO_irrefl' (h : existsᶠ x in l, ‖f' x‖ != 0) : ¬f' =o[l] f' := by
  intro ho
  rcases ((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div]; rw [← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_ge hle

/--
theorem `isLittleO_irrefl` / 定理 `isLittleO_irrefl`

English:
theorem isLittleO_irrefl
  given: (h : existsᶠ x in l, f'' x != 0)
  statement: ¬f'' =o[l] f''
  proof: isLittleO_irrefl' h.mono fun _x => norm_ne_zero_iff.mpr

中文:
定理 isLittleO_irrefl
  条件: (h : 存在ᶠ x in l, f'' x != 0)
  结论: ¬f'' =o[l] f''
  证明: isLittleO_irrefl' h.mono fun _x => norm_ne_zero_iff.mpr

Depends on / 依赖: h.mono, isLittleO_irrefl, norm_ne_zero_iff, norm_ne_zero_iff.mpr
-/
theorem isLittleO_irrefl (h : existsᶠ x in l, f'' x != 0) : ¬f'' =o[l] f'' :=
isLittleO_irrefl' h.mono fun _x => norm_ne_zero_iff.mpr

/--
theorem `IsBigO.not_isLittleO` / 定理 `IsBigO.not_isLittleO`

English:
theorem IsBigO.not_isLittleO
  given: (h : f'' =O[l] g') (hf : existsᶠ x in l, f'' x != 0)
  proof: fun h' =>
  isLittleO_irrefl hf (h.trans_isLittleO h')

中文:
定理 IsBigO.not_isLittleO
  条件: (h : f'' =O[l] g') (hf : 存在ᶠ x in l, f'' x != 0)
  证明: fun h' =>
  isLittleO_irrefl hf (h.trans_isLittleO h')
-/
theorem IsBigO.not_isLittleO (h : f'' =O[l] g') (hf : existsᶠ x in l, f'' x != 0) :
    ¬g' =o[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isLittleO h')

/--
theorem `IsLittleO.not_isBigO` / 定理 `IsLittleO.not_isBigO`

English:
theorem IsLittleO.not_isBigO
  given: (h : f'' =o[l] g') (hf : existsᶠ x in l, f'' x != 0)
  proof: fun h' =>
  isLittleO_irrefl hf (h.trans_isBigO h')

中文:
定理 IsLittleO.not_isBigO
  条件: (h : f'' =o[l] g') (hf : 存在ᶠ x in l, f'' x != 0)
  证明: fun h' =>
  isLittleO_irrefl hf (h.trans_isBigO h')
-/
theorem IsLittleO.not_isBigO (h : f'' =o[l] g') (hf : existsᶠ x in l, f'' x != 0) :
    ¬g' =O[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isBigO h')

section Bot

variable (c f g)

@[simp]
/--
theorem `isBigOWith_bot` / 定理 `isBigOWith_bot`

English:
theorem isBigOWith_bot
  statement: IsBigOWith c ⊥ f g
  proof: IsBigOWith.of_bound trivial

@[simp]

中文:
定理 isBigOWith_bot
  结论: IsBigOWith c ⊥ f g
  证明: IsBigOWith.of_bound trivial

@[simp]

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, of_bound
-/
theorem isBigOWith_bot : IsBigOWith c ⊥ f g :=
IsBigOWith.of_bound trivial

@[simp]
/--
theorem `isBigO_bot` / 定理 `isBigO_bot`

English:
theorem isBigO_bot
  statement: f =O[⊥] g
  proof: (isBigOWith_bot 1 f g).isBigO

@[simp]

中文:
定理 isBigO_bot
  结论: f =O[⊥] g
  证明: (isBigOWith_bot 1 f g).isBigO

@[simp]

Depends on / 依赖: isBigO, isBigOWith_bot
-/
theorem isBigO_bot : f =O[⊥] g :=
  (isBigOWith_bot 1 f g).isBigO

@[simp]
/--
theorem `isLittleO_bot` / 定理 `isLittleO_bot`

English:
theorem isLittleO_bot
  statement: f =o[⊥] g
  proof: IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g

中文:
定理 isLittleO_bot
  结论: f =o[⊥] g
  证明: IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, isBigOWith_bot, of_isBigOWith
-/
theorem isLittleO_bot : f =o[⊥] g :=
  IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g

end Bot

@[simp]
/--
theorem `isBigOWith_pure` / 定理 `isBigOWith_pure`

English:
theorem isBigOWith_pure
  given: {x}
  statement: IsBigOWith c (pure x) f g ↔ ‖f x‖ <= c * ‖g x‖
  proof: isBigOWith_iff

中文:
定理 isBigOWith_pure
  条件: {x}
  结论: IsBigOWith c (pure x) f g ↔ ‖f x‖ <= c * ‖g x‖
  证明: isBigOWith_iff

Depends on / 依赖: isBigOWith_iff
-/
theorem isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ <= c * ‖g x‖ :=
  isBigOWith_iff

/--
theorem `IsBigOWith.sup` / 定理 `IsBigOWith.sup`

English:
theorem IsBigOWith.sup
  given: (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g)
  proof: IsBigOWith.of_bound mem_sup.2 ⟨h.bound, h'.bound⟩

中文:
定理 IsBigOWith.上确界
  条件: (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g)
  证明: IsBigOWith.of_bound mem_sup.2 ⟨h.bound, h'.bound⟩

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, h.bound, mem_sup, of_bound
-/
theorem IsBigOWith.sup (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g) :
    IsBigOWith c (l ⊔ l') f g :=
IsBigOWith.of_bound mem_sup.2 ⟨h.bound, h'.bound⟩

/--
theorem `IsBigOWith.sup'` / 定理 `IsBigOWith.sup'`

English:
theorem IsBigOWith.sup'
  given: (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g')
  proof: IsBigOWith.of_bound
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩

中文:
定理 IsBigOWith.上确界'
  条件: (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g')
  证明: IsBigOWith.of_bound
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, h.weaken, le_max_left, le_max_right, mem_sup, of_bound, weaken
-/
theorem IsBigOWith.sup' (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g') :
    IsBigOWith (max c c') (l ⊔ l') f g' :=
IsBigOWith.of_bound
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩

/--
theorem `IsBigO.sup` / 定理 `IsBigO.sup`

English:
theorem IsBigO.sup
  given: (h : f =O[l] g') (h' : f =O[l'] g')
  statement: f =O[l ⊔ l'] g'
  proof: let ⟨_c, hc⟩ := h.isBigOWith
  let ⟨_c', hc'⟩ := h'.isBigOWith
  (hc.sup' hc').isBigO

中文:
定理 IsBigO.上确界
  条件: (h : f =O[l] g') (h' : f =O[l'] g')
  结论: f =O[l ⊔ l'] g'
  证明: let ⟨_c, hc⟩ := h.isBigOWith
  let ⟨_c', hc'⟩ := h'.isBigOWith
  (hc.sup' hc').isBigO

Depends on / 依赖: h.isBigOWith, hc.sup, isBigO, isBigOWith
-/
theorem IsBigO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  let ⟨_c', hc'⟩ := h'.isBigOWith
  (hc.sup' hc').isBigO

/--
theorem `IsLittleO.sup` / 定理 `IsLittleO.sup`

English:
theorem IsLittleO.sup
  given: (h : f =o[l] g) (h' : f =o[l'] g)
  statement: f =o[l ⊔ l'] g
  proof: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)

@[simp]

中文:
定理 IsLittleO.上确界
  条件: (h : f =o[l] g) (h' : f =o[l'] g)
  结论: f =o[l ⊔ l'] g
  证明: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)

@[simp]

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, forall_isBigOWith, h.forall_isBigOWith, of_isBigOWith
-/
theorem IsLittleO.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)

@[simp]
/--
theorem `isBigO_sup` / 定理 `isBigO_sup`

English:
theorem isBigO_sup
  statement: f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g'
  proof: ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

@[simp]

中文:
定理 isBigO_sup
  结论: f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g'
  证明: ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

@[simp]

Depends on / 依赖: h.mono, le_sup_left, le_sup_right
-/
theorem isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

@[simp]
/--
theorem `isLittleO_sup` / 定理 `isLittleO_sup`

English:
theorem isLittleO_sup
  statement: f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g
  proof: ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

中文:
定理 isLittleO_sup
  结论: f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g
  证明: ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

Depends on / 依赖: h.mono, le_sup_left, le_sup_right
-/
theorem isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

/--
theorem `isBigOWith_insert` / 定理 `isBigOWith_insert`

English:
theorem isBigOWith_insert
  statement: [TopologicalSpace α] {x : α} {s : Set α} {C : Real} {g : α -> E} {g' : α -> F}
  proof: by
  simp_rw [IsBigOWith_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and]

中文:
定理 isBigOWith_insert
  结论: [拓扑空间 α] {x : α} {s : 集合 α} {C : 实数} {g : α -> E} {g' : α -> F}
  证明: by
  simp_rw [IsBigOWith_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and]

Depends on / 依赖: IsBigOWith_def, eventually_pure, eventually_sup, nhdsWithin_insert, simp_rw, true_and
-/
theorem isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : Real} {g : α -> E} {g' : α -> F}
    (h : ‖g x‖ <= C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x) g g' ↔
    IsBigOWith C (𝓝[s] x) g g' := by
  simp_rw [IsBigOWith_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and]

/--
theorem `IsBigOWith.insert` / 定理 `IsBigOWith.insert`

English:
theorem IsBigOWith.insert
  statement: [TopologicalSpace α] {x : α} {s : Set α} {C : Real} {g : α -> E}
  proof: (isBigOWith_insert h2).mpr h1

中文:
定理 IsBigOWith.insert
  结论: [拓扑空间 α] {x : α} {s : 集合 α} {C : 实数} {g : α -> E}
  证明: (isBigOWith_insert h2).mpr h1
-/
protected theorem IsBigOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : Real} {g : α -> E}
    {g' : α -> F} (h1 : IsBigOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ <= C * ‖g' x‖) :
    IsBigOWith C (𝓝[insert x s] x) g g' :=
  (isBigOWith_insert h2).mpr h1

/--
theorem `isLittleO_insert` / 定理 `isLittleO_insert`

English:
theorem isLittleO_insert
  statement: [TopologicalSpace α] {x : α} {s : Set α} {g : α -> E'} {g' : α -> F'}
  proof: by
  simp_rw [IsLittleO_def]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [isBigOWith_insert]
  rw [h]; rw [norm_zero]
  positivity

中文:
定理 isLittleO_insert
  结论: [拓扑空间 α] {x : α} {s : 集合 α} {g : α -> E'} {g' : α -> F'}
  证明: by
  simp_rw [IsLittleO_def]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [isBigOWith_insert]
  rw [h]; rw [norm_zero]
  positivity

Depends on / 依赖: IsLittleO_def, forall_congr, isBigOWith_insert, norm_zero, simp_rw
-/
theorem isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α -> E'} {g' : α -> F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' := by
  simp_rw [IsLittleO_def]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [isBigOWith_insert]
  rw [h]; rw [norm_zero]
  positivity

/--
theorem `IsLittleO.insert` / 定理 `IsLittleO.insert`

English:
theorem IsLittleO.insert
  statement: [TopologicalSpace α] {x : α} {s : Set α} {g : α -> E'}
  proof: (isLittleO_insert h2).mpr h1

中文:
定理 IsLittleO.insert
  结论: [拓扑空间 α] {x : α} {s : 集合 α} {g : α -> E'}
  证明: (isLittleO_insert h2).mpr h1
-/
protected theorem IsLittleO.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α -> E'}
    {g' : α -> F'} (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isLittleO_insert h2).mpr h1

/-! ### Simplification: norm, abs -/


section NormAbs

variable {u v : α -> Real}

@[simp]
/--
theorem `isBigOWith_norm_right` / 定理 `isBigOWith_norm_right`

English:
theorem isBigOWith_norm_right
  statement: (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g'
  proof: by
  simp only [IsBigOWith_def, norm_norm]

@[simp]

中文:
定理 isBigOWith_norm_right
  结论: (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g'
  证明: by
  simp only [IsBigOWith_def, norm_norm]

@[simp]

Depends on / 依赖: IsBigOWith_def, norm_norm
-/
theorem isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_norm]

@[simp]
/--
theorem `isBigOWith_abs_right` / 定理 `isBigOWith_abs_right`

English:
theorem isBigOWith_abs_right
  statement: (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u
  proof: @isBigOWith_norm_right _ _ _ _ _ _ f u l

alias ⟨IsBigOWith.of_norm_right, IsBigOWith.norm_right⟩ := isBigOWith_norm_right

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right

@[simp]

中文:
定理 isBigOWith_abs_right
  结论: (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u
  证明: @isBigOWith_norm_right _ _ _ _ _ _ f u l

alias ⟨IsBigOWith.of_norm_right, IsBigOWith.norm_right⟩ := isBigOWith_norm_right

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right

@[simp]

Depends on / 依赖: isBigOWith_norm_right
-/
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  @isBigOWith_norm_right _ _ _ _ _ _ f u l

alias ⟨IsBigOWith.of_norm_right, IsBigOWith.norm_right⟩ := isBigOWith_norm_right

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right

@[simp]
/--
theorem `isBigO_norm_right` / 定理 `isBigO_norm_right`

English:
theorem isBigO_norm_right
  statement: (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g'
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_right

@[simp]

中文:
定理 isBigO_norm_right
  结论: (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g'
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_right

@[simp]

Depends on / 依赖: IsBigO_def, exists_congr, isBigOWith_norm_right
-/
theorem isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_right

@[simp]
/--
theorem `isBigO_abs_right` / 定理 `isBigO_abs_right`

English:
theorem isBigO_abs_right
  statement: (f =O[l] fun x => |u x|) ↔ f =O[l] u
  proof: @isBigO_norm_right _ _ Real _ _ _ _ _

alias ⟨IsBigO.of_norm_right, IsBigO.norm_right⟩ := isBigO_norm_right

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right

@[simp]

中文:
定理 isBigO_abs_right
  结论: (f =O[l] fun x => |u x|) ↔ f =O[l] u
  证明: @isBigO_norm_right _ _ Real _ _ _ _ _

alias ⟨IsBigO.of_norm_right, IsBigO.norm_right⟩ := isBigO_norm_right

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right

@[simp]

Depends on / 依赖: isBigO_norm_right
-/
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isBigO_norm_right _ _ Real _ _ _ _ _

alias ⟨IsBigO.of_norm_right, IsBigO.norm_right⟩ := isBigO_norm_right

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right

@[simp]
/--
theorem `isLittleO_norm_right` / 定理 `isLittleO_norm_right`

English:
theorem isLittleO_norm_right
  statement: (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g'
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_right

@[simp]

中文:
定理 isLittleO_norm_right
  结论: (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g'
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_right

@[simp]

Depends on / 依赖: IsLittleO_def, isBigOWith_norm_right
-/
theorem isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_right

@[simp]
/--
theorem `isLittleO_abs_right` / 定理 `isLittleO_abs_right`

English:
theorem isLittleO_abs_right
  statement: (f =o[l] fun x => |u x|) ↔ f =o[l] u
  proof: @isLittleO_norm_right _ _ Real _ _ _ _ _

alias ⟨IsLittleO.of_norm_right, IsLittleO.norm_right⟩ := isLittleO_norm_right

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right

@[simp]

中文:
定理 isLittleO_abs_right
  结论: (f =o[l] fun x => |u x|) ↔ f =o[l] u
  证明: @isLittleO_norm_right _ _ Real _ _ _ _ _

alias ⟨IsLittleO.of_norm_right, IsLittleO.norm_right⟩ := isLittleO_norm_right

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right

@[simp]

Depends on / 依赖: isLittleO_norm_right
-/
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isLittleO_norm_right _ _ Real _ _ _ _ _

alias ⟨IsLittleO.of_norm_right, IsLittleO.norm_right⟩ := isLittleO_norm_right

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right

@[simp]
/--
theorem `isBigOWith_norm_left` / 定理 `isBigOWith_norm_left`

English:
theorem isBigOWith_norm_left
  statement: IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g
  proof: by
  simp only [IsBigOWith_def, norm_norm]

@[simp]

中文:
定理 isBigOWith_norm_left
  结论: IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g
  证明: by
  simp only [IsBigOWith_def, norm_norm]

@[simp]

Depends on / 依赖: IsBigOWith_def, norm_norm
-/
theorem isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_norm]

@[simp]
/--
theorem `isBigOWith_abs_left` / 定理 `isBigOWith_abs_left`

English:
theorem isBigOWith_abs_left
  statement: IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g
  proof: @isBigOWith_norm_left _ _ _ _ _ _ g u l

alias ⟨IsBigOWith.of_norm_left, IsBigOWith.norm_left⟩ := isBigOWith_norm_left

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left

@[simp]

中文:
定理 isBigOWith_abs_left
  结论: IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g
  证明: @isBigOWith_norm_left _ _ _ _ _ _ g u l

alias ⟨IsBigOWith.of_norm_left, IsBigOWith.norm_left⟩ := isBigOWith_norm_left

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left

@[simp]

Depends on / 依赖: isBigOWith_norm_left
-/
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  @isBigOWith_norm_left _ _ _ _ _ _ g u l

alias ⟨IsBigOWith.of_norm_left, IsBigOWith.norm_left⟩ := isBigOWith_norm_left

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left

@[simp]
/--
theorem `isBigO_norm_left` / 定理 `isBigO_norm_left`

English:
theorem isBigO_norm_left
  statement: (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_left

@[simp]

中文:
定理 isBigO_norm_left
  结论: (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_left

@[simp]

Depends on / 依赖: IsBigO_def, exists_congr, isBigOWith_norm_left
-/
theorem isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_left

@[simp]
/--
theorem `isBigO_abs_left` / 定理 `isBigO_abs_left`

English:
theorem isBigO_abs_left
  statement: (fun x => |u x|) =O[l] g ↔ u =O[l] g
  proof: @isBigO_norm_left _ _ _ _ _ g u l

alias ⟨IsBigO.of_norm_left, IsBigO.norm_left⟩ := isBigO_norm_left

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left

@[simp]

中文:
定理 isBigO_abs_left
  结论: (fun x => |u x|) =O[l] g ↔ u =O[l] g
  证明: @isBigO_norm_left _ _ _ _ _ g u l

alias ⟨IsBigO.of_norm_left, IsBigO.norm_left⟩ := isBigO_norm_left

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left

@[simp]

Depends on / 依赖: isBigO_norm_left
-/
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isBigO_norm_left _ _ _ _ _ g u l

alias ⟨IsBigO.of_norm_left, IsBigO.norm_left⟩ := isBigO_norm_left

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left

@[simp]
/--
theorem `isLittleO_norm_left` / 定理 `isLittleO_norm_left`

English:
theorem isLittleO_norm_left
  statement: (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_left

@[simp]

中文:
定理 isLittleO_norm_left
  结论: (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_left

@[simp]

Depends on / 依赖: IsLittleO_def, isBigOWith_norm_left
-/
theorem isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_left

@[simp]
/--
theorem `isLittleO_abs_left` / 定理 `isLittleO_abs_left`

English:
theorem isLittleO_abs_left
  statement: (fun x => |u x|) =o[l] g ↔ u =o[l] g
  proof: @isLittleO_norm_left _ _ _ _ _ g u l

alias ⟨IsLittleO.of_norm_left, IsLittleO.norm_left⟩ := isLittleO_norm_left

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left

中文:
定理 isLittleO_abs_left
  结论: (fun x => |u x|) =o[l] g ↔ u =o[l] g
  证明: @isLittleO_norm_left _ _ _ _ _ g u l

alias ⟨IsLittleO.of_norm_left, IsLittleO.norm_left⟩ := isLittleO_norm_left

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left

Depends on / 依赖: isLittleO_norm_left
-/
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isLittleO_norm_left _ _ _ _ _ g u l

alias ⟨IsLittleO.of_norm_left, IsLittleO.norm_left⟩ := isLittleO_norm_left

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left

/--
theorem `isBigOWith_norm_norm` / 定理 `isBigOWith_norm_norm`

English:
theorem isBigOWith_norm_norm
  proof: isBigOWith_norm_left.trans isBigOWith_norm_right

中文:
定理 isBigOWith_norm_norm
  证明: isBigOWith_norm_left.trans isBigOWith_norm_right

Depends on / 依赖: isBigOWith_norm_left, isBigOWith_norm_left.trans, isBigOWith_norm_right
-/
theorem isBigOWith_norm_norm :
    (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsBigOWith c l f' g' :=
  isBigOWith_norm_left.trans isBigOWith_norm_right

/--
theorem `isBigOWith_abs_abs` / 定理 `isBigOWith_abs_abs`

English:
theorem isBigOWith_abs_abs
  proof: isBigOWith_abs_left.trans isBigOWith_abs_right

alias ⟨IsBigOWith.of_norm_norm, IsBigOWith.norm_norm⟩ := isBigOWith_norm_norm

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs

中文:
定理 isBigOWith_abs_abs
  证明: isBigOWith_abs_left.trans isBigOWith_abs_right

alias ⟨IsBigOWith.of_norm_norm, IsBigOWith.norm_norm⟩ := isBigOWith_norm_norm

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs

Depends on / 依赖: isBigOWith_abs_left, isBigOWith_abs_left.trans, isBigOWith_abs_right
-/
theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right

alias ⟨IsBigOWith.of_norm_norm, IsBigOWith.norm_norm⟩ := isBigOWith_norm_norm

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs

/--
theorem `isBigO_norm_norm` / 定理 `isBigO_norm_norm`

English:
theorem isBigO_norm_norm
  statement: ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g'
  proof: isBigO_norm_left.trans isBigO_norm_right

中文:
定理 isBigO_norm_norm
  结论: ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g'
  证明: isBigO_norm_left.trans isBigO_norm_right

Depends on / 依赖: isBigO_norm_left, isBigO_norm_left.trans, isBigO_norm_right
-/
theorem isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isBigO_norm_left.trans isBigO_norm_right

/--
theorem `isBigO_abs_abs` / 定理 `isBigO_abs_abs`

English:
theorem isBigO_abs_abs
  statement: ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v
  proof: isBigO_abs_left.trans isBigO_abs_right

alias ⟨IsBigO.of_norm_norm, IsBigO.norm_norm⟩ := isBigO_norm_norm

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs

中文:
定理 isBigO_abs_abs
  结论: ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v
  证明: isBigO_abs_left.trans isBigO_abs_right

alias ⟨IsBigO.of_norm_norm, IsBigO.norm_norm⟩ := isBigO_norm_norm

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs

Depends on / 依赖: isBigO_abs_left, isBigO_abs_left.trans, isBigO_abs_right
-/
theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right

alias ⟨IsBigO.of_norm_norm, IsBigO.norm_norm⟩ := isBigO_norm_norm

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs

/--
theorem `isLittleO_norm_norm` / 定理 `isLittleO_norm_norm`

English:
theorem isLittleO_norm_norm
  statement: ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g'
  proof: isLittleO_norm_left.trans isLittleO_norm_right

中文:
定理 isLittleO_norm_norm
  结论: ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g'
  证明: isLittleO_norm_left.trans isLittleO_norm_right

Depends on / 依赖: isLittleO_norm_left, isLittleO_norm_left.trans, isLittleO_norm_right
-/
theorem isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isLittleO_norm_left.trans isLittleO_norm_right

/--
theorem `isLittleO_abs_abs` / 定理 `isLittleO_abs_abs`

English:
theorem isLittleO_abs_abs
  statement: ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v
  proof: isLittleO_abs_left.trans isLittleO_abs_right

alias ⟨IsLittleO.of_norm_norm, IsLittleO.norm_norm⟩ := isLittleO_norm_norm

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs

中文:
定理 isLittleO_abs_abs
  结论: ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v
  证明: isLittleO_abs_left.trans isLittleO_abs_right

alias ⟨IsLittleO.of_norm_norm, IsLittleO.norm_norm⟩ := isLittleO_norm_norm

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs

Depends on / 依赖: isLittleO_abs_left, isLittleO_abs_left.trans, isLittleO_abs_right
-/
theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right

alias ⟨IsLittleO.of_norm_norm, IsLittleO.norm_norm⟩ := isLittleO_norm_norm

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
/--
theorem `isBigOWith_neg_right` / 定理 `isBigOWith_neg_right`

English:
theorem isBigOWith_neg_right
  statement: (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g'
  proof: by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right

@[simp]

中文:
定理 isBigOWith_neg_right
  结论: (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g'
  证明: by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right

@[simp]

Depends on / 依赖: IsBigOWith_def, norm_neg
-/
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right

@[simp]
/--
theorem `isBigO_neg_right` / 定理 `isBigO_neg_right`

English:
theorem isBigO_neg_right
  statement: (f =O[l] fun x => -g' x) ↔ f =O[l] g'
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right

@[simp]

中文:
定理 isBigO_neg_right
  结论: (f =O[l] fun x => -g' x) ↔ f =O[l] g'
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right

@[simp]

Depends on / 依赖: IsBigO_def, exists_congr, isBigOWith_neg_right
-/
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right

@[simp]
/--
theorem `isLittleO_neg_right` / 定理 `isLittleO_neg_right`

English:
theorem isLittleO_neg_right
  statement: (f =o[l] fun x => -g' x) ↔ f =o[l] g'
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right

@[simp]

中文:
定理 isLittleO_neg_right
  结论: (f =o[l] fun x => -g' x) ↔ f =o[l] g'
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right

@[simp]

Depends on / 依赖: IsLittleO_def, isBigOWith_neg_right
-/
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right

@[simp]
/--
theorem `isBigOWith_neg_left` / 定理 `isBigOWith_neg_left`

English:
theorem isBigOWith_neg_left
  statement: IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g
  proof: by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left

@[simp]

中文:
定理 isBigOWith_neg_left
  结论: IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g
  证明: by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left

@[simp]

Depends on / 依赖: IsBigOWith_def, norm_neg
-/
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left

@[simp]
/--
theorem `isBigO_neg_left` / 定理 `isBigO_neg_left`

English:
theorem isBigO_neg_left
  statement: (fun x => -f' x) =O[l] g ↔ f' =O[l] g
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left

@[simp]

中文:
定理 isBigO_neg_left
  结论: (fun x => -f' x) =O[l] g ↔ f' =O[l] g
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left

@[simp]

Depends on / 依赖: IsBigO_def, exists_congr, isBigOWith_neg_left
-/
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left

@[simp]
/--
theorem `isLittleO_neg_left` / 定理 `isLittleO_neg_left`

English:
theorem isLittleO_neg_left
  statement: (fun x => -f' x) =o[l] g ↔ f' =o[l] g
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left

中文:
定理 isLittleO_neg_left
  结论: (fun x => -f' x) =o[l] g ↔ f' =o[l] g
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left

Depends on / 依赖: IsLittleO_def, isBigOWith_neg_left
-/
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left



/--
theorem `isBigOWith_fst_prod` / 定理 `isBigOWith_fst_prod`

English:
theorem isBigOWith_fst_prod
  statement: IsBigOWith 1 l f' fun x => (f' x, g' x)
  proof: isBigOWith_of_le l fun _x => le_max_left _ _

中文:
定理 isBigOWith_fst_prod
  结论: IsBigOWith 1 l f' fun x => (f' x, g' x)
  证明: isBigOWith_of_le l fun _x => le_max_left _ _

Depends on / 依赖: isBigOWith_of_le, le_max_left
-/
theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_left _ _

/--
theorem `isBigOWith_snd_prod` / 定理 `isBigOWith_snd_prod`

English:
theorem isBigOWith_snd_prod
  statement: IsBigOWith 1 l g' fun x => (f' x, g' x)
  proof: isBigOWith_of_le l fun _x => le_max_right _ _

中文:
定理 isBigOWith_snd_prod
  结论: IsBigOWith 1 l g' fun x => (f' x, g' x)
  证明: isBigOWith_of_le l fun _x => le_max_right _ _

Depends on / 依赖: isBigOWith_of_le, le_max_right
-/
theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_right _ _

/--
theorem `isBigO_fst_prod` / 定理 `isBigO_fst_prod`

English:
theorem isBigO_fst_prod
  statement: f' =O[l] fun x => (f' x, g' x)
  proof: isBigOWith_fst_prod.isBigO

中文:
定理 isBigO_fst_prod
  结论: f' =O[l] fun x => (f' x, g' x)
  证明: isBigOWith_fst_prod.isBigO

Depends on / 依赖: isBigO, isBigOWith_fst_prod, isBigOWith_fst_prod.isBigO
-/
theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.isBigO

/--
theorem `isBigO_snd_prod` / 定理 `isBigO_snd_prod`

English:
theorem isBigO_snd_prod
  statement: g' =O[l] fun x => (f' x, g' x)
  proof: isBigOWith_snd_prod.isBigO

中文:
定理 isBigO_snd_prod
  结论: g' =O[l] fun x => (f' x, g' x)
  证明: isBigOWith_snd_prod.isBigO

Depends on / 依赖: isBigO, isBigOWith_snd_prod, isBigOWith_snd_prod.isBigO
-/
theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.isBigO

/--
theorem `isBigO_fst_prod'` / 定理 `isBigO_fst_prod'`

English:
theorem isBigO_fst_prod'
  given: {f' : α -> E' × F'}
  statement: (fun x => (f' x).1) =O[l] f'
  proof: by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_fst_prod (E' := E') (F' := F')

中文:
定理 isBigO_fst_prod'
  条件: {f' : α -> E' × F'}
  结论: (fun x => (f' x).1) =O[l] f'
  证明: by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_fst_prod (E' := E') (F' := F')

Depends on / 依赖: IsBigOWith_def, IsBigO_def, isBigO_fst_prod
-/
theorem isBigO_fst_prod' {f' : α -> E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_fst_prod (E' := E') (F' := F')

/--
theorem `isBigO_snd_prod'` / 定理 `isBigO_snd_prod'`

English:
theorem isBigO_snd_prod'
  given: {f' : α -> E' × F'}
  statement: (fun x => (f' x).2) =O[l] f'
  proof: by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_snd_prod (E' := E') (F' := F')

中文:
定理 isBigO_snd_prod'
  条件: {f' : α -> E' × F'}
  结论: (fun x => (f' x).2) =O[l] f'
  证明: by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_snd_prod (E' := E') (F' := F')

Depends on / 依赖: IsBigOWith_def, IsBigO_def, isBigO_snd_prod
-/
theorem isBigO_snd_prod' {f' : α -> E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_snd_prod (E' := E') (F' := F')

section

variable (f' k')

/--
theorem `IsBigOWith.prod_rightl` / 定理 `IsBigOWith.prod_rightl`

English:
theorem IsBigOWith.prod_rightl
  given: (h : IsBigOWith c l f g') (hc : 0 <= c)
  proof: (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)

中文:
定理 IsBigOWith.prod_rightl
  条件: (h : IsBigOWith c l f g') (hc : 0 <= c)
  证明: (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)

Depends on / 依赖: congr_const, h.trans, isBigOWith_fst_prod, mul_one
-/
theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 <= c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)

/--
theorem `IsBigO.prod_rightl` / 定理 `IsBigO.prod_rightl`

English:
theorem IsBigO.prod_rightl
  given: (h : f =O[l] g')
  statement: f =O[l] fun x => (g' x, k' x)
  proof: let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO

中文:
定理 IsBigO.prod_rightl
  条件: (h : f =O[l] g')
  结论: f =O[l] fun x => (g' x, k' x)
  证明: let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO

Depends on / 依赖: cnonneg, exists_nonneg, h.exists_nonneg, hc.prod_rightl, isBigO, prod_rightl
-/
theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO

/--
theorem `IsLittleO.prod_rightl` / 定理 `IsLittleO.prod_rightl`

English:
theorem IsLittleO.prod_rightl
  given: (h : f =o[l] g')
  statement: f =o[l] fun x => (g' x, k' x)
  proof: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le

中文:
定理 IsLittleO.prod_rightl
  条件: (h : f =o[l] g')
  结论: f =o[l] fun x => (g' x, k' x)
  证明: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, cpos.le, forall_isBigOWith, h.forall_isBigOWith, of_isBigOWith, prod_rightl
-/
theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le

/--
theorem `IsBigOWith.prod_rightr` / 定理 `IsBigOWith.prod_rightr`

English:
theorem IsBigOWith.prod_rightr
  given: (h : IsBigOWith c l f g') (hc : 0 <= c)
  proof: (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)

中文:
定理 IsBigOWith.prod_rightr
  条件: (h : IsBigOWith c l f g') (hc : 0 <= c)
  证明: (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)

Depends on / 依赖: congr_const, h.trans, isBigOWith_snd_prod, mul_one
-/
theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 <= c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)

/--
theorem `IsBigO.prod_rightr` / 定理 `IsBigO.prod_rightr`

English:
theorem IsBigO.prod_rightr
  given: (h : f =O[l] g')
  statement: f =O[l] fun x => (f' x, g' x)
  proof: let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO

中文:
定理 IsBigO.prod_rightr
  条件: (h : f =O[l] g')
  结论: f =O[l] fun x => (f' x, g' x)
  证明: let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO

Depends on / 依赖: cnonneg, exists_nonneg, h.exists_nonneg, hc.prod_rightr, isBigO, prod_rightr
-/
theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO

/--
theorem `IsLittleO.prod_rightr` / 定理 `IsLittleO.prod_rightr`

English:
theorem IsLittleO.prod_rightr
  given: (h : f =o[l] g')
  statement: f =o[l] fun x => (f' x, g' x)
  proof: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le

中文:
定理 IsLittleO.prod_rightr
  条件: (h : f =o[l] g')
  结论: f =o[l] fun x => (f' x, g' x)
  证明: IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, cpos.le, forall_isBigOWith, h.forall_isBigOWith, of_isBigOWith, prod_rightr
-/
theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le

end

section

variable {f : α × β -> E} {g : α × β -> F} {l' : Filter β}

/--
theorem `IsBigO.fiberwise_right` / 定理 `IsBigO.fiberwise_right`

English:
theorem IsBigO.fiberwise_right
  proof: by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₁ fun _ ha => ⟨c, mem_of_superset ht₂ fun _ hb => ht ⟨ha, hb⟩⟩

中文:
定理 IsBigO.fiberwise_right
  证明: by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₁ fun _ ha => ⟨c, mem_of_superset ht₂ fun _ hb => ht ⟨ha, hb⟩⟩
-/
protected theorem IsBigO.fiberwise_right :
    f =O[l ×ˢ l'] g -> forallᶠ a in l, (f ⟨a, ·⟩) =O[l'] (g ⟨a, ·⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₁ fun _ ha => ⟨c, mem_of_superset ht₂ fun _ hb => ht ⟨ha, hb⟩⟩

/--
theorem `IsBigO.fiberwise_left` / 定理 `IsBigO.fiberwise_left`

English:
theorem IsBigO.fiberwise_left
  proof: by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₂ fun _ hb => ⟨c, mem_of_superset ht₁ fun _ ha => ht ⟨ha, hb⟩⟩

中文:
定理 IsBigO.fiberwise_left
  证明: by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₂ fun _ hb => ⟨c, mem_of_superset ht₁ fun _ ha => ht ⟨ha, hb⟩⟩
-/
protected theorem IsBigO.fiberwise_left :
    f =O[l ×ˢ l'] g -> forallᶠ b in l', (f ⟨·, b⟩) =O[l] (g ⟨·, b⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₂ fun _ hb => ⟨c, mem_of_superset ht₁ fun _ ha => ht ⟨ha, hb⟩⟩

end

section

variable (l' : Filter β)

/--
theorem `IsBigO.comp_fst` / 定理 `IsBigO.comp_fst`

English:
theorem IsBigO.comp_fst
  statement: f =O[l] g -> (f ∘ Prod.fst) =O[l ×ˢ l'] (g ∘ Prod.fst)
  proof: by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ => ⟨c, _, hc, fun _ => True, eventually_true l', fun {_} h {_} _ => h⟩

中文:
定理 IsBigO.comp_fst
  结论: f =O[l] g -> (f ∘ 积类型.fst) =O[l ×ˢ l'] (g ∘ 积类型.fst)
  证明: by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ => ⟨c, _, hc, fun _ => True, eventually_true l', fun {_} h {_} _ => h⟩
-/
protected theorem IsBigO.comp_fst : f =O[l] g -> (f ∘ Prod.fst) =O[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ => ⟨c, _, hc, fun _ => True, eventually_true l', fun {_} h {_} _ => h⟩

/--
theorem `IsBigO.comp_snd` / 定理 `IsBigO.comp_snd`

English:
theorem IsBigO.comp_snd
  statement: f =O[l] g -> (f ∘ Prod.snd) =O[l' ×ˢ l] (g ∘ Prod.snd)
  proof: by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ => ⟨c, fun _ => True, eventually_true l', _, hc, fun _ => id⟩

中文:
定理 IsBigO.comp_snd
  结论: f =O[l] g -> (f ∘ 积类型.snd) =O[l' ×ˢ l] (g ∘ 积类型.snd)
  证明: by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ => ⟨c, fun _ => True, eventually_true l', _, hc, fun _ => id⟩
-/
protected theorem IsBigO.comp_snd : f =O[l] g -> (f ∘ Prod.snd) =O[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ => ⟨c, fun _ => True, eventually_true l', _, hc, fun _ => id⟩

/--
theorem `IsLittleO.comp_fst` / 定理 `IsLittleO.comp_fst`

English:
theorem IsLittleO.comp_fst
  statement: f =o[l] g -> (f ∘ Prod.fst) =o[l ×ˢ l'] (g ∘ Prod.fst)
  proof: by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc => ⟨_, h hc, fun _ => True, eventually_true l', fun {_} h {_} _ => h⟩

中文:
定理 IsLittleO.comp_fst
  结论: f =o[l] g -> (f ∘ 积类型.fst) =o[l ×ˢ l'] (g ∘ 积类型.fst)
  证明: by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc => ⟨_, h hc, fun _ => True, eventually_true l', fun {_} h {_} _ => h⟩
-/
protected theorem IsLittleO.comp_fst : f =o[l] g -> (f ∘ Prod.fst) =o[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc => ⟨_, h hc, fun _ => True, eventually_true l', fun {_} h {_} _ => h⟩

/--
theorem `IsLittleO.comp_snd` / 定理 `IsLittleO.comp_snd`

English:
theorem IsLittleO.comp_snd
  statement: f =o[l] g -> (f ∘ Prod.snd) =o[l' ×ˢ l] (g ∘ Prod.snd)
  proof: by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc => ⟨fun _ => True, eventually_true l', _, h hc, fun _ => id⟩

中文:
定理 IsLittleO.comp_snd
  结论: f =o[l] g -> (f ∘ 积类型.snd) =o[l' ×ˢ l] (g ∘ 积类型.snd)
  证明: by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc => ⟨fun _ => True, eventually_true l', _, h hc, fun _ => id⟩
-/
protected theorem IsLittleO.comp_snd : f =o[l] g -> (f ∘ Prod.snd) =o[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc => ⟨fun _ => True, eventually_true l', _, h hc, fun _ => id⟩

end

/--
theorem `IsBigOWith.prod_left_same` / 定理 `IsBigOWith.prod_left_same`

English:
theorem IsBigOWith.prod_left_same
  given: (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k')
  proof: by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg] with x using max_le

中文:
定理 IsBigOWith.prod_left_same
  条件: (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k')
  证明: by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg] with x using max_le

Depends on / 依赖: filter_upwards, isBigOWith_iff, max_le
-/
theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg] with x using max_le

/--
theorem `IsBigOWith.prod_left` / 定理 `IsBigOWith.prod_left`

English:
theorem IsBigOWith.prod_left
  given: (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k')
  proof: (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')

中文:
定理 IsBigOWith.prod_left
  条件: (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k')
  证明: (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')

Depends on / 依赖: hf.weaken, hg.weaken, le_max_left, le_max_right, prod_left_same, weaken
-/
theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')

/--
theorem `IsBigOWith.prod_left_fst` / 定理 `IsBigOWith.prod_left_fst`

English:
theorem IsBigOWith.prod_left_fst
  given: (h : IsBigOWith c l (fun x => (f' x, g' x)) k')
  proof: (isBigOWith_fst_prod.trans h zero_le_one).congr_const one_mul c

中文:
定理 IsBigOWith.prod_left_fst
  条件: (h : IsBigOWith c l (fun x => (f' x, g' x)) k')
  证明: (isBigOWith_fst_prod.trans h zero_le_one).congr_const one_mul c

Depends on / 依赖: congr_const, isBigOWith_fst_prod, isBigOWith_fst_prod.trans, one_mul, zero_le_one
-/
theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
(isBigOWith_fst_prod.trans h zero_le_one).congr_const one_mul c

/--
theorem `IsBigOWith.prod_left_snd` / 定理 `IsBigOWith.prod_left_snd`

English:
theorem IsBigOWith.prod_left_snd
  given: (h : IsBigOWith c l (fun x => (f' x, g' x)) k')
  proof: (isBigOWith_snd_prod.trans h zero_le_one).congr_const one_mul c

中文:
定理 IsBigOWith.prod_left_snd
  条件: (h : IsBigOWith c l (fun x => (f' x, g' x)) k')
  证明: (isBigOWith_snd_prod.trans h zero_le_one).congr_const one_mul c

Depends on / 依赖: congr_const, isBigOWith_snd_prod, isBigOWith_snd_prod.trans, one_mul, zero_le_one
-/
theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
(isBigOWith_snd_prod.trans h zero_le_one).congr_const one_mul c

/--
theorem `isBigOWith_prod_left` / 定理 `isBigOWith_prod_left`

English:
theorem isBigOWith_prod_left
  proof: ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

中文:
定理 isBigOWith_prod_left
  证明: ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

Depends on / 依赖: h.prod_left_fst, h.prod_left_snd, prod_left_fst, prod_left_same, prod_left_snd
-/
theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

/--
theorem `IsBigO.prod_left` / 定理 `IsBigO.prod_left`

English:
theorem IsBigO.prod_left
  given: (hf : f' =O[l] k') (hg : g' =O[l] k')
  statement: (fun x => (f' x, g' x)) =O[l] k'
  proof: let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO

中文:
定理 IsBigO.prod_left
  条件: (hf : f' =O[l] k') (hg : g' =O[l] k')
  结论: (fun x => (f' x, g' x)) =O[l] k'
  证明: let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO

Depends on / 依赖: hf.isBigOWith, hf.prod_left, hg.isBigOWith, isBigO, isBigOWith, prod_left
-/
theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO

/--
theorem `IsBigO.prod_left_fst` / 定理 `IsBigO.prod_left_fst`

English:
theorem IsBigO.prod_left_fst
  statement: (fun x => (f' x, g' x)) =O[l] k' -> f' =O[l] k'
  proof: IsBigO.trans isBigO_fst_prod

中文:
定理 IsBigO.prod_left_fst
  结论: (fun x => (f' x, g' x)) =O[l] k' -> f' =O[l] k'
  证明: IsBigO.trans isBigO_fst_prod

Depends on / 依赖: IsBigO, IsBigO.trans, isBigO_fst_prod
-/
theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' -> f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod

/--
theorem `IsBigO.prod_left_snd` / 定理 `IsBigO.prod_left_snd`

English:
theorem IsBigO.prod_left_snd
  statement: (fun x => (f' x, g' x)) =O[l] k' -> g' =O[l] k'
  proof: IsBigO.trans isBigO_snd_prod

@[simp]

中文:
定理 IsBigO.prod_left_snd
  结论: (fun x => (f' x, g' x)) =O[l] k' -> g' =O[l] k'
  证明: IsBigO.trans isBigO_snd_prod

@[simp]

Depends on / 依赖: IsBigO, IsBigO.trans, isBigO_snd_prod
-/
theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' -> g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod

@[simp]
/--
theorem `isBigO_prod_left` / 定理 `isBigO_prod_left`

English:
theorem isBigO_prod_left
  statement: (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k'
  proof: ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

中文:
定理 isBigO_prod_left
  结论: (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k'
  证明: ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

Depends on / 依赖: h.prod_left_fst, h.prod_left_snd, prod_left, prod_left_fst, prod_left_snd
-/
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

/--
theorem `IsLittleO.prod_left` / 定理 `IsLittleO.prod_left`

English:
theorem IsLittleO.prod_left
  given: (hf : f' =o[l] k') (hg : g' =o[l] k')
  proof: IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)

中文:
定理 IsLittleO.prod_left
  条件: (hf : f' =o[l] k') (hg : g' =o[l] k')
  证明: IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, forall_isBigOWith, hf.forall_isBigOWith, hg.forall_isBigOWith, of_isBigOWith, prod_left_same
-/
theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)

/--
theorem `IsLittleO.prod_left_fst` / 定理 `IsLittleO.prod_left_fst`

English:
theorem IsLittleO.prod_left_fst
  statement: (fun x => (f' x, g' x)) =o[l] k' -> f' =o[l] k'
  proof: IsBigO.trans_isLittleO isBigO_fst_prod

中文:
定理 IsLittleO.prod_left_fst
  结论: (fun x => (f' x, g' x)) =o[l] k' -> f' =o[l] k'
  证明: IsBigO.trans_isLittleO isBigO_fst_prod

Depends on / 依赖: IsBigO, IsBigO.trans_isLittleO, isBigO_fst_prod, trans_isLittleO
-/
theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' -> f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod

/--
theorem `IsLittleO.prod_left_snd` / 定理 `IsLittleO.prod_left_snd`

English:
theorem IsLittleO.prod_left_snd
  statement: (fun x => (f' x, g' x)) =o[l] k' -> g' =o[l] k'
  proof: IsBigO.trans_isLittleO isBigO_snd_prod

@[simp]

中文:
定理 IsLittleO.prod_left_snd
  结论: (fun x => (f' x, g' x)) =o[l] k' -> g' =o[l] k'
  证明: IsBigO.trans_isLittleO isBigO_snd_prod

@[simp]

Depends on / 依赖: IsBigO, IsBigO.trans_isLittleO, isBigO_snd_prod, trans_isLittleO
-/
theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' -> g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod

@[simp]
/--
theorem `isLittleO_prod_left` / 定理 `isLittleO_prod_left`

English:
theorem isLittleO_prod_left
  statement: (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k'
  proof: ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

中文:
定理 isLittleO_prod_left
  结论: (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k'
  证明: ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

Depends on / 依赖: h.prod_left_fst, h.prod_left_snd, prod_left, prod_left_fst, prod_left_snd
-/
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

/--
theorem `IsBigOWith.eq_zero_imp` / 定理 `IsBigOWith.eq_zero_imp`

English:
theorem IsBigOWith.eq_zero_imp
  given: (h : IsBigOWith c l f'' g'')
  statement: forallᶠ x in l, g'' x = 0 -> f'' x = 0
  proof: Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 by simpa [hg] using hx

中文:
定理 IsBigOWith.eq_zero_imp
  条件: (h : IsBigOWith c l f'' g'')
  结论: 对任意ᶠ x in l, g'' x = 0 -> f'' x = 0
  证明: Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 by simpa [hg] using hx

Depends on / 依赖: Eventually, Eventually.mono, h.bound, norm_le_zero_iff
-/
theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : forallᶠ x in l, g'' x = 0 -> f'' x = 0 :=
Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 by simpa [hg] using hx

/--
theorem `IsBigO.eq_zero_imp` / 定理 `IsBigO.eq_zero_imp`

English:
theorem IsBigO.eq_zero_imp
  given: (h : f'' =O[l] g'')
  statement: forallᶠ x in l, g'' x = 0 -> f'' x = 0
  proof: let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp

中文:
定理 IsBigO.eq_zero_imp
  条件: (h : f'' =O[l] g'')
  结论: 对任意ᶠ x in l, g'' x = 0 -> f'' x = 0
  证明: let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp

Depends on / 依赖: eq_zero_imp, h.isBigOWith, hC.eq_zero_imp, isBigOWith
-/
theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : forallᶠ x in l, g'' x = 0 -> f'' x = 0 :=
  let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α -> E'} {g₁ g₂ : α -> F'}

/--
theorem `IsBigOWith.add` / 定理 `IsBigOWith.add`

English:
theorem IsBigOWith.add
  given: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g)
  proof: by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ <= c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm

中文:
定理 IsBigOWith.add
  条件: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g)
  证明: by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ <= c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm

Depends on / 依赖: IsBigOWith_def, add_mul, filter_upwards, norm_add_le_of_le
-/
theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ <= c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm

/--
theorem `IsBigO.add` / 定理 `IsBigO.add`

English:
theorem IsBigO.add
  given: (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g)
  statement: (fun x => f₁ x + f₂ x) =O[l] g
  proof: let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO

中文:
定理 IsBigO.add
  条件: (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g)
  结论: (fun x => f₁ x + f₂ x) =O[l] g
  证明: let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO

Depends on / 依赖: isBigO, isBigOWith
-/
theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO

/--
theorem `IsLittleO.add` / 定理 `IsLittleO.add`

English:
theorem IsLittleO.add
  given: (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g)
  statement: (fun x => f₁ x + f₂ x) =o[l] g
  proof: IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)

中文:
定理 IsLittleO.add
  条件: (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g)
  结论: (fun x => f₁ x + f₂ x) =o[l] g
  证明: IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, add_halves, congr_const, forall_isBigOWith, half_pos, of_isBigOWith
-/
theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)

/--
theorem `IsBigOWith.add_add` / 定理 `IsBigOWith.add_add`

English:
theorem IsBigOWith.add_add
  statement: {g₁ g₂ : α -> Real} (h₁ : IsBigOWith c₁ l f₁ g₁)
  proof: by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc
    ‖f₁ x + f₂ x‖ <= c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖ := norm_add_le_of_le hx₁ hx₂
    _ <= (max c₁ c₂) * ‖g₁ x‖ + (max c₁ c₂) * ‖g₂ x‖ := by
        gcongr <;> simp [le_max_left _ _, le_max_right _ _]
    _ = (max c₁ c₂) * ‖‖g₁ 

中文:
定理 IsBigOWith.add_add
  结论: {g₁ g₂ : α -> 实数} (h₁ : IsBigOWith c₁ l f₁ g₁)
  证明: by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc
    ‖f₁ x + f₂ x‖ <= c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖ := norm_add_le_of_le hx₁ hx₂
    _ <= (max c₁ c₂) * ‖g₁ x‖ + (max c₁ c₂) * ‖g₂ x‖ := by
        gcongr <;> simp [le_max_left _ _, le_max_right _ _]
    _ = (max c₁ c₂) * ‖‖g₁ 

Depends on / 依赖: IsBigOWith_def, Real.norm_of_nonneg, add_nonneg, filter_upwards, le_max_left, le_max_right, mul_add, norm_add_le_of_le, norm_nonneg, norm_of_nonneg
-/
theorem IsBigOWith.add_add {g₁ g₂ : α -> Real} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (max c₁ c₂) l (fun x => f₁ x + f₂ x) (fun x => ‖g₁ x‖ + ‖g₂ x‖) := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc
    ‖f₁ x + f₂ x‖ <= c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖ := norm_add_le_of_le hx₁ hx₂
    _ <= (max c₁ c₂) * ‖g₁ x‖ + (max c₁ c₂) * ‖g₂ x‖ := by
        gcongr <;> simp [le_max_left _ _, le_max_right _ _]
    _ = (max c₁ c₂) * ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]; rw [mul_add]

/--
theorem `IsBigO.add_add` / 定理 `IsBigO.add_add`

English:
theorem IsBigO.add_add
  given: {g₁ g₂ : α -> Real} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂)
  proof: by
  obtain ⟨c₁, hc₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, hc₂⟩ := h₂.isBigOWith
  exact (hc₁.add_add hc₂).isBigO

中文:
定理 IsBigO.add_add
  条件: {g₁ g₂ : α -> 实数} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂)
  证明: by
  obtain ⟨c₁, hc₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, hc₂⟩ := h₂.isBigOWith
  exact (hc₁.add_add hc₂).isBigO

Depends on / 依赖: add_add, isBigO, isBigOWith
-/
theorem IsBigO.add_add {g₁ g₂ : α -> Real} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x + f₂ x) =O[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  obtain ⟨c₁, hc₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, hc₂⟩ := h₂.isBigOWith
  exact (hc₁.add_add hc₂).isBigO

/--
theorem `IsLittleO.add_add` / 定理 `IsLittleO.add_add`

English:
theorem IsLittleO.add_add
  given: (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂)
  proof: by
  refine (h₁.trans_le fun x => ?_).add (h₂.trans_le ?_) <;> simp [abs_of_nonneg, add_nonneg]

中文:
定理 IsLittleO.add_add
  条件: (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂)
  证明: by
  refine (h₁.trans_le fun x => ?_).add (h₂.trans_le ?_) <;> simp [abs_of_nonneg, add_nonneg]

Depends on / 依赖: abs_of_nonneg, add_nonneg, trans_le
-/
theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine (h₁.trans_le fun x => ?_).add (h₂.trans_le ?_) <;> simp [abs_of_nonneg, add_nonneg]

/--
theorem `IsBigO.add_isLittleO` / 定理 `IsBigO.add_isLittleO`

English:
theorem IsBigO.add_isLittleO
  given: (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g)
  statement: (fun x => f₁ x + f₂ x) =O[l] g
  proof: h₁.add h₂.isBigO

中文:
定理 IsBigO.add_isLittleO
  条件: (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g)
  结论: (fun x => f₁ x + f₂ x) =O[l] g
  证明: h₁.add h₂.isBigO

Depends on / 依赖: isBigO
-/
theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.isBigO

/--
theorem `IsLittleO.add_isBigO` / 定理 `IsLittleO.add_isBigO`

English:
theorem IsLittleO.add_isBigO
  given: (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g)
  statement: (fun x => f₁ x + f₂ x) =O[l] g
  proof: h₁.isBigO.add h₂

中文:
定理 IsLittleO.add_isBigO
  条件: (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g)
  结论: (fun x => f₁ x + f₂ x) =O[l] g
  证明: h₁.isBigO.add h₂

Depends on / 依赖: isBigO, isBigO.add
-/
theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.isBigO.add h₂

/--
theorem `IsBigOWith.add_isLittleO` / 定理 `IsBigOWith.add_isLittleO`

English:
theorem IsBigOWith.add_isLittleO
  given: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂)
  proof: (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel _ _)

中文:
定理 IsBigOWith.add_isLittleO
  条件: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂)
  证明: (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel _ _)

Depends on / 依赖: add_sub_cancel, congr_const, forall_isBigOWith, sub_pos
-/
theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel _ _)

/--
theorem `IsLittleO.add_isBigOWith` / 定理 `IsLittleO.add_isBigOWith`

English:
theorem IsLittleO.add_isBigOWith
  given: (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂)
  proof: (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _

中文:
定理 IsLittleO.add_isBigOWith
  条件: (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂)
  证明: (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _

Depends on / 依赖: add_comm, add_isLittleO, congr_left
-/
theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _

/--
theorem `IsBigOWith.sub` / 定理 `IsBigOWith.sub`

English:
theorem IsBigOWith.sub
  given: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g)
  proof: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

中文:
定理 IsBigOWith.sub
  条件: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g)
  证明: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

Depends on / 依赖: neg_left, sub_eq_add_neg
-/
theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

/--
theorem `IsBigOWith.sub_isLittleO` / 定理 `IsBigOWith.sub_isLittleO`

English:
theorem IsBigOWith.sub_isLittleO
  given: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂)
  proof: by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc

中文:
定理 IsBigOWith.sub_isLittleO
  条件: (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂)
  证明: by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc

Depends on / 依赖: add_isLittleO, neg_left, sub_eq_add_neg
-/
theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc

/--
theorem `IsBigO.sub` / 定理 `IsBigO.sub`

English:
theorem IsBigO.sub
  given: (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g)
  statement: (fun x => f₁ x - f₂ x) =O[l] g
  proof: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

中文:
定理 IsBigO.sub
  条件: (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g)
  结论: (fun x => f₁ x - f₂ x) =O[l] g
  证明: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

Depends on / 依赖: neg_left, sub_eq_add_neg
-/
theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

/--
theorem `IsLittleO.sub` / 定理 `IsLittleO.sub`

English:
theorem IsLittleO.sub
  given: (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g)
  statement: (fun x => f₁ x - f₂ x) =o[l] g
  proof: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

中文:
定理 IsLittleO.sub
  条件: (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g)
  结论: (fun x => f₁ x - f₂ x) =o[l] g
  证明: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

Depends on / 依赖: neg_left, sub_eq_add_neg
-/
theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

/--
theorem `IsBigO.add_iff_left` / 定理 `IsBigO.add_iff_left`

English:
theorem IsBigO.add_iff_left
  given: (h₂ : f₂ =O[l] g)
  statement: (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g)
  proof: .congr (fun _ => add_sub_cancel_right _ _) (fun _ => rfl), fun h => h.add h₂⟩ ⟨fun h => h.sub h₂

中文:
定理 IsBigO.add_iff_left
  条件: (h₂ : f₂ =O[l] g)
  结论: (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g)
  证明: .congr (fun _ => add_sub_cancel_right _ _) (fun _ => rfl), fun h => h.add h₂⟩ ⟨fun h => h.sub h₂

Depends on / 依赖: add_sub_cancel_right, h.add, h.sub
-/
theorem IsBigO.add_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
.congr (fun _ => add_sub_cancel_right _ _) (fun _ => rfl), fun h => h.add h₂⟩ ⟨fun h => h.sub h₂

/--
theorem `IsBigO.add_iff_right` / 定理 `IsBigO.add_iff_right`

English:
theorem IsBigO.add_iff_right
  given: (h₁ : f₁ =O[l] g)
  statement: (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g)
  proof: .congr (fun _ => (eq_sub_of_add_eq' rfl).symm) (fun _ => rfl), fun h => h₁.add h⟩ ⟨fun h => h.sub h₁

中文:
定理 IsBigO.add_iff_right
  条件: (h₁ : f₁ =O[l] g)
  结论: (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g)
  证明: .congr (fun _ => (eq_sub_of_add_eq' rfl).symm) (fun _ => rfl), fun h => h₁.add h⟩ ⟨fun h => h.sub h₁

Depends on / 依赖: eq_sub_of_add_eq, h.sub
-/
theorem IsBigO.add_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
.congr (fun _ => (eq_sub_of_add_eq' rfl).symm) (fun _ => rfl), fun h => h₁.add h⟩ ⟨fun h => h.sub h₁

/--
theorem `IsLittleO.add_iff_left` / 定理 `IsLittleO.add_iff_left`

English:
theorem IsLittleO.add_iff_left
  given: (h₂ : f₂ =o[l] g)
  statement: (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g)
  proof: .congr (fun _ => add_sub_cancel_right _ _) (fun _ => rfl), fun h => h.add h₂⟩ ⟨fun h => h.sub h₂

中文:
定理 IsLittleO.add_iff_left
  条件: (h₂ : f₂ =o[l] g)
  结论: (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g)
  证明: .congr (fun _ => add_sub_cancel_right _ _) (fun _ => rfl), fun h => h.add h₂⟩ ⟨fun h => h.sub h₂

Depends on / 依赖: add_sub_cancel_right, h.add, h.sub
-/
theorem IsLittleO.add_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
.congr (fun _ => add_sub_cancel_right _ _) (fun _ => rfl), fun h => h.add h₂⟩ ⟨fun h => h.sub h₂

/--
theorem `IsLittleO.add_iff_right` / 定理 `IsLittleO.add_iff_right`

English:
theorem IsLittleO.add_iff_right
  given: (h₁ : f₁ =o[l] g)
  statement: (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g)
  proof: .congr (fun _ => (eq_sub_of_add_eq' rfl).symm) (fun _ => rfl), fun h => h₁.add h⟩ ⟨fun h => h.sub h₁

中文:
定理 IsLittleO.add_iff_right
  条件: (h₁ : f₁ =o[l] g)
  结论: (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g)
  证明: .congr (fun _ => (eq_sub_of_add_eq' rfl).symm) (fun _ => rfl), fun h => h₁.add h⟩ ⟨fun h => h.sub h₁

Depends on / 依赖: eq_sub_of_add_eq, h.sub
-/
theorem IsLittleO.add_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
.congr (fun _ => (eq_sub_of_add_eq' rfl).symm) (fun _ => rfl), fun h => h₁.add h⟩ ⟨fun h => h.sub h₁

/--
theorem `IsBigO.sub_iff_left` / 定理 `IsBigO.sub_iff_left`

English:
theorem IsBigO.sub_iff_left
  given: (h₂ : f₂ =O[l] g)
  statement: (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g)
  proof: .congr (fun _ => sub_add_cancel ..) (fun _ => rfl), fun h => h.sub h₂⟩ ⟨fun h => h.add h₂

中文:
定理 IsBigO.sub_iff_left
  条件: (h₂ : f₂ =O[l] g)
  结论: (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g)
  证明: .congr (fun _ => sub_add_cancel ..) (fun _ => rfl), fun h => h.sub h₂⟩ ⟨fun h => h.add h₂

Depends on / 依赖: h.add, h.sub, sub_add_cancel
-/
theorem IsBigO.sub_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
.congr (fun _ => sub_add_cancel ..) (fun _ => rfl), fun h => h.sub h₂⟩ ⟨fun h => h.add h₂

/--
theorem `IsBigO.sub_iff_right` / 定理 `IsBigO.sub_iff_right`

English:
theorem IsBigO.sub_iff_right
  given: (h₁ : f₁ =O[l] g)
  statement: (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g)
  proof: .congr (fun _ => sub_sub_self ..) (fun _ => rfl), fun h => h₁.sub h⟩ ⟨fun h => h₁.sub h

中文:
定理 IsBigO.sub_iff_right
  条件: (h₁ : f₁ =O[l] g)
  结论: (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g)
  证明: .congr (fun _ => sub_sub_self ..) (fun _ => rfl), fun h => h₁.sub h⟩ ⟨fun h => h₁.sub h

Depends on / 依赖: sub_sub_self
-/
theorem IsBigO.sub_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
.congr (fun _ => sub_sub_self ..) (fun _ => rfl), fun h => h₁.sub h⟩ ⟨fun h => h₁.sub h

/--
theorem `IsLittleO.sub_iff_left` / 定理 `IsLittleO.sub_iff_left`

English:
theorem IsLittleO.sub_iff_left
  given: (h₂ : f₂ =o[l] g)
  statement: (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g)
  proof: .congr (fun _ => sub_add_cancel ..) (fun _ => rfl), fun h => h.sub h₂⟩ ⟨fun h => h.add h₂

中文:
定理 IsLittleO.sub_iff_left
  条件: (h₂ : f₂ =o[l] g)
  结论: (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g)
  证明: .congr (fun _ => sub_add_cancel ..) (fun _ => rfl), fun h => h.sub h₂⟩ ⟨fun h => h.add h₂

Depends on / 依赖: h.add, h.sub, sub_add_cancel
-/
theorem IsLittleO.sub_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
.congr (fun _ => sub_add_cancel ..) (fun _ => rfl), fun h => h.sub h₂⟩ ⟨fun h => h.add h₂

/--
theorem `IsLittleO.sub_iff_right` / 定理 `IsLittleO.sub_iff_right`

English:
theorem IsLittleO.sub_iff_right
  given: (h₁ : f₁ =o[l] g)
  statement: (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g)
  proof: .congr (fun _ => sub_sub_self ..) (fun _ => rfl), fun h => h₁.sub h⟩ ⟨fun h => h₁.sub h

中文:
定理 IsLittleO.sub_iff_right
  条件: (h₁ : f₁ =o[l] g)
  结论: (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g)
  证明: .congr (fun _ => sub_sub_self ..) (fun _ => rfl), fun h => h₁.sub h⟩ ⟨fun h => h₁.sub h

Depends on / 依赖: sub_sub_self
-/
theorem IsLittleO.sub_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
.congr (fun _ => sub_sub_self ..) (fun _ => rfl), fun h => h₁.sub h⟩ ⟨fun h => h₁.sub h

end add_sub

/-!
### Lemmas about `IsBigO (f₁ - f₂) g l` / `IsLittleO (f₁ - f₂) g l` treated as a binary relation
-/


section IsBigOOAsRel

variable {f₁ f₂ f₃ : α -> E'}

/--
theorem `IsBigOWith.symm` / 定理 `IsBigOWith.symm`

English:
theorem IsBigOWith.symm
  given: (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
  proof: h.neg_left.congr_left fun _x => neg_sub _ _

中文:
定理 IsBigOWith.symm
  条件: (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
  证明: h.neg_left.congr_left fun _x => neg_sub _ _

Depends on / 依赖: congr_left, h.neg_left.congr_left, neg_left, neg_sub
-/
theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun _x => neg_sub _ _

/--
theorem `isBigOWith_comm` / 定理 `isBigOWith_comm`

English:
theorem isBigOWith_comm
  proof: ⟨IsBigOWith.symm, IsBigOWith.symm⟩

中文:
定理 isBigOWith_comm
  证明: ⟨IsBigOWith.symm, IsBigOWith.symm⟩

Depends on / 依赖: IsBigOWith, IsBigOWith.symm
-/
theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩

/--
theorem `IsBigO.symm` / 定理 `IsBigO.symm`

English:
theorem IsBigO.symm
  given: (h : (fun x => f₁ x - f₂ x) =O[l] g)
  statement: (fun x => f₂ x - f₁ x) =O[l] g
  proof: h.neg_left.congr_left fun _x => neg_sub _ _

中文:
定理 IsBigO.symm
  条件: (h : (fun x => f₁ x - f₂ x) =O[l] g)
  结论: (fun x => f₂ x - f₁ x) =O[l] g
  证明: h.neg_left.congr_left fun _x => neg_sub _ _

Depends on / 依赖: congr_left, h.neg_left.congr_left, neg_left, neg_sub
-/
theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun _x => neg_sub _ _

/--
theorem `isBigO_comm` / 定理 `isBigO_comm`

English:
theorem isBigO_comm
  statement: (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g
  proof: ⟨IsBigO.symm, IsBigO.symm⟩

中文:
定理 isBigO_comm
  结论: (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g
  证明: ⟨IsBigO.symm, IsBigO.symm⟩

Depends on / 依赖: IsBigO, IsBigO.symm
-/
theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩

/--
theorem `IsLittleO.symm` / 定理 `IsLittleO.symm`

English:
theorem IsLittleO.symm
  given: (h : (fun x => f₁ x - f₂ x) =o[l] g)
  statement: (fun x => f₂ x - f₁ x) =o[l] g
  proof: by
  simpa only [neg_sub] using h.neg_left

中文:
定理 IsLittleO.symm
  条件: (h : (fun x => f₁ x - f₂ x) =o[l] g)
  结论: (fun x => f₂ x - f₁ x) =o[l] g
  证明: by
  simpa only [neg_sub] using h.neg_left

Depends on / 依赖: h.neg_left, neg_left, neg_sub
-/
theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left

/--
theorem `isLittleO_comm` / 定理 `isLittleO_comm`

English:
theorem isLittleO_comm
  statement: (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g
  proof: ⟨IsLittleO.symm, IsLittleO.symm⟩

中文:
定理 isLittleO_comm
  结论: (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g
  证明: ⟨IsLittleO.symm, IsLittleO.symm⟩

Depends on / 依赖: IsLittleO, IsLittleO.symm
-/
theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩

/--
theorem `IsBigOWith.triangle` / 定理 `IsBigOWith.triangle`

English:
theorem IsBigOWith.triangle
  statement: (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
  proof: (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

中文:
定理 IsBigOWith.triangle
  结论: (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
  证明: (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

Depends on / 依赖: congr_left, sub_add_sub_cancel
-/
theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

/--
theorem `IsBigO.triangle` / 定理 `IsBigO.triangle`

English:
theorem IsBigO.triangle
  statement: (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
  proof: (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

中文:
定理 IsBigO.triangle
  结论: (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
  证明: (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

Depends on / 依赖: congr_left, sub_add_sub_cancel
-/
theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

/--
theorem `IsLittleO.triangle` / 定理 `IsLittleO.triangle`

English:
theorem IsLittleO.triangle
  statement: (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
  proof: (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

中文:
定理 IsLittleO.triangle
  结论: (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
  证明: (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

Depends on / 依赖: congr_left, sub_add_sub_cancel
-/
theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

/--
theorem `IsBigO.congr_of_sub` / 定理 `IsBigO.congr_of_sub`

English:
theorem IsBigO.congr_of_sub
  given: (h : (fun x => f₁ x - f₂ x) =O[l] g)
  statement: f₁ =O[l] g ↔ f₂ =O[l] g
  proof: ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

中文:
定理 IsBigO.congr_of_sub
  条件: (h : (fun x => f₁ x - f₂ x) =O[l] g)
  结论: f₁ =O[l] g ↔ f₂ =O[l] g
  证明: ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

Depends on / 依赖: congr_left, h.add, sub_add_cancel, sub_sub_cancel
-/
theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

/--
theorem `IsLittleO.congr_of_sub` / 定理 `IsLittleO.congr_of_sub`

English:
theorem IsLittleO.congr_of_sub
  given: (h : (fun x => f₁ x - f₂ x) =o[l] g)
  statement: f₁ =o[l] g ↔ f₂ =o[l] g
  proof: ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

中文:
定理 IsLittleO.congr_of_sub
  条件: (h : (fun x => f₁ x - f₂ x) =o[l] g)
  结论: f₁ =o[l] g ↔ f₂ =o[l] g
  证明: ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

Depends on / 依赖: congr_left, h.add, sub_add_cancel, sub_sub_cancel
-/
theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

end IsBigOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

/--
theorem `isLittleO_zero` / 定理 `isLittleO_zero`

English:
theorem isLittleO_zero
  statement: (fun _x => (0 : E')) =o[l] g'
  proof: IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

中文:
定理 isLittleO_zero
  结论: (fun _x => (0 : E')) =o[l] g'
  证明: IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

Depends on / 依赖: IsLittleO, IsLittleO.of_bound, hc.le, mul_nonneg, norm_nonneg, of_bound, univ_mem
-/
theorem isLittleO_zero : (fun _x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

/--
theorem `isBigOWith_zero` / 定理 `isBigOWith_zero`

English:
theorem isBigOWith_zero
  given: (hc : 0 <= c)
  statement: IsBigOWith c l (fun _x => (0 : E')) g'
  proof: IsBigOWith.of_bound univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)

中文:
定理 isBigOWith_zero
  条件: (hc : 0 <= c)
  结论: IsBigOWith c l (fun _x => (0 : E')) g'
  证明: IsBigOWith.of_bound univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, mul_nonneg, norm_nonneg, of_bound, univ_mem
-/
theorem isBigOWith_zero (hc : 0 <= c) : IsBigOWith c l (fun _x => (0 : E')) g' :=
IsBigOWith.of_bound univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)

/--
theorem `isBigOWith_zero'` / 定理 `isBigOWith_zero'`

English:
theorem isBigOWith_zero'
  statement: IsBigOWith 0 l (fun _x => (0 : E')) g
  proof: IsBigOWith.of_bound univ_mem' fun x => by simp

中文:
定理 isBigOWith_zero'
  结论: IsBigOWith 0 l (fun _x => (0 : E')) g
  证明: IsBigOWith.of_bound univ_mem' fun x => by simp

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, of_bound, univ_mem
-/
theorem isBigOWith_zero' : IsBigOWith 0 l (fun _x => (0 : E')) g :=
IsBigOWith.of_bound univ_mem' fun x => by simp

/--
theorem `isBigO_zero` / 定理 `isBigO_zero`

English:
theorem isBigO_zero
  statement: (fun _x => (0 : E')) =O[l] g
  proof: isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩

中文:
定理 isBigO_zero
  结论: (fun _x => (0 : E')) =O[l] g
  证明: isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩

Depends on / 依赖: isBigOWith_zero, isBigO_iff_isBigOWith
-/
theorem isBigO_zero : (fun _x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩

/--
theorem `isBigO_refl_left` / 定理 `isBigO_refl_left`

English:
theorem isBigO_refl_left
  statement: (fun x => f' x - f' x) =O[l] g'
  proof: (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm

中文:
定理 isBigO_refl_left
  结论: (fun x => f' x - f' x) =O[l] g'
  证明: (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm

Depends on / 依赖: congr_left, isBigO_zero, sub_self
-/
theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm

/--
theorem `isLittleO_refl_left` / 定理 `isLittleO_refl_left`

English:
theorem isLittleO_refl_left
  statement: (fun x => f' x - f' x) =o[l] g'
  proof: (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm

中文:
定理 isLittleO_refl_left
  结论: (fun x => f' x - f' x) =o[l] g'
  证明: (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm

Depends on / 依赖: congr_left, isLittleO_zero, sub_self
-/
theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm

variable {g g' l}

@[simp]
/--
theorem `isBigOWith_zero_right_iff` / 定理 `isBigOWith_zero_right_iff`

English:
theorem isBigOWith_zero_right_iff
  statement: (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
  proof: by
  simp only [IsBigOWith_def, norm_zero, mul_zero, norm_le_zero_iff, EventuallyEq, Pi.zero_apply]

@[simp]

中文:
定理 isBigOWith_zero_right_iff
  结论: (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
  证明: by
  simp only [IsBigOWith_def, norm_zero, mul_zero, norm_le_zero_iff, EventuallyEq, Pi.zero_apply]

@[simp]

Depends on / 依赖: EventuallyEq, IsBigOWith_def, Pi.zero_apply, mul_zero, norm_le_zero_iff, norm_zero, zero_apply
-/
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [IsBigOWith_def, norm_zero, mul_zero, norm_le_zero_iff, EventuallyEq, Pi.zero_apply]

@[simp]
/--
theorem `isBigO_zero_right_iff` / 定理 `isBigO_zero_right_iff`

English:
theorem isBigO_zero_right_iff
  statement: (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
  proof: ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩

@[simp]

中文:
定理 isBigO_zero_right_iff
  结论: (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
  证明: ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩

@[simp]

Depends on / 依赖: IsBigOWith, h.isBigOWith, isBigO, isBigOWith, isBigOWith_zero_right_iff
-/
theorem isBigO_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩

@[simp]
/--
theorem `isLittleO_zero_right_iff` / 定理 `isLittleO_zero_right_iff`

English:
theorem isLittleO_zero_right_iff
  statement: (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
  proof: ⟨fun h => isBigO_zero_right_iff.1 h.isBigO,
   fun h => IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩

中文:
定理 isLittleO_zero_right_iff
  结论: (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
  证明: ⟨fun h => isBigO_zero_right_iff.1 h.isBigO,
   fun h => IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, h.isBigO, isBigO, isBigOWith_zero_right_iff, isBigO_zero_right_iff, of_isBigOWith
-/
theorem isLittleO_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.isBigO,
   fun h => IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩

/--
theorem `isBigOWith_const_const` / 定理 `isBigOWith_const_const`

English:
theorem isBigOWith_const_const
  given: (c : E) {c' : F''} (hc' : c' != 0) (l : Filter α)
  proof: by
  simp only [IsBigOWith_def]
  apply univ_mem'
  intro x
  rw [mem_ofPred]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc')]

中文:
定理 isBigOWith_const_const
  条件: (c : E) {c' : F''} (hc' : c' != 0) (l : 滤子 α)
  证明: by
  simp only [IsBigOWith_def]
  apply univ_mem'
  intro x
  rw [mem_ofPred]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc')]

Depends on / 依赖: IsBigOWith_def, mem_ofPred, norm_ne_zero_iff, norm_ne_zero_iff.mpr, univ_mem
-/
theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' != 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c' := by
  simp only [IsBigOWith_def]
  apply univ_mem'
  intro x
  rw [mem_ofPred]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc')]

/--
theorem `isBigO_const_const` / 定理 `isBigO_const_const`

English:
theorem isBigO_const_const
  given: (c : E) {c' : F''} (hc' : c' != 0) (l : Filter α)
  proof: (isBigOWith_const_const c hc' l).isBigO

@[simp]

中文:
定理 isBigO_const_const
  条件: (c : E) {c' : F''} (hc' : c' != 0) (l : 滤子 α)
  证明: (isBigOWith_const_const c hc' l).isBigO

@[simp]

Depends on / 依赖: isBigO, isBigOWith_const_const
-/
theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' != 0) (l : Filter α) :
    (fun _x : α => c) =O[l] fun _x => c' :=
  (isBigOWith_const_const c hc' l).isBigO

@[simp]
/--
theorem `isBigO_const_const_iff` / 定理 `isBigO_const_const_iff`

English:
theorem isBigO_const_const_iff
  given: {c : E''} {c' : F''} (l : Filter α) [l.NeBot]
  proof: by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', isBigO_const_const _ hc']

@[simp]

中文:
定理 isBigO_const_const_iff
  条件: {c : E''} {c' : F''} (l : 滤子 α) [l.NeBot]
  证明: by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', isBigO_const_const _ hc']

@[simp]

Depends on / 依赖: EventuallyEq, eq_or_ne, isBigO_const_const
-/
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] :
    ((fun _x : α => c) =O[l] fun _x => c') ↔ c' = 0 -> c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', isBigO_const_const _ hc']

@[simp]
/--
theorem `isBigO_pure` / 定理 `isBigO_pure`

English:
theorem isBigO_pure
  given: {x}
  statement: f'' =O[pure x] g'' ↔ g'' x = 0 -> f'' x = 0
  proof: calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 -> f'' x = 0 := isBigO_const_const_iff _

中文:
定理 isBigO_pure
  条件: {x}
  结论: f'' =O[pure x] g'' ↔ g'' x = 0 -> f'' x = 0
  证明: calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 -> f'' x = 0 := isBigO_const_const_iff _

Depends on / 依赖: isBigO_congr, isBigO_const_const_iff
-/
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 -> f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 -> f'' x = 0 := isBigO_const_const_iff _

end ZeroConst


/--
theorem `isBigOWith_const_mul_self` / 定理 `isBigOWith_const_mul_self`

English:
theorem isBigOWith_const_mul_self
  given: (c : R) (f : α -> R) (l : Filter α)
  proof: isBigOWith_of_le' _ fun _x => norm_mul_le _ _

中文:
定理 isBigOWith_const_mul_self
  条件: (c : R) (f : α -> R) (l : 滤子 α)
  证明: isBigOWith_of_le' _ fun _x => norm_mul_le _ _

Depends on / 依赖: isBigOWith_of_le, norm_mul_le
-/
theorem isBigOWith_const_mul_self (c : R) (f : α -> R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun _x => norm_mul_le _ _

/--
theorem `isBigO_const_mul_self` / 定理 `isBigO_const_mul_self`

English:
theorem isBigO_const_mul_self
  given: (c : R) (f : α -> R) (l : Filter α)
  statement: (fun x => c * f x) =O[l] f
  proof: (isBigOWith_const_mul_self c f l).isBigO

中文:
定理 isBigO_const_mul_self
  条件: (c : R) (f : α -> R) (l : 滤子 α)
  结论: (fun x => c * f x) =O[l] f
  证明: (isBigOWith_const_mul_self c f l).isBigO

Depends on / 依赖: isBigO, isBigOWith_const_mul_self
-/
theorem isBigO_const_mul_self (c : R) (f : α -> R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).isBigO

/--
theorem `IsBigOWith.const_mul_left` / 定理 `IsBigOWith.const_mul_left`

English:
theorem IsBigOWith.const_mul_left
  given: {f : α -> R} (h : IsBigOWith c l f g) (c' : R)
  proof: (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')

中文:
定理 IsBigOWith.const_mul_left
  条件: {f : α -> R} (h : IsBigOWith c l f g) (c' : R)
  证明: (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')

Depends on / 依赖: isBigOWith_const_mul_self, norm_nonneg
-/
theorem IsBigOWith.const_mul_left {f : α -> R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')

/--
theorem `IsBigO.const_mul_left` / 定理 `IsBigO.const_mul_left`

English:
theorem IsBigO.const_mul_left
  given: {f : α -> R} (h : f =O[l] g) (c' : R)
  statement: (fun x => c' * f x) =O[l] g
  proof: let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO

中文:
定理 IsBigO.const_mul_left
  条件: {f : α -> R} (h : f =O[l] g) (c' : R)
  结论: (fun x => c' * f x) =O[l] g
  证明: let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO

Depends on / 依赖: const_mul_left, h.isBigOWith, hc.const_mul_left, isBigO, isBigOWith
-/
theorem IsBigO.const_mul_left {f : α -> R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO

/--
theorem `isBigOWith_self_const_mul'` / 定理 `isBigOWith_self_const_mul'`

English:
theorem isBigOWith_self_const_mul'
  given: (u : Rˣ) (f : α -> R) (l : Filter α)
  proof: (isBigOWith_const_mul_self ↑u⁻¹ (fun x => ↑u * f x) l).congr_left
    fun x => u.inv_mul_cancel_left (f x)

中文:
定理 isBigOWith_self_const_mul'
  条件: (u : Rˣ) (f : α -> R) (l : 滤子 α)
  证明: (isBigOWith_const_mul_self ↑u⁻¹ (fun x => ↑u * f x) l).congr_left
    fun x => u.inv_mul_cancel_left (f x)

Depends on / 依赖: congr_left, inv_mul_cancel_left, isBigOWith_const_mul_self, u.inv_mul_cancel_left
-/
theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α -> R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isBigOWith_const_mul_self ↑u⁻¹ (fun x => ↑u * f x) l).congr_left
    fun x => u.inv_mul_cancel_left (f x)

/--
theorem `isBigOWith_self_const_mul` / 定理 `isBigOWith_self_const_mul`

English:
theorem isBigOWith_self_const_mul
  given: {c : S} (hc : c != 0) (f : α -> S) (l : Filter α)
  proof: by
  simp [IsBigOWith, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]

中文:
定理 isBigOWith_self_const_mul
  条件: {c : S} (hc : c != 0) (f : α -> S) (l : 滤子 α)
  证明: by
  simp [IsBigOWith, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]

Depends on / 依赖: IsBigOWith, norm_ne_zero_iff, norm_ne_zero_iff.mpr
-/
theorem isBigOWith_self_const_mul {c : S} (hc : c != 0) (f : α -> S) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x => c * f x := by
  simp [IsBigOWith, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]

/--
theorem `isBigO_self_const_mul'` / 定理 `isBigO_self_const_mul'`

English:
theorem isBigO_self_const_mul'
  given: {c : R} (hc : IsUnit c) (f : α -> R) (l : Filter α)
  proof: let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO

中文:
定理 isBigO_self_const_mul'
  条件: {c : R} (hc : 是单位 c) (f : α -> R) (l : 滤子 α)
  证明: let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO

Depends on / 依赖: isBigO, isBigOWith_self_const_mul
-/
theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α -> R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO

/--
theorem `isBigO_self_const_mul` / 定理 `isBigO_self_const_mul`

English:
theorem isBigO_self_const_mul
  given: {c : S} (hc : c != 0) (f : α -> S) (l : Filter α)
  proof: (isBigOWith_self_const_mul hc f l).isBigO

中文:
定理 isBigO_self_const_mul
  条件: {c : S} (hc : c != 0) (f : α -> S) (l : 滤子 α)
  证明: (isBigOWith_self_const_mul hc f l).isBigO

Depends on / 依赖: isBigO, isBigOWith_self_const_mul
-/
theorem isBigO_self_const_mul {c : S} (hc : c != 0) (f : α -> S) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  (isBigOWith_self_const_mul hc f l).isBigO

/--
theorem `isBigO_const_mul_left_iff'` / 定理 `isBigO_const_mul_left_iff'`

English:
theorem isBigO_const_mul_left_iff'
  given: {f : α -> R} {c : R} (hc : IsUnit c)
  proof: ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

中文:
定理 isBigO_const_mul_left_iff'
  条件: {f : α -> R} {c : R} (hc : 是单位 c)
  证明: ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

Depends on / 依赖: const_mul_left, h.const_mul_left, isBigO_self_const_mul
-/
theorem isBigO_const_mul_left_iff' {f : α -> R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

/--
theorem `isBigO_const_mul_left_iff` / 定理 `isBigO_const_mul_left_iff`

English:
theorem isBigO_const_mul_left_iff
  given: {f : α -> S} {c : S} (hc : c != 0)
  proof: ⟨(isBigO_self_const_mul hc f l).trans, (isBigO_const_mul_self c f l).trans⟩

中文:
定理 isBigO_const_mul_left_iff
  条件: {f : α -> S} {c : S} (hc : c != 0)
  证明: ⟨(isBigO_self_const_mul hc f l).trans, (isBigO_const_mul_self c f l).trans⟩

Depends on / 依赖: isBigO_const_mul_self, isBigO_self_const_mul
-/
theorem isBigO_const_mul_left_iff {f : α -> S} {c : S} (hc : c != 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans, (isBigO_const_mul_self c f l).trans⟩

/--
theorem `IsLittleO.const_mul_left` / 定理 `IsLittleO.const_mul_left`

English:
theorem IsLittleO.const_mul_left
  given: {f : α -> R} (h : f =o[l] g) (c : R)
  statement: (fun x => c * f x) =o[l] g
  proof: (isBigO_const_mul_self c f l).trans_isLittleO h

中文:
定理 IsLittleO.const_mul_left
  条件: {f : α -> R} (h : f =o[l] g) (c : R)
  结论: (fun x => c * f x) =o[l] g
  证明: (isBigO_const_mul_self c f l).trans_isLittleO h

Depends on / 依赖: isBigO_const_mul_self, trans_isLittleO
-/
theorem IsLittleO.const_mul_left {f : α -> R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h

/--
theorem `isLittleO_const_mul_left_iff'` / 定理 `isLittleO_const_mul_left_iff'`

English:
theorem isLittleO_const_mul_left_iff'
  given: {f : α -> R} {c : R} (hc : IsUnit c)
  proof: ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩

中文:
定理 isLittleO_const_mul_left_iff'
  条件: {f : α -> R} {c : R} (hc : 是单位 c)
  证明: ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩

Depends on / 依赖: const_mul_left, h.const_mul_left, isBigO_self_const_mul, trans_isLittleO
-/
theorem isLittleO_const_mul_left_iff' {f : α -> R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩

/--
theorem `isLittleO_const_mul_left_iff` / 定理 `isLittleO_const_mul_left_iff`

English:
theorem isLittleO_const_mul_left_iff
  given: {f : α -> S} {c : S} (hc : c != 0)
  proof: ⟨(isBigO_self_const_mul hc f l).trans_isLittleO, (isBigO_const_mul_self c f l).trans_isLittleO⟩

中文:
定理 isLittleO_const_mul_left_iff
  条件: {f : α -> S} {c : S} (hc : c != 0)
  证明: ⟨(isBigO_self_const_mul hc f l).trans_isLittleO, (isBigO_const_mul_self c f l).trans_isLittleO⟩

Depends on / 依赖: isBigO_const_mul_self, isBigO_self_const_mul, trans_isLittleO
-/
theorem isLittleO_const_mul_left_iff {f : α -> S} {c : S} (hc : c != 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans_isLittleO, (isBigO_const_mul_self c f l).trans_isLittleO⟩

/--
theorem `IsBigOWith.of_const_mul_right` / 定理 `IsBigOWith.of_const_mul_right`

English:
theorem IsBigOWith.of_const_mul_right
  statement: {g : α -> R} {c : R} (hc' : 0 <= c')
  proof: h.trans (isBigOWith_const_mul_self c g l) hc'

中文:
定理 IsBigOWith.of_const_mul_right
  结论: {g : α -> R} {c : R} (hc' : 0 <= c')
  证明: h.trans (isBigOWith_const_mul_self c g l) hc'

Depends on / 依赖: h.trans, isBigOWith_const_mul_self
-/
theorem IsBigOWith.of_const_mul_right {g : α -> R} {c : R} (hc' : 0 <= c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'

/--
theorem `IsBigO.of_const_mul_right` / 定理 `IsBigO.of_const_mul_right`

English:
theorem IsBigO.of_const_mul_right
  given: {g : α -> R} {c : R} (h : f =O[l] fun x => c * g x)
  statement: f =O[l] g
  proof: let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO

中文:
定理 IsBigO.of_const_mul_right
  条件: {g : α -> R} {c : R} (h : f =O[l] fun x => c * g x)
  结论: f =O[l] g
  证明: let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO

Depends on / 依赖: cnonneg, exists_nonneg, h.exists_nonneg, hc.of_const_mul_right, isBigO, of_const_mul_right
-/
theorem IsBigO.of_const_mul_right {g : α -> R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO

/--
theorem `IsBigOWith.const_mul_right'` / 定理 `IsBigOWith.const_mul_right'`

English:
theorem IsBigOWith.const_mul_right'
  statement: {g : α -> R} {u : Rˣ} {c' : Real} (hc' : 0 <= c')
  proof: h.trans (isBigOWith_self_const_mul' _ _ _) hc'

中文:
定理 IsBigOWith.const_mul_right'
  结论: {g : α -> R} {u : Rˣ} {c' : 实数} (hc' : 0 <= c')
  证明: h.trans (isBigOWith_self_const_mul' _ _ _) hc'

Depends on / 依赖: h.trans, isBigOWith_self_const_mul
-/
theorem IsBigOWith.const_mul_right' {g : α -> R} {u : Rˣ} {c' : Real} (hc' : 0 <= c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'

/--
theorem `IsBigOWith.const_mul_right` / 定理 `IsBigOWith.const_mul_right`

English:
theorem IsBigOWith.const_mul_right
  statement: {g : α -> S} {c : S} (hc : c != 0) {c' : Real} (hc' : 0 <= c')
  proof: h.trans (isBigOWith_self_const_mul hc g l) hc'

中文:
定理 IsBigOWith.const_mul_right
  结论: {g : α -> S} {c : S} (hc : c != 0) {c' : 实数} (hc' : 0 <= c')
  证明: h.trans (isBigOWith_self_const_mul hc g l) hc'

Depends on / 依赖: h.trans, isBigOWith_self_const_mul
-/
theorem IsBigOWith.const_mul_right {g : α -> S} {c : S} (hc : c != 0) {c' : Real} (hc' : 0 <= c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul hc g l) hc'

/--
theorem `IsBigO.const_mul_right'` / 定理 `IsBigO.const_mul_right'`

English:
theorem IsBigO.const_mul_right'
  given: {g : α -> R} {c : R} (hc : IsUnit c) (h : f =O[l] g)
  proof: h.trans (isBigO_self_const_mul' hc g l)

中文:
定理 IsBigO.const_mul_right'
  条件: {g : α -> R} {c : R} (hc : 是单位 c) (h : f =O[l] g)
  证明: h.trans (isBigO_self_const_mul' hc g l)

Depends on / 依赖: h.trans, isBigO_self_const_mul
-/
theorem IsBigO.const_mul_right' {g : α -> R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)

/--
theorem `IsBigO.const_mul_right` / 定理 `IsBigO.const_mul_right`

English:
theorem IsBigO.const_mul_right
  given: {g : α -> S} {c : S} (hc : c != 0) (h : f =O[l] g)
  proof: match h.exists_nonneg with
  | ⟨_, hd, hd'⟩ => (hd'.const_mul_right hc hd).isBigO

中文:
定理 IsBigO.const_mul_right
  条件: {g : α -> S} {c : S} (hc : c != 0) (h : f =O[l] g)
  证明: match h.exists_nonneg with
  | ⟨_, hd, hd'⟩ => (hd'.const_mul_right hc hd).isBigO

Depends on / 依赖: const_mul_right, exists_nonneg, h.exists_nonneg, isBigO
-/
theorem IsBigO.const_mul_right {g : α -> S} {c : S} (hc : c != 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  match h.exists_nonneg with
  | ⟨_, hd, hd'⟩ => (hd'.const_mul_right hc hd).isBigO

/--
theorem `isBigO_const_mul_right_iff'` / 定理 `isBigO_const_mul_right_iff'`

English:
theorem isBigO_const_mul_right_iff'
  given: {g : α -> R} {c : R} (hc : IsUnit c)
  proof: ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

中文:
定理 isBigO_const_mul_right_iff'
  条件: {g : α -> R} {c : R} (hc : 是单位 c)
  证明: ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

Depends on / 依赖: const_mul_right, h.const_mul_right, h.of_const_mul_right, of_const_mul_right
-/
theorem isBigO_const_mul_right_iff' {g : α -> R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

/--
theorem `isBigO_const_mul_right_iff` / 定理 `isBigO_const_mul_right_iff`

English:
theorem isBigO_const_mul_right_iff
  given: {g : α -> S} {c : S} (hc : c != 0)
  proof: ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right hc⟩

中文:
定理 isBigO_const_mul_right_iff
  条件: {g : α -> S} {c : S} (hc : c != 0)
  证明: ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right hc⟩

Depends on / 依赖: const_mul_right, h.const_mul_right, h.of_const_mul_right, of_const_mul_right
-/
theorem isBigO_const_mul_right_iff {g : α -> S} {c : S} (hc : c != 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right hc⟩

/--
theorem `IsLittleO.of_const_mul_right` / 定理 `IsLittleO.of_const_mul_right`

English:
theorem IsLittleO.of_const_mul_right
  given: {g : α -> R} {c : R} (h : f =o[l] fun x => c * g x)
  proof: h.trans_isBigO (isBigO_const_mul_self c g l)

中文:
定理 IsLittleO.of_const_mul_right
  条件: {g : α -> R} {c : R} (h : f =o[l] fun x => c * g x)
  证明: h.trans_isBigO (isBigO_const_mul_self c g l)

Depends on / 依赖: h.trans_isBigO, isBigO_const_mul_self, trans_isBigO
-/
theorem IsLittleO.of_const_mul_right {g : α -> R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)

/--
theorem `IsLittleO.const_mul_right'` / 定理 `IsLittleO.const_mul_right'`

English:
theorem IsLittleO.const_mul_right'
  given: {g : α -> R} {c : R} (hc : IsUnit c) (h : f =o[l] g)
  proof: h.trans_isBigO (isBigO_self_const_mul' hc g l)

中文:
定理 IsLittleO.const_mul_right'
  条件: {g : α -> R} {c : R} (hc : 是单位 c) (h : f =o[l] g)
  证明: h.trans_isBigO (isBigO_self_const_mul' hc g l)

Depends on / 依赖: h.trans_isBigO, isBigO_self_const_mul, trans_isBigO
-/
theorem IsLittleO.const_mul_right' {g : α -> R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)

/--
theorem `IsLittleO.const_mul_right` / 定理 `IsLittleO.const_mul_right`

English:
theorem IsLittleO.const_mul_right
  given: {g : α -> S} {c : S} (hc : c != 0) (h : f =o[l] g)
  proof: h.trans_isBigO isBigO_self_const_mul hc g l

中文:
定理 IsLittleO.const_mul_right
  条件: {g : α -> S} {c : S} (hc : c != 0) (h : f =o[l] g)
  证明: h.trans_isBigO isBigO_self_const_mul hc g l

Depends on / 依赖: h.trans_isBigO, isBigO_self_const_mul, trans_isBigO
-/
theorem IsLittleO.const_mul_right {g : α -> S} {c : S} (hc : c != 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
h.trans_isBigO isBigO_self_const_mul hc g l

/--
theorem `isLittleO_const_mul_right_iff'` / 定理 `isLittleO_const_mul_right_iff'`

English:
theorem isLittleO_const_mul_right_iff'
  given: {g : α -> R} {c : R} (hc : IsUnit c)
  proof: ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

中文:
定理 isLittleO_const_mul_right_iff'
  条件: {g : α -> R} {c : R} (hc : 是单位 c)
  证明: ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

Depends on / 依赖: const_mul_right, h.const_mul_right, h.of_const_mul_right, of_const_mul_right
-/
theorem isLittleO_const_mul_right_iff' {g : α -> R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

/--
theorem `isLittleO_const_mul_right_iff` / 定理 `isLittleO_const_mul_right_iff`

English:
theorem isLittleO_const_mul_right_iff
  given: {g : α -> S} {c : S} (hc : c != 0)
  proof: ⟨fun h => h.of_const_mul_right, fun h => h.trans_isBigO (isBigO_self_const_mul hc g l)⟩

中文:
定理 isLittleO_const_mul_right_iff
  条件: {g : α -> S} {c : S} (hc : c != 0)
  证明: ⟨fun h => h.of_const_mul_right, fun h => h.trans_isBigO (isBigO_self_const_mul hc g l)⟩

Depends on / 依赖: h.of_const_mul_right, h.trans_isBigO, isBigO_self_const_mul, of_const_mul_right, trans_isBigO
-/
theorem isLittleO_const_mul_right_iff {g : α -> S} {c : S} (hc : c != 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.trans_isBigO (isBigO_self_const_mul hc g l)⟩


/--
theorem `IsBigOWith.mul` / 定理 `IsBigOWith.mul`

English:
theorem IsBigOWith.mul
  statement: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} {c₁ c₂ : Real} (h₁ : IsBigOWith c₁ l f₁ g₁)
  proof: by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul]; rw [mul_mul_mul_comm]

中文:
定理 IsBigOWith.mul
  结论: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} {c₁ c₂ : 实数} (h₁ : IsBigOWith c₁ l f₁ g₁)
  证明: by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul]; rw [mul_mul_mul_comm]

Depends on / 依赖: IsBigOWith_def, convert, filter_upwards, le_trans, mul_le_mul, mul_mul_mul_comm, norm_mul, norm_mul_le, norm_nonneg
-/
theorem IsBigOWith.mul {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} {c₁ c₂ : Real} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul]; rw [mul_mul_mul_comm]

/--
theorem `IsBigO.mul` / 定理 `IsBigO.mul`

English:
theorem IsBigO.mul
  given: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂)
  proof: let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO

中文:
定理 IsBigO.mul
  条件: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂)
  证明: let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO

Depends on / 依赖: hc.mul, isBigO, isBigOWith
-/
theorem IsBigO.mul {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO

/--
theorem `IsBigO.mul_isLittleO` / 定理 `IsBigO.mul_isLittleO`

English:
theorem IsBigO.mul_isLittleO
  given: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂)
  proof: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

中文:
定理 IsBigO.mul_isLittleO
  条件: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂)
  证明: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

Depends on / 依赖: IsLittleO_def, congr_const, div_pos, exists_pos, ne_of_gt
-/
theorem IsBigO.mul_isLittleO {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

/--
theorem `IsLittleO.mul_isBigO` / 定理 `IsLittleO.mul_isBigO`

English:
theorem IsLittleO.mul_isBigO
  given: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂)
  proof: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

中文:
定理 IsLittleO.mul_isBigO
  条件: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂)
  证明: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

Depends on / 依赖: IsLittleO_def, congr_const, div_pos, exists_pos, ne_of_gt
-/
theorem IsLittleO.mul_isBigO {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

/--
theorem `IsLittleO.mul` / 定理 `IsLittleO.mul`

English:
theorem IsLittleO.mul
  given: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂)
  proof: h₁.mul_isBigO h₂.isBigO

中文:
定理 IsLittleO.mul
  条件: {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂)
  证明: h₁.mul_isBigO h₂.isBigO

Depends on / 依赖: isBigO, mul_isBigO
-/
theorem IsLittleO.mul {f₁ f₂ : α -> R} {g₁ g₂ : α -> S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.isBigO

/--
theorem `IsBigOWith.pow'` / 定理 `IsBigOWith.pow'`

English:
theorem IsBigOWith.pow'
  given: [NormOneClass S] {f : α -> R} {g : α -> S} (h : IsBigOWith c l f g)
  proof: NormOneClass.nontrivial
    simpa using isBigOWith_const_const (1 : R) (one_ne_zero' S) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using (IsBigOWith.pow' h (n + 1)).mul h

中文:
定理 IsBigOWith.pow'
  条件: [NormOne类 S] {f : α -> R} {g : α -> S} (h : IsBigOWith c l f g)
  证明: NormOneClass.nontrivial
    simpa using isBigOWith_const_const (1 : R) (one_ne_zero' S) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using (IsBigOWith.pow' h (n + 1)).mul h

Depends on / 依赖: NormOneClass, NormOneClass.nontrivial, nontrivial
-/
theorem IsBigOWith.pow' [NormOneClass S] {f : α -> R} {g : α -> S} (h : IsBigOWith c l f g) :
    forall n : Nat, IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n => c ^ (n + 1))
      l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by
    have : Nontrivial S := NormOneClass.nontrivial
    simpa using isBigOWith_const_const (1 : R) (one_ne_zero' S) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using (IsBigOWith.pow' h (n + 1)).mul h

/--
theorem `IsBigOWith.pow` / 定理 `IsBigOWith.pow`

English:
theorem IsBigOWith.pow
  statement: [NormOneClass R] [NormOneClass S]

中文:
定理 IsBigOWith.pow
  结论: [NormOne类 R] [NormOne类 S]
-/
theorem IsBigOWith.pow [NormOneClass R] [NormOneClass S]
    {f : α -> R} {g : α -> S} (h : IsBigOWith c l f g) :
    forall n : Nat, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)

/--
theorem `IsBigOWith.of_pow` / 定理 `IsBigOWith.of_pow`

English:
theorem IsBigOWith.of_pow
  statement: [NormOneClass S] {n : Nat} {f : α -> S} {g : α -> R}
  proof: IsBigOWith.of_bound (h.weaken hc).bound.mono fun x hx =>
le_of_pow_le_pow_left₀ hn (by positivity)
      calc
        ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
        _ <= c' ^ n * ‖g x ^ n‖ := hx
        _ <= c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
        _ = (c' * ‖g x

中文:
定理 IsBigOWith.of_pow
  结论: [NormOne类 S] {n : 自然数} {f : α -> S} {g : α -> R}
  证明: IsBigOWith.of_bound (h.weaken hc).bound.mono fun x hx =>
le_of_pow_le_pow_left₀ hn (by positivity)
      calc
        ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
        _ <= c' ^ n * ‖g x ^ n‖ := hx
        _ <= c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
        _ = (c' * ‖g x

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, bot_lt, bound.mono, h.weaken, hn.bot_lt, mul_pow, norm_pow, norm_pow_le, of_bound, weaken
-/
theorem IsBigOWith.of_pow [NormOneClass S] {n : Nat} {f : α -> S} {g : α -> R}
    (h : IsBigOWith c l (f ^ n) (g ^ n)) (hn : n != 0) (hc : c <= c' ^ n) (hc' : 0 <= c') :
    IsBigOWith c' l f g :=
IsBigOWith.of_bound (h.weaken hc).bound.mono fun x hx =>
le_of_pow_le_pow_left₀ hn (by positivity)
      calc
        ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
        _ <= c' ^ n * ‖g x ^ n‖ := hx
        _ <= c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
        _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm

/--
theorem `IsBigO.pow` / 定理 `IsBigO.pow`

English:
theorem IsBigO.pow
  given: [NormOneClass S] {f : α -> R} {g : α -> S} (h : f =O[l] g) (n : Nat)
  proof: let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩

中文:
定理 IsBigO.pow
  条件: [NormOne类 S] {f : α -> R} {g : α -> S} (h : f =O[l] g) (n : 自然数)
  证明: let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩

Depends on / 依赖: h.isBigOWith, hC.pow, isBigOWith, isBigO_iff_isBigOWith
-/
theorem IsBigO.pow [NormOneClass S] {f : α -> R} {g : α -> S} (h : f =O[l] g) (n : Nat) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩

/--
theorem `IsLittleO.pow` / 定理 `IsLittleO.pow`

English:
theorem IsLittleO.pow
  given: {f : α -> R} {g : α -> S} (h : f =o[l] g) {n : Nat} (hn : 0 < n)
  proof: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; clear hn
  induction n with
  | zero => simpa only [pow_one]
  | succ n ihn => convert! ihn.mul h <;> simp [pow_succ]

中文:
定理 IsLittleO.pow
  条件: {f : α -> R} {g : α -> S} (h : f =o[l] g) {n : 自然数} (hn : 0 < n)
  证明: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; clear hn
  induction n with
  | zero => simpa only [pow_one]
  | succ n ihn => convert! ihn.mul h <;> simp [pow_succ]

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, convert, exists_eq_succ_of_ne_zero, hn.ne, ihn.mul, pow_one, pow_succ
-/
theorem IsLittleO.pow {f : α -> R} {g : α -> S} (h : f =o[l] g) {n : Nat} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; clear hn
  induction n with
  | zero => simpa only [pow_one]
  | succ n ihn => convert! ihn.mul h <;> simp [pow_succ]

/--
theorem `IsLittleO.of_pow` / 定理 `IsLittleO.of_pow`

English:
theorem IsLittleO.of_pow
  statement: [NormOneClass S] {f : α -> S} {g : α -> R} {n : Nat}
  proof: IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le

中文:
定理 IsLittleO.of_pow
  结论: [NormOne类 S] {f : α -> S} {g : α -> R} {n : 自然数}
  证明: IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, h.def, hc.le, le_rfl, of_isBigOWith, of_pow, pow_pos
-/
theorem IsLittleO.of_pow [NormOneClass S] {f : α -> S} {g : α -> R} {n : Nat}
    (h : (f ^ n) =o[l] (g ^ n)) (hn : n != 0) : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le


/--
theorem `IsBigOWith.inv_rev` / 定理 `IsBigOWith.inv_rev`

English:
theorem IsBigOWith.inv_rev
  statement: {f : α -> 𝕜} {g : α -> 𝕜'} (h : IsBigOWith c l f g)
  proof: by
  refine IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => ?_))
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero, le_rfl]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_anti₀

中文:
定理 IsBigOWith.inv_rev
  结论: {f : α -> 𝕜} {g : α -> 𝕜'} (h : IsBigOWith c l f g)
  证明: by
  refine IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => ?_))
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero, le_rfl]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_anti₀

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, div_eq_inv_mul, eq_or_ne, h.bound.mp, inv_zero, le_rfl, mul_inv, mul_zero, norm_inv, norm_nonneg, norm_pos_iff, norm_zero, of_bound, pos_of_mul_pos_left, replace, trans_le
-/
theorem IsBigOWith.inv_rev {f : α -> 𝕜} {g : α -> 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : forallᶠ x in l, f x = 0 -> g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => ?_))
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero, le_rfl]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_anti₀ (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff₀ hc] using! hle

/--
theorem `IsBigO.inv_rev` / 定理 `IsBigO.inv_rev`

English:
theorem IsBigO.inv_rev
  statement: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =O[l] g)
  proof: let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO

中文:
定理 IsBigO.inv_rev
  结论: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =O[l] g)
  证明: let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO

Depends on / 依赖: h.isBigOWith, hc.inv_rev, inv_rev, isBigO, isBigOWith
-/
theorem IsBigO.inv_rev {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =O[l] g)
    (h₀ : forallᶠ x in l, f x = 0 -> g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO

/--
theorem `IsLittleO.inv_rev` / 定理 `IsLittleO.inv_rev`

English:
theorem IsLittleO.inv_rev
  statement: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =o[l] g)
  proof: IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀

中文:
定理 IsLittleO.inv_rev
  结论: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =o[l] g)
  证明: IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀

Depends on / 依赖: IsLittleO, IsLittleO.of_isBigOWith, h.def, inv_rev, of_isBigOWith
-/
theorem IsLittleO.inv_rev {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =o[l] g)
    (h₀ : forallᶠ x in l, f x = 0 -> g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀

/-! ### Sum -/

section Sum

variable {ι : Type*} {A : ι -> α -> E'} {C : ι -> Real} {s : Finset ι}

/--
theorem `IsBigOWith.sum` / 定理 `IsBigOWith.sum`

English:
theorem IsBigOWith.sum
  given: (h : forall i in s, IsBigOWith (C i) l (A i) g)
  proof: by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty]
      apply isBigOWith_zero'
  | cons i s is IH =>
    simp only [Finset.sum_cons, Finset.forall_mem_cons] at h ⊢
    exact h.1.add (IH h.2)

中文:
定理 IsBigOWith.求和
  条件: (h : 对任意 i in s, IsBigOWith (C i) l (A i) g)
  证明: by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty]
      apply isBigOWith_zero'
  | cons i s is IH =>
    simp only [Finset.sum_cons, Finset.forall_mem_cons] at h ⊢
    exact h.1.add (IH h.2)
-/
@[to_fun] theorem IsBigOWith.sum (h : forall i in s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i in s, C i) l (∑ i in s, A i) g := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty]
      apply isBigOWith_zero'
  | cons i s is IH =>
    simp only [Finset.sum_cons, Finset.forall_mem_cons] at h ⊢
    exact h.1.add (IH h.2)

/--
theorem `IsBigO.sum` / 定理 `IsBigO.sum`

English:
theorem IsBigO.sum
  given: (h : forall i in s, A i =O[l] g)
  statement: (∑ i in s, A i) =O[l] g
  proof: by
  simp only [IsBigO_def] at *
  choose! C hC using h
  exact ⟨_, IsBigOWith.sum hC⟩

中文:
定理 IsBigO.求和
  条件: (h : 对任意 i in s, A i =O[l] g)
  结论: (∑ i in s, A i) =O[l] g
  证明: by
  simp only [IsBigO_def] at *
  choose! C hC using h
  exact ⟨_, IsBigOWith.sum hC⟩
-/
@[to_fun] theorem IsBigO.sum (h : forall i in s, A i =O[l] g) : (∑ i in s, A i) =O[l] g := by
  simp only [IsBigO_def] at *
  choose! C hC using h
  exact ⟨_, IsBigOWith.sum hC⟩

/--
theorem `IsLittleO.sum` / 定理 `IsLittleO.sum`

English:
theorem IsLittleO.sum
  given: (h : forall i in s, A i =o[l] g')
  statement: (∑ i in s, A i) =o[l] g'
  proof: by
  exact Finset.sum_induction A (· =o[l] g') (fun _ _ => .add) (isLittleO_zero ..) h

中文:
定理 IsLittleO.求和
  条件: (h : 对任意 i in s, A i =o[l] g')
  结论: (∑ i in s, A i) =o[l] g'
  证明: by
  exact Finset.sum_induction A (· =o[l] g') (fun _ _ => .add) (isLittleO_zero ..) h
-/
@[to_fun] theorem IsLittleO.sum (h : forall i in s, A i =o[l] g') : (∑ i in s, A i) =o[l] g' := by
  exact Finset.sum_induction A (· =o[l] g') (fun _ _ => .add) (isLittleO_zero ..) h

variable {B : ι -> α -> Real}

/--
theorem `IsBigOWith.sum_congr` / 定理 `IsBigOWith.sum_congr`

English:
theorem IsBigOWith.sum_congr
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isBigOWith_zero]
  simp only [IsBigOWith_def] at *
  filter_upwards [(eventually_all_finset s).mpr hAB]
    with x hx
  calc
    ‖∑ i in s, A i x‖ <= ∑ i in s, ‖A i x‖ := norm_sum_le ..
    _ <= ∑ i in s, C i * ‖B i x‖ := Finset.sum_le_sum (fu

中文:
定理 IsBigOWith.sum_congr
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isBigOWith_zero]
  simp only [IsBigOWith_def] at *
  filter_upwards [(eventually_all_finset s).mpr hAB]
    with x hx
  calc
    ‖∑ i in s, A i x‖ <= ∑ i in s, ‖A i x‖ := norm_sum_le ..
    _ <= ∑ i in s, C i * ‖B i x‖ := Finset.sum_le_sum (fu

Depends on / 依赖: Finset, Finset.le_sup, Finset.sum_le_sum, IsBigOWith_def, _eq_csSup_image, _iff, eq_empty_or_nonempty, eventually_all_finset, filter_upwards, isBigOWith_zero, le_sup, norm_sum_le, s.eq_empty_or_nonempty, s.sup, sum_le_sum
-/
theorem IsBigOWith.sum_congr
    (hAB : forall i in s, IsBigOWith (C i) l (A i) (B i)) :
    IsBigOWith (sSup (C '' s)) l (fun H => ∑ i in s, A i H) (fun H => ∑ i in s, ‖B i H‖) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isBigOWith_zero]
  simp only [IsBigOWith_def] at *
  filter_upwards [(eventually_all_finset s).mpr hAB]
    with x hx
  calc
    ‖∑ i in s, A i x‖ <= ∑ i in s, ‖A i x‖ := norm_sum_le ..
    _ <= ∑ i in s, C i * ‖B i x‖ := Finset.sum_le_sum (fun j hj => hx j hj)
    _ <= ∑ i in s, sSup (C '' s) * ‖B i x‖ := by
        refine Finset.sum_le_sum ?_
        intro j hj; gcongr
        rw [← s.sup'_eq_csSup_image hs]; rw [Finset.le_sup'_iff]; use j
    _ = sSup (C '' s) * ∑ i in s, ‖B i x‖ := (Finset.mul_sum ..).symm
    _ = sSup (C '' s) * ‖∑ i in s, ‖B i x‖‖ := by
      congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]

/--
theorem `IsBigO.sum_congr` / 定理 `IsBigO.sum_congr`

English:
theorem IsBigO.sum_congr
  given: (hAB : forall i in s, A i =O[l] B i)
  proof: by
  simp only [IsBigO_def] at *
  choose! C hC using hAB
  exact ⟨_, IsBigOWith.sum_congr hC⟩

中文:
定理 IsBigO.sum_congr
  条件: (hAB : 对任意 i in s, A i =O[l] B i)
  证明: by
  simp only [IsBigO_def] at *
  choose! C hC using hAB
  exact ⟨_, IsBigOWith.sum_congr hC⟩

Depends on / 依赖: IsBigOWith, IsBigOWith.sum_congr, IsBigO_def, sum_congr
-/
theorem IsBigO.sum_congr (hAB : forall i in s, A i =O[l] B i) :
    (fun H => ∑ i in s, A i H) =O[l] fun H => ∑ i in s, ‖B i H‖ := by
  simp only [IsBigO_def] at *
  choose! C hC using hAB
  exact ⟨_, IsBigOWith.sum_congr hC⟩

/--
theorem `IsLittleO.sum_congr` / 定理 `IsLittleO.sum_congr`

English:
theorem IsLittleO.sum_congr
  given: (hAB : forall i in s, A i =o[l] B i)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp [isLittleO_zero]
  | cons i s his h =>
  simp_rw [Finset.sum_cons]
  calc (fun H => A i H + ∑ j in s, A j H)
      =o[l] fun H => ‖B i H‖ + ‖∑ j in s, ‖B j H‖‖ :=
          (hAB i (by simp)).add_add (h (fun j hj => hAB j (by simp [h

中文:
定理 IsLittleO.sum_congr
  条件: (hAB : 对任意 i in s, A i =o[l] B i)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp [isLittleO_zero]
  | cons i s his h =>
  simp_rw [Finset.sum_cons]
  calc (fun H => A i H + ∑ j in s, A j H)
      =o[l] fun H => ‖B i H‖ + ‖∑ j in s, ‖B j H‖‖ :=
          (hAB i (by simp)).add_add (h (fun j hj => hAB j (by simp [h

Depends on / 依赖: Eventually, Eventually.of_forall, Finset, Finset.cons_induction, Finset.sum_cons, Finset.sum_nonneg, Real.norm_of_nonneg, add_add, congr_arg, cons_induction, isLittleO_zero, norm_nonneg, norm_of_nonneg, of_forall, simp_rw, sum_cons, sum_nonneg
-/
theorem IsLittleO.sum_congr (hAB : forall i in s, A i =o[l] B i) :
    (fun H => ∑ i in s, A i H) =o[l] fun H => ∑ i in s, ‖B i H‖ := by
  induction s using Finset.cons_induction with
  | empty => simp [isLittleO_zero]
  | cons i s his h =>
  simp_rw [Finset.sum_cons]
  calc (fun H => A i H + ∑ j in s, A j H)
      =o[l] fun H => ‖B i H‖ + ‖∑ j in s, ‖B j H‖‖ :=
          (hAB i (by simp)).add_add (h (fun j hj => hAB j (by simp [hj])))
    _ =ᶠ[l] fun H => ‖B i H‖ + ∑ j in s, ‖B j H‖ := by
        refine Eventually.of_forall fun H => congr_arg (‖B i H‖ + ·) ?_
        exact Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/--
theorem `IsBigOWith.sum_congr'` / 定理 `IsBigOWith.sum_congr'`

English:
theorem IsBigOWith.sum_congr'
  statement: {C : Real} {i : α -> Finset ι}
  proof: by
  simp only [IsBigOWith_def] at *
  obtain ⟨s₁, hs₁, s₂, hs₂, hbound⟩ := Filter.eventually_prod_iff.mp hAB
  filter_upwards [hs₂] with H hH
  calc
    ‖∑ j in i H, A j H‖ <= ∑ j in i H, ‖A j H‖ := norm_sum_le ..
    _ <= ∑ j in i H, C * ‖B j H‖ :=
        Finset.sum_le_sum fun j _ => hbound (Filt

中文:
定理 IsBigOWith.sum_congr'
  结论: {C : 实数} {i : α -> 有限集 ι}
  证明: by
  simp only [IsBigOWith_def] at *
  obtain ⟨s₁, hs₁, s₂, hs₂, hbound⟩ := Filter.eventually_prod_iff.mp hAB
  filter_upwards [hs₂] with H hH
  calc
    ‖∑ j in i H, A j H‖ <= ∑ j in i H, ‖A j H‖ := norm_sum_le ..
    _ <= ∑ j in i H, C * ‖B j H‖ :=
        Finset.sum_le_sum fun j _ => hbound (Filt

Depends on / 依赖: Filter, Filter.eventually_prod_iff.mp, Filter.eventually_top.mp, Finset, Finset.mul_sum, Finset.sum_le_sum, Finset.sum_nonneg, IsBigOWith_def, Real.norm_of_nonneg, eventually_prod_iff, eventually_top, filter_upwards, hbound, mul_sum, norm_nonneg, norm_of_nonneg, norm_sum_le, sum_le_sum, sum_nonneg
-/
theorem IsBigOWith.sum_congr' {C : Real} {i : α -> Finset ι}
    (hAB : IsBigOWith C (⊤ ×ˢ l) A.uncurry B.uncurry) :
    IsBigOWith C l (fun H => ∑ j in i H, A j H) (fun H => ∑ j in i H, ‖B j H‖) := by
  simp only [IsBigOWith_def] at *
  obtain ⟨s₁, hs₁, s₂, hs₂, hbound⟩ := Filter.eventually_prod_iff.mp hAB
  filter_upwards [hs₂] with H hH
  calc
    ‖∑ j in i H, A j H‖ <= ∑ j in i H, ‖A j H‖ := norm_sum_le ..
    _ <= ∑ j in i H, C * ‖B j H‖ :=
        Finset.sum_le_sum fun j _ => hbound (Filter.eventually_top.mp hs₁ j) hH
    _ = C * ∑ j in i H, ‖B j H‖ := (Finset.mul_sum ..).symm
    _ = C * ‖∑ j in i H, ‖B j H‖‖ := by
        congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]

/--
theorem `IsBigO.sum_congr'` / 定理 `IsBigO.sum_congr'`

English:
theorem IsBigO.sum_congr'
  given: {i : α -> Finset ι} (hAB : A.uncurry =O[⊤ ×ˢ l] B.uncurry)
  proof: by
  simp only [IsBigO_def]
  obtain ⟨C, hC⟩ := hAB.isBigOWith
  exact ⟨C, hC.sum_congr'⟩

中文:
定理 IsBigO.sum_congr'
  条件: {i : α -> 有限集 ι} (hAB : A.uncurry =O[⊤ ×ˢ l] B.uncurry)
  证明: by
  simp only [IsBigO_def]
  obtain ⟨C, hC⟩ := hAB.isBigOWith
  exact ⟨C, hC.sum_congr'⟩

Depends on / 依赖: IsBigO_def, hAB.isBigOWith, hC.sum_congr, isBigOWith, sum_congr
-/
theorem IsBigO.sum_congr' {i : α -> Finset ι} (hAB : A.uncurry =O[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j in i H, A j H) =O[l] (fun H => ∑ j in i H, ‖B j H‖) := by
  simp only [IsBigO_def]
  obtain ⟨C, hC⟩ := hAB.isBigOWith
  exact ⟨C, hC.sum_congr'⟩

/--
theorem `IsLittleO.sum_congr'` / 定理 `IsLittleO.sum_congr'`

English:
theorem IsLittleO.sum_congr'
  given: {i : α -> Finset ι} (hAB : A.uncurry =o[⊤ ×ˢ l] B.uncurry)
  proof: by
  rw [isLittleO_iff_forall_isBigOWith] at *
  intro c hc
  exact (hAB hc).sum_congr'

中文:
定理 IsLittleO.sum_congr'
  条件: {i : α -> 有限集 ι} (hAB : A.uncurry =o[⊤ ×ˢ l] B.uncurry)
  证明: by
  rw [isLittleO_iff_forall_isBigOWith] at *
  intro c hc
  exact (hAB hc).sum_congr'

Depends on / 依赖: isLittleO_iff_forall_isBigOWith, sum_congr
-/
theorem IsLittleO.sum_congr' {i : α -> Finset ι} (hAB : A.uncurry =o[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j in i H, A j H) =o[l] (fun H => ∑ j in i H, ‖B j H‖) := by
  rw [isLittleO_iff_forall_isBigOWith] at *
  intro c hc
  exact (hAB hc).sum_congr'

end Sum

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `IsBigOWith` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

section EventuallyMulDivCancel

variable {u v : α -> 𝕜}

/--
theorem `IsBigOWith.eventually_mul_div_cancel` / 定理 `IsBigOWith.eventually_mul_div_cancel`

English:
theorem IsBigOWith.eventually_mul_div_cancel
  given: (h : IsBigOWith c l u v)
  statement: u / v * v =ᶠ[l] u
  proof: Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy

中文:
定理 IsBigOWith.eventually_mul_div_cancel
  条件: (h : IsBigOWith c l u v)
  结论: u / v * v =ᶠ[l] u
  证明: Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy

Depends on / 依赖: Eventually, Eventually.mono, div_mul_cancel_of_imp, h.bound
-/
theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy

/--
theorem `IsBigO.eventually_mul_div_cancel` / 定理 `IsBigO.eventually_mul_div_cancel`

English:
theorem IsBigO.eventually_mul_div_cancel
  given: (h : u =O[l] v)
  statement: u / v * v =ᶠ[l] u
  proof: let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel

中文:
定理 IsBigO.eventually_mul_div_cancel
  条件: (h : u =O[l] v)
  结论: u / v * v =ᶠ[l] u
  证明: let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel

Depends on / 依赖: eventually_mul_div_cancel, h.isBigOWith, hc.eventually_mul_div_cancel, isBigOWith
-/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel

/--
theorem `IsLittleO.eventually_mul_div_cancel` / 定理 `IsLittleO.eventually_mul_div_cancel`

English:
theorem IsLittleO.eventually_mul_div_cancel
  given: (h : u =o[l] v)
  statement: u / v * v =ᶠ[l] u
  proof: (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel

中文:
定理 IsLittleO.eventually_mul_div_cancel
  条件: (h : u =o[l] v)
  结论: u / v * v =ᶠ[l] u
  证明: (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel

Depends on / 依赖: eventually_mul_div_cancel, forall_isBigOWith, h.forall_isBigOWith, zero_lt_one
-/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel

end EventuallyMulDivCancel

end Asymptotics
