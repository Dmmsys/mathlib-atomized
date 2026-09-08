/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

# Finiteness properties under localization

In this file we establish behaviour of `Module.Finite` under localizations.

## Main results

- `Module.Finite.of_isLocalizedModule`: If `M` is a finite `R`-module,
  `S` is a submonoid of `R`, `Rₚ` is the localization of `R` at `S`
  and `Mₚ` is the localization of `M` at `S`, then `Mₚ` is a finite
  `Rₚ`-module.
- `Module.Finite.of_localizationSpan_finite`: If `M` is an `R`-module
  and `{ r }` is a finite set generating the unit ideal such that
  `Mᵣ` is a finite `Rᵣ`-module for each `r`, then `M` is a finite `R`-module.

## TODO

* Move the results that `Module.Finite` over a semilocal ring is a local property from
  `Mathlib/RingTheory/LocalProperties/Semilocal.lean` to this file.

-/

@[expose] public section

universe u v w t

section

open scoped Pointwise

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type*) [CommSemiring R'] [CommSemiring S']
variable [Algebra R R'] [Algebra S S']

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the span of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
span of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
/-
**IsLocalization.smul_mem_finsetIntegerMultiple_span** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsLocalization.smul_mem_finsetIntegerMultiple_span [Algebra R S] [Algebra 
R S'] [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S
) (s : Finset S') (hx : algebraMap S S' x in Submodule.span R (s : Set S')) : ex
ists m : M, m • x in Submodule.span R (IsLocalization.finsetIntegerMultiple (M.m
ap (algebraMap R S)) s : Set S)
参数：M.map (algebraMap R S)；x : S；s : Finset S'；hx : algebraMap S S' x in Submodul
e.span R (s : Set S')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.finsetIntegerMultiple_image`：finsetIntegerMultiple_image 
[DecidableEq R] (s : Finset S) : algebraMap R S '' finsetIntegerMultiple M s = c
ommonDenomOfFinset M s • (s : Se…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用引理 `AlgHom.coe_toLinearMap`：coe_toLinearMap : ⇑φ.toLinearMap = φ
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Submodule.span_smul`：span_smul (a : α) (s : Set M) : span R (a • s) = a 
• span R s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the span of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
span of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
theorem IsLocalization.smul_mem_finsetIntegerMultiple_span [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x ∈ Submodule.span R (s : Set S')) :
    ∃ m : M, m • x ∈
      Submodule.span R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  let g : S →ₐ[R] S' :=
    AlgHom.mk' (algebraMap S S') fun c x => by simp [Algebra.algebraMap_eq_smul_one]
  have g_apply : ∀ x, g x = algebraMap S S' x := fun _ => rfl
  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := IsLocalization.commonDenomOfFinset (M.map (algebraMap R S)) s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨y', hy', e : algebraMap R S y' = y⟩ := y.prop
  have : algebraMap R S y' • (s : Set S') = y' • (s : Set S') := by
    simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  rw [← e, this] at hx₁
  replace hx₁ := congr_arg (Submodule.span R) hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y' • Submodule.span R (s : Set S') := Set.smul_mem_smul_set hx
  rw [hx₁, ← g_apply, ← map_smul g, g_apply, ← Algebra.linearMap_apply, ← AlgHom.coe_toLinearMap,
    ← Submodule.map_span] at hx
  -- Since `x` falls in the span of `s` in `S'`, `y' • x : S` falls in the span of `s'` in `S'`.
  -- That is, there exists some `x' : S` in the span of `s'` in `S` and `x' = y' • x` in `S'`.
  -- Thus `a • (y' • x) = a • x' ∈ span s'` in `S` for some `a ∈ M`.
  obtain ⟨x', hx', hx'' : algebraMap _ _ _ = _⟩ := hx
  obtain ⟨⟨_, a, ha₁, rfl⟩, ha₂⟩ :=
    (IsLocalization.eq_iff_exists (M.map (algebraMap R S)) S').mp hx''
  use (⟨a, ha₁⟩ : M) * (⟨y', hy'⟩ : M)
  convert!
    (Submodule.span R
          (IsLocalization.finsetIntegerMultiple (Submonoid.map (algebraMap R S) M) s :
            Set S)).smul_mem
      a hx' using 1
  convert! ha₂.symm using 1
  · rw [Subtype.coe_mk, Submonoid.smul_def, Submonoid.coe_mul, ← smul_smul]
    exact Algebra.smul_def _ _
  · exact Algebra.smul_def _ _

/-- If `M` is an `R' = S⁻¹R` module, and `x ∈ span R' s`,
then `t • x ∈ span R s` for some `t : S`. -/
/-
**multiple_mem_span_of_mem_localization_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiple_mem_span_of_mem_localization_span {N : Type*} [AddCommMonoid N] [
Module R N] [Module R' N] [IsScalarTower R R' N] [IsLocalization M R'] (s : Set 
N) (x : N) (hx : x in Submodule.span R' s) : exists (t : M), t • x in Submodule.
span R s
参数：s : Set N；x : N；hx : x in Submodule.span R' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_finite_of_mem_span`：mem_span_finite_of_mem_span {S : 
Set M} {x : M} (hx : x in span R S) : exists T : Finset M, ↑T subseteq S ∧ x in 
span R (T : Set M)
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…

--- 原说明 ---
If `M` is an `R' = S⁻¹R` module, and `x ∈ span R' s`,
then `t • x ∈ span R s` for some `t : S`.
-/
theorem multiple_mem_span_of_mem_localization_span
    {N : Type*} [AddCommMonoid N] [Module R N] [Module R' N]
    [IsScalarTower R R' N] [IsLocalization M R'] (s : Set N) (x : N)
    (hx : x ∈ Submodule.span R' s) : ∃ (t : M), t • x ∈ Submodule.span R s := by
  classical
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : ∃ t : M, t • x ∈ Submodule.span R (s' : Set N)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x with
  | empty => use 1; simpa using hs'
  | insert a s _ hs =>
  simp only [Finset.coe_insert,
    Submodule.mem_span_insert] at hs' ⊢
  rcases hs' with ⟨y, z, hz, rfl⟩
  rcases IsLocalization.surj M y with ⟨⟨y', s'⟩, e⟩
  apply congrArg (fun x ↦ x • a) at e
  simp only [algebraMap_smul] at e
  rcases hs _ hz with ⟨t, ht⟩
  refine ⟨t * s', t * y', _, (Submodule.span R (s : Set N)).smul_mem s' ht, ?_⟩
  rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, ← smul_smul, ← e, mul_comm, ← Algebra.smul_def]
  simp [Submonoid.smul_def]

/-- If `S` is an `R' = M⁻¹R` algebra, and `x ∈ adjoin R' s`,
then `t • x ∈ adjoin R s` for some `t : M`. -/
/-
**multiple_mem_adjoin_of_mem_localization_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiple_mem_adjoin_of_mem_localization_adjoin [Algebra R' S] [Algebra R S
] [IsScalarTower R R' S] [IsLocalization M R'] (s : Set S) (x : S) (hx : x in Al
gebra.adjoin R' s) : exists t : M, t • x in Algebra.adjoin R s
参数：s : Set S；x : S；hx : x in Algebra.adjoin R' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `multiple_mem_span_of_mem_localization_span`：multiple_mem_span_of_mem_loc
alization_span {N : Type*} [AddCommMonoid N] [Module R N] [Module R' N] [IsScala
rTower R R' N] [IsLocalization M…

--- 原说明 ---
If `S` is an `R' = M⁻¹R` algebra, and `x ∈ adjoin R' s`,
then `t • x ∈ adjoin R s` for some `t : M`.
-/
theorem multiple_mem_adjoin_of_mem_localization_adjoin [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] [IsLocalization M R'] (s : Set S) (x : S)
    (hx : x ∈ Algebra.adjoin R' s) : ∃ t : M, t • x ∈ Algebra.adjoin R s := by
  change ∃ t : M, t • x ∈ Subalgebra.toSubmodule (Algebra.adjoin R s)
  change x ∈ Subalgebra.toSubmodule (Algebra.adjoin R' s) at hx
  simp_rw [Algebra.adjoin_eq_span] at hx ⊢
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx

end

namespace Module.Finite

section

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {Rₚ : Type v} [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {Mₚ : Type t} [AddCommMonoid Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
variable (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Finite.of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：of_isLocalization (R S) {Rₚ Sₚ : Type*} [CommSemiring R] [CommSemiring S] 
[CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] 
[Algebra S Sₚ] [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M
 : Submonoid R) [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmono
id S M) Sₚ] [hRS : Module.Finite R S] : Module.Finite Rₚ Sₚ
参数：R S；M : Submonoid R；Algebra.algebraMapSubmonoid S M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `span_eq_top_localization_localization`：span_eq_top_localization_localiza
tion {v : Set A} (hv : span R v = ⊤) : span Rₛ (algebraMap A Aₛ '' v) = ⊤
-/
lemma of_isLocalization (R S) {Rₚ Sₚ : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R)
    [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ]
    [hRS : Module.Finite R S] :
    Module.Finite Rₚ Sₚ := by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
      (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is generated by `T` as an `R`-module,
  -- then `S'` is generated by `T` as an `R'`-module.
  obtain ⟨T, hT⟩ := hRS
  use T.image (algebraMap S Sₚ)
  simpa using span_eq_top_localization_localization Rₚ M Sₚ hT
/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [CommSemiring R] {P : Ideal R} [CommSemiring S] [Algebra R S]
    [Module.Finite R S] [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
  .of_isLocalization R S P.primeCompl

open Algebra nonZeroDivisors in
/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Module.Finite A C] :
    Module.Finite (FractionRing A) (Localization (algebraMapSubmonoid C A⁰)) :=
  .of_isLocalization A C A⁰

include S f in
/-
**Module.Finite.of_isLocalizedModule** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：of_isLocalizedModule [Module.Finite R M] : Module.Finite Rₚ Mₚ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `span_eq_top_of_isLocalizedModule`：span_eq_top_of_isLocalizedModule {v : 
Set M} (hv : span R v = ⊤) : span Rₛ (f '' v) = ⊤
-/
lemma of_isLocalizedModule [Module.Finite R M] : Module.Finite Rₚ Mₚ := by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  simpa using span_eq_top_of_isLocalizedModule Rₚ S f hT
/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite R M] : Module.Finite (Localization S) (LocalizedModule S M) :=
  of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

end

variable {R : Type u} [CommSemiring R] {M : Type w} [AddCommMonoid M] [Module R M]

/--
If there exists a finite set `{ r }` of `R` that generates the unit ideal and such that `Mᵣ` is
`Rᵣ`-finite for each `r`, then `M` is a finite `R`-module.

General version for any modules `Mᵣ` and rings `Rᵣ` satisfying the correct universal properties.
See `Module.Finite.of_localizationSpan_finite` for the specialized version.

See `of_localizationSpan'` for a version without the finite set assumption.
-/
/-
**Module.Finite.of_localizationSpan_finite'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Fi
nite`。
形式化陈述：of_localizationSpan_finite' (t : Finset R) (ht : Ideal.span (t : Set R) = 
⊤) {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid (Mₚ g)] [forall (
g : t), Module R (Mₚ g)] {Rₚ : forall (_ : t), Type*} [forall (g : t), CommSemir
ing (Rₚ g)] [forall (g : t), Algebra R (Rₚ g)] [forall (g : t), IsLocalization.A
way g.val (Rₚ g)] [forall (g : t), Module (Rₚ g) (Mₚ g)] [forall (g : t), IsScal
arTower R (Rₚ g) (Mₚ g)] (f : forall (g : t), M ->ₗ[R] Mₚ g) [forall (g : t), Is
LocalizedModule.Away g.val
参数：t : Finset R；ht : Ideal.span (t : Set R) = ⊤；_ : t；g : t；Mₚ g；g : t；Mₚ g；_ : 
t；g : t；Rₚ g；g : t；Rₚ g；g : t；Rₚ g；g : t；Rₚ g；Mₚ g；g : t；Rₚ g；Mₚ g；f : forall (g
 : t), M ->ₗ[R] Mₚ g；g : t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_attach_biUnion`：span_attach_biUnion [DecidableEq M] {α : 
Type*} (s : Finset α) (f : s -> Finset M) : span R (s.attach.biUnion f : Set M) 
= ⨆ x, span R (f x)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.mem_of_span_eq_top_of_smul_pow_mem`：mem_of_span_eq_top_of_smul
_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M) (H : f
orall r : s, exists n : Nat, ((r :…
· 使用定理 `multiple_mem_span_of_mem_localization_span`：multiple_mem_span_of_mem_loc
alization_span {N : Type*} [AddCommMonoid N] [Module R N] [Module R' N] [IsScala
rTower R R' N] [IsLocalization M…
· 使用定理 `IsLocalizedModule.smul_mem_finsetIntegerMultiple_span`：smul_mem_finsetIn
tegerMultiple_span [DecidableEq M] (x : M) (s : Finset M') (hx : f x in Submodul
e.span R s) : exists (m : S), m • x in Subm…
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If there exists a finite set `{ r }` of `R` that generates the unit ideal and su
ch that `Mᵣ` is
`Rᵣ`-finite for each `r`, then `M` is a finite `R`-module.

General version for any modules `Mᵣ` and rings `Rᵣ` satisfying the correct unive
rsal properties.
See `Module.Finite.of_localizationSpan_finite` for the specialized version.

See `of_localizationSpan'` for a version without the finite set assumption.
-/
theorem of_localizationSpan_finite' (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    {Mₚ : ∀ (_ : t), Type*} [∀ (g : t), AddCommMonoid (Mₚ g)] [∀ (g : t), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : t), Type*} [∀ (g : t), CommSemiring (Rₚ g)] [∀ (g : t), Algebra R (Rₚ g)]
    [∀ (g : t), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : t), Module (Rₚ g) (Mₚ g)] [∀ (g : t), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : t), M →ₗ[R] Mₚ g) [∀ (g : t), IsLocalizedModule.Away g.val (f g)]
    (H : ∀ (g : t), Module.Finite (Rₚ g) (Mₚ g)) :
    Module.Finite R M := by
  classical
  constructor
  choose s₁ s₂ using (fun g ↦ (H g).1)
  let sf := fun x : t ↦
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) (f x) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (t : Set R) ht _ (fun r ↦ ?_)
  set S : Submonoid R := Submonoid.powers r.val
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := multiple_mem_span_of_mem_localization_span S (Rₚ r)
    (s₁ r : Set (Mₚ r)) (IsLocalizedModule.mk' (f r) x (1 : S)) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def, ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_one] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalizedModule.smul_mem_finsetIntegerMultiple_span
    S (f r) _ (s₁ r) hn₁
  rw [Submonoid.smul_def] at hn₂
  use n₂ + n₁
  apply le_iSup (fun x : t ↦ Submodule.span R (sf x : Set M)) r
  rw [pow_add, mul_smul]
  exact hn₂

/--
If there exists a set `{ r }` of `R` that generates the unit ideal and such that `Mᵣ` is `Rᵣ`-finite
for each `r`, then `M` is a finite `R`-module.

General version for any modules `Mᵣ` and rings `Rᵣ` satisfying the correct universal properties.
See `Module.Finite.of_localizationSpan_finite` for the specialized version.
-/
/-
**Module.Finite.of_localizationSpan'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：of_localizationSpan' (t : Set R) (ht : Ideal.span t = ⊤) {Mₚ : forall (_ :
 t), Type*} [forall (g : t), AddCommMonoid (Mₚ g)] [forall (g : t), Module R (Mₚ
 g)] {Rₚ : forall (_ : t), Type*} [forall (g : t), CommSemiring (Rₚ g)] [forall 
(g : t), Algebra R (Rₚ g)] [h₁ : forall (g : t), IsLocalization.Away g.val (Rₚ g
)] [forall (g : t), Module (Rₚ g) (Mₚ g)] [forall (g : t), IsScalarTower R (Rₚ g
) (Mₚ g)] (f : forall (g : t), M ->ₗ[R] Mₚ g) [h₂ : forall (g : t), IsLocalizedM
odule.Away g.val (f g)] (H
参数：t : Set R；ht : Ideal.span t = ⊤；_ : t；g : t；Mₚ g；g : t；Mₚ g；_ : t；g : t；Rₚ g；
g : t；Rₚ g；g : t；Rₚ g；g : t；Rₚ g；Mₚ g；g : t；Rₚ g；Mₚ g；f : forall (g : t), M ->ₗ[
R] Mₚ g；g : t；f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Module.Finite.of_localizationSpan_finite'`：of_localizationSpan_finite' (
t : Finset R) (ht : Ideal.span (t : Set R) = ⊤) {Mₚ : forall (_ : t), Type*} [fo
rall (g : t), AddCommMonoid (Mₚ…

--- 原说明 ---
If there exists a set `{ r }` of `R` that generates the unit ideal and such that
 `Mᵣ` is `Rᵣ`-finite
for each `r`, then `M` is a finite `R`-module.

General version for any modules `Mᵣ` and rings `Rᵣ` satisfying the correct unive
rsal properties.
See `Module.Finite.of_localizationSpan_finite` for the specialized version.
-/
theorem of_localizationSpan' (t : Set R) (ht : Ideal.span t = ⊤)
    {Mₚ : ∀ (_ : t), Type*} [∀ (g : t), AddCommMonoid (Mₚ g)] [∀ (g : t), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : t), Type*} [∀ (g : t), CommSemiring (Rₚ g)] [∀ (g : t), Algebra R (Rₚ g)]
    [h₁ : ∀ (g : t), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : t), Module (Rₚ g) (Mₚ g)] [∀ (g : t), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : t), M →ₗ[R] Mₚ g) [h₂ : ∀ (g : t), IsLocalizedModule.Away g.val (f g)]
    (H : ∀ (g : t), Module.Finite (Rₚ g) (Mₚ g)) :
    Module.Finite R M := by
  rw [Ideal.span_eq_top_iff_finite] at ht
  obtain ⟨t', hc, ht'⟩ := ht
  have (g : t') : IsLocalization.Away g.val (Rₚ ⟨g.val, hc g.property⟩) :=
    h₁ ⟨g.val, hc g.property⟩
  have (g : t') : IsLocalizedModule.Away g.val
    ((fun g ↦ f ⟨g.val, hc g.property⟩) g) := h₂ ⟨g.val, hc g.property⟩
  apply of_localizationSpan_finite' t' ht' (fun g ↦ f ⟨g.val, hc g.property⟩)
    (fun g ↦ H ⟨g.val, hc g.property⟩)

/--
If there exists a finite set `{ r }` of `R` that generates the unit ideal and such that `Mᵣ` is
`Rᵣ`-finite for each `r`, then `M` is a finite `R`-module.

See `of_localizationSpan` for a version without the finite set assumption.
-/
/-
**Module.Finite.of_localizationSpan_finite** 是 Mathlib 中的一个定理，位于命名空间 `Module.Fin
ite`。
形式化陈述：of_localizationSpan_finite (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤
) (H : forall (g : t), Module.Finite (Localization.Away g.val) (LocalizedModule.
Away g.val M)) : Module.Finite R M
参数：t : Finset R；ht : Ideal.span (t : Set R) = ⊤；H : forall (g : t), Module.Finit
e (Localization.Away g.val) (LocalizedModule.Away g.val M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.of_localizationSpan_finite'`：of_localizationSpan_finite' (
t : Finset R) (ht : Ideal.span (t : Set R) = ⊤) {Mₚ : forall (_ : t), Type*} [fo
rall (g : t), AddCommMonoid (Mₚ…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…

--- 原说明 ---
If there exists a finite set `{ r }` of `R` that generates the unit ideal and su
ch that `Mᵣ` is
`Rᵣ`-finite for each `r`, then `M` is a finite `R`-module.

See `of_localizationSpan` for a version without the finite set assumption.
-/
theorem of_localizationSpan_finite (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (H : ∀ (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) :
    Module.Finite R M :=
  let f (g : t) : M →ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan_finite' t ht f H

/-- If there exists a set `{ r }` of `R` that generates the unit ideal and such that `Mᵣ` is
`Rᵣ`-finite for each `r`, then `M` is a finite `R`-module. -/
/-
**Module.Finite.of_localizationSpan** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤) (H : forall (g : t
), Module.Finite (Localization.Away g.val) (LocalizedModule.Away g.val M)) : Mod
ule.Finite R M
参数：t : Set R；ht : Ideal.span t = ⊤；H : forall (g : t), Module.Finite (Localizati
on.Away g.val) (LocalizedModule.Away g.val M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.of_localizationSpan'`：of_localizationSpan' (t : Set R) (ht
 : Ideal.span t = ⊤) {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid
 (Mₚ g)] [forall (g : t)…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…

--- 原说明 ---
If there exists a set `{ r }` of `R` that generates the unit ideal and such that
 `Mᵣ` is
`Rᵣ`-finite for each `r`, then `M` is a finite `R`-module.
-/
theorem of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) :
    Module.Finite R M :=
  let f (g : t) : M →ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan' t ht f H

end Finite

end Module

namespace Submodule

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Submodule R M}

/-
**Submodule.of_localizationSpan'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type v} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N : Submodule R M} (s : Set R),   Ideal.spa
n s = ⊤ →     ∀ {Mₚ : ↑s → Type u_1} [inst_3 : (g : ↑s) → AddCommMonoid (Mₚ g)] 
[inst_4 : (g : ↑s) → _root_.Module R (Mₚ g)]       {Rₚ : ↑s → Type u_2} [inst_5 
: (g : ↑s) → CommSemiring (Rₚ g)] [inst_6 : (g : ↑s) → Algebra R (Rₚ g)]       [
inst_7 : ∀ (g : ↑s), IsLocalization.Away (↑g) (Rₚ g)] [inst_8 : (g : ↑s) → _root
_.Module (Rₚ g) (Mₚ g)]       [inst_9 : ∀ (g : ↑s), IsScalarTower R (Rₚ g) (Mₚ g
)] (ϕ : (g : ↑s) → M →ₗ[R] Mₚ g)       [inst_10 : ∀ (g : ↑s), IsLocalizedModule 
(Submonoid.powers ↑g) (ϕ g)],       (∀ (g : ↑s), (Submodule.localized' (Rₚ g) (S
ubmonoid.powers ↑g) (ϕ g) N).FG) → N.FG
参数：s : Set R；g : ↑s；Mₚ g；g : ↑s；Mₚ g；g : ↑s；Rₚ g；g : ↑s；Rₚ g；g : ↑s；↑g；Rₚ g；g : 
↑s；Rₚ g；Mₚ g；g : ↑s；Rₚ g；Mₚ g；ϕ : (g : ↑s) → M →ₗ[R] Mₚ g；g : ↑s；Submonoid.power
s ↑g；ϕ g；∀ (g : ↑s), (Submodule.localized' (Rₚ g) (Submonoid.powers ↑g) (ϕ g) N)
.FG。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Module.Finite.of_localizationSpan'`：of_localizationSpan' (t : Set R) (ht
 : Ideal.span t = ⊤) {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid
 (Mₚ g)] [forall (g : t)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
-/
lemma of_localizationSpan' (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommMonoid (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommSemiring (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (H : ∀ (g : s), (N.localized' (Rₚ g) (Submonoid.powers g.1) (ϕ g)).FG) :
    N.FG := by
  simp [← Module.Finite.iff_fg, Module.Finite.of_localizationSpan' s hs
    (fun g ↦ N.toLocalized' (Rₚ g) (Submonoid.powers g.1) (ϕ g))
    (fun g ↦ Module.Finite.iff_fg.mpr (H g))]
/-
**Submodule.of_localizationSpan** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type v} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N : Submodule R M} (s : Set R),   Ideal.spa
n s = ⊤ → (∀ (g : ↑s), (Submodule.localized (Submonoid.powers ↑g) N).FG) → N.FG
参数：s : Set R；∀ (g : ↑s), (Submodule.localized (Submonoid.powers ↑g) N).FG。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.of_localizationSpan'`：∀ {R : Type u} [inst : CommSemiring R] {
M : Type v} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submo
dule R M} (s : Set R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
-/
lemma of_localizationSpan (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
    (H : ∀ (g : s), (localized (Submonoid.powers g.1) N).FG) : N.FG :=
  N.of_localizationSpan' s hs (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) H

variable (R' : Type*) [CommSemiring R'] [Algebra R R']
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
  (S : Submonoid R) [IsLocalization S R'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
/-
**Submodule.localized'_fg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type v} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N : Submodule R M} (R' : Type u_1) [inst_3 
: CommSemiring R'] [inst_4 : Algebra R R'] {M' : Type u_2}   [inst_5 : AddCommMo
noid M'] [inst_6 : _root_.Module R M'] [inst_7 : _root_.Module R' M']   [inst_8 
: IsScalarTower R R' M'] (S : Submonoid R) [inst_9 : IsLocalization S R'] (f : M
 →ₗ[R] M')   [inst_10 : IsLocalizedModule S f], N.FG → (Submodule.localized' R' 
S f N).FG
参数：R' : Type u_1；S : Submonoid R；f : M →ₗ[R] M'；Submodule.localized' R' S f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.localized'_span`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3
} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : A
ddCommMonoid M]…
-/
lemma localized'_fg (h : N.FG) : (N.localized' R' S f).FG := by
  rw [fg_def] at h ⊢
  rcases h with ⟨s, hfin, hspan⟩
  exact ⟨f '' s, hfin.image f, by rw [← hspan, localized'_span]⟩
/-
**Submodule.localized_fg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type v} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N : Submodule R M} (S : Submonoid R), N.FG 
→ (Submodule.localized S N).FG
参数：S : Submonoid R；Submodule.localized S N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.localized'_fg`：∀ {R : Type u} [inst : CommSemiring R] {M : Typ
e v} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R 
M} (R' : Type…
-/
lemma localized_fg (h : N.FG) : (N.localized S).FG := localized'_fg _ S _ h

end Submodule

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- If `I` is an ideal such that there exists a set `{ r }` of `R` that generates the unit ideal
and such that the image of `I` in `Rᵣ` is finitely generated for each `r`, then `I` is finitely
generated. -/
/-
**Ideal.fg_of_localizationSpan** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {I : Ideal R} (t : Set R),   Ideal.
span t = ⊤ → (∀ (g : ↑t), (Ideal.map (algebraMap R (Localization.Away ↑g)) I).FG
) → I.FG
参数：t : Set R；∀ (g : ↑t), (Ideal.map (algebraMap R (Localization.Away ↑g)) I).FG。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.of_localizationSpan'`：of_localizationSpan' (t : Set R) (ht
 : Ideal.span t = ⊤) {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid
 (Mₚ g)] [forall (g : t)…
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…

--- 原说明 ---
If `I` is an ideal such that there exists a set `{ r }` of `R` that generates th
e unit ideal
and such that the image of `I` in `Rᵣ` is finitely generated for each `r`, then 
`I` is finitely
generated.
-/
lemma fg_of_localizationSpan {I : Ideal R} (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ (g : t), (I.map (algebraMap R (Localization.Away g.val))).FG) : I.FG := by
  apply Module.Finite.iff_fg.mp
  let k (g : t) : I →ₗ[R] (I.map (algebraMap R (Localization.Away g.val))) :=
    Algebra.idealMap I (S := Localization.Away g.val)
  exact Module.Finite.of_localizationSpan' t ht k (fun g ↦ .of_fg (H g))

end Ideal

variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S] {f : R →+* S}

/--
To check that the kernel of a ring homomorphism is finitely generated,
it suffices to check this after localizing at a spanning set of the source.
-/
/-
**RingHom.ker_fg_of_localizationSpan** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：RingHom.ker_fg_of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤) (H 
: forall g : t, (RingHom.ker (Localization.awayMap f g.val)).FG) : (RingHom.ker 
f).FG
参数：t : Set R；ht : Ideal.span t = ⊤；H : forall g : t, (RingHom.ker (Localization.
awayMap f g.val)).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.fg_of_localizationSpan`：∀ {R : Type u} [inst : CommSemiring R] {I 
: Ideal R} (t : Set R),   Ideal.span t = ⊤ → (∀ (g : ↑t), (Ideal.map (algebraMap
 R (Localization.A…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalization.ker_map`：IsLocalization.ker_map (hT : Submonoid.map g M =
 T) : RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S ->+* Q)
 = (RingHom.…

--- 原说明 ---
To check that the kernel of a ring homomorphism is finitely generated,
it suffices to check this after localizing at a spanning set of the source.
-/
lemma RingHom.ker_fg_of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ g : t, (RingHom.ker (Localization.awayMap f g.val)).FG) :
    (RingHom.ker f).FG := by
  apply Ideal.fg_of_localizationSpan t ht
  intro g
  rw [← IsLocalization.ker_map (Localization.Away (f g.val)) f (Submonoid.map_powers f g.val)]
  exact H g
