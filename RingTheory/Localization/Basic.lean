/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Data.Finite.Prod
public import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Localizations of commutative rings

This file contains various basic results on localizations.

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

* `IsLocalization.algEquiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
  are isomorphic as `R`-algebras

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists Ideal

open Function

namespace Localization

open IsLocalization

variable {ι : Type*} {R : ι → Type*} [∀ i, CommSemiring (R i)]
variable {i : ι} (S : Submonoid (R i))

/-- `IsLocalization.map` applied to a projection homomorphism from a product ring. -/
/-
**Localization.mapPiEvalRingHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Localization`。
形式化陈述：mapPiEvalRingHom : Localization (S.comap <| Pi.evalRingHom R i) ->+* Local
ization S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalization.map` applied to a projection homomorphism from a product ring.
-/
noncomputable abbrev mapPiEvalRingHom :
    Localization (S.comap <| Pi.evalRingHom R i) →+* Localization S :=
  map (T := S) _ (Pi.evalRingHom R i) le_rfl

open Function in
/-
**Localization.mapPiEvalRingHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Localizatio
n`。
形式化陈述：mapPiEvalRingHom_bijective : Bijective (mapPiEvalRingHom S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submono
id R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 
: IsLoc…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
-/
theorem mapPiEvalRingHom_bijective : Bijective (mapPiEvalRingHom S) := by
  let T := S.comap (Pi.evalRingHom R i)
  classical
  refine ⟨fun x₁ x₂ eq ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨r₁, s₁, rfl⟩ := exists_mk'_eq T x₁
    obtain ⟨r₂, s₂, rfl⟩ := exists_mk'_eq T x₂
    simp_rw [map_mk'] at eq
    rw [IsLocalization.eq] at eq ⊢
    obtain ⟨s, hs⟩ := eq
    refine ⟨⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩, funext fun j ↦ ?_⟩
    obtain rfl | ne := eq_or_ne j i
    · simpa using hs
    · simp [update_of_ne ne]
  · obtain ⟨r, s, rfl⟩ := exists_mk'_eq S x
    exact ⟨mk' (M := T) _ (update 0 i r) ⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩,
      by simp [map_mk']⟩

end Localization

section CommSemiring

variable {R : Type*} [CommSemiring R] {M N : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

include M in
variable (R M) in
/-
**IsLocalization.finite** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (M : Submonoid R) {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLocalization M S] [Finite 
R], Finite S
参数：R : Type u_1；M : Submonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
-/
protected lemma finite [Finite R] : Finite S := by
  have : Function.Surjective (Function.uncurry (mk' (M := M) S)) := fun x ↦ by
    simpa using IsLocalization.exists_mk'_eq M x
  exact .of_surjective _ this

section CompatibleSMul

variable (N₁ N₂ : Type*) [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]

set_option backward.isDefEq.respectTransparency false in
variable (M S) in
include M in
/-
**IsLocalization.linearMap_compatibleSMul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：linearMap_compatibleSMul [Module S N₁] [Module S N₂] [IsScalarTower R S N₁
] [IsScalarTower R S N₂] : LinearMap.CompatibleSMul N₁ N₂ S R where map_smul f s
 s'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsUnit.smul_left_cancel`：smul_left_cancel {a : α} (ha : IsUnit a) {x y :
 β} : a • x = a • y ↔ x = y
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearMap_compatibleSMul [Module S N₁] [Module S N₂]
    [IsScalarTower R S N₁] [IsScalarTower R S N₂] :
    LinearMap.CompatibleSMul N₁ N₂ S R where
  map_smul f s s' := by
    obtain ⟨r, m, rfl⟩ := exists_mk'_eq M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module (Localization M) N₁] [Module (Localization M) N₂]
    [IsScalarTower R (Localization M) N₁] [IsScalarTower R (Localization M) N₂] :
    LinearMap.CompatibleSMul N₁ N₂ (Localization M) R :=
  linearMap_compatibleSMul M ..

end CompatibleSMul

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

variable (M) in
include M in
-- This is not an instance since the submonoid `M` would become a metavariable in typeclass search.
/-
**IsLocalization.algHom_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：algHom_subsingleton [Algebra R P] : Subsingleton (S ->ₐ[R] P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

section AlgEquiv

variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

section

variable (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps!]
/-
**IsLocalization.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：algEquiv : S ≃ₐ[R] Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`.
-/
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }

end

/-
**IsLocalization.algEquiv_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y
参数：x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.algEquiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_id_mk'`：map_id_mk' {Q : Type*} [CommSemiring Q] [Alge
bra R Q] [IsLocalization M Q] (x) (y : M) : map Q (RingHom.id R) (le_refl M) (mk
' S x y) = mk' …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y := by
  simp
/-
**IsLocalization.algEquiv_symm_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk
' S x y
参数：x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.algEquiv_symm_apply`：∀ {R : Type u_1} [inst : CommSemirin
g R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_id_mk'`：map_id_mk' {Q : Type*} [CommSemiring Q] [Alge
bra R Q] [IsLocalization M Q] (x) (y : M) : map Q (RingHom.id R) (le_refl M) (mk
' S x y) = mk' …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y := by simp

variable (M) in
include M in
/-
**IsLocalization.bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLocalization M S] {Q : Typ
e u_4} [inst_4 : CommSemiring Q] [inst_5 : Algebra R Q]   [IsLocalization M Q] (
f : S →+* Q), f.comp (algebraMap R S) = algebraMap R Q → Function.Bijective ⇑f
参数：M : Submonoid R；f : S →+* Q；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma bijective (f : S →+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q) :
    Function.Bijective f :=
  (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective

end AlgEquiv

section liftAlgHom

variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R}
  {S : Type*} [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
  {P : Type*} [CommSemiring P] [Algebra A P] [IsLocalization M S]
  {f : R →ₐ[A] P} (hf : ∀ y : M, IsUnit (f y)) (x : S)
include hf

/-- `AlgHom` version of `IsLocalization.lift`. -/
/-
**IsLocalization.liftAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：liftAlgHom : S ->ₐ[A] P where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom` version of `IsLocalization.lift`.
-/
noncomputable def liftAlgHom : S →ₐ[A] P where
  __ := lift hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]
/-
**IsLocalization.liftAlgHom_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`
。
形式化陈述：liftAlgHom_toRingHom : (liftAlgHom hf : S ->ₐ[A] P).toRingHom = lift hf
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlgHom_toRingHom : (liftAlgHom hf : S →ₐ[A] P).toRingHom = lift hf := rfl

@[simp]
/-
**IsLocalization.coe_liftAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coe_liftAlgHom : ⇑(liftAlgHom hf : S ->ₐ[A] P) = lift hf
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftAlgHom : ⇑(liftAlgHom hf : S →ₐ[A] P) = lift hf := rfl
/-
**IsLocalization.liftAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：liftAlgHom_apply : liftAlgHom hf x = lift hf x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlgHom_apply : liftAlgHom hf x = lift hf x := rfl

end liftAlgHom

section AlgEquivOfAlgEquiv

variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R} (S : Type*)
  [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [IsLocalization M S]
  {P : Type*} [CommSemiring P] [Algebra A P] {T : Submonoid P} (Q : Type*)
  [CommSemiring Q] [Algebra A Q] [Algebra P Q] [IsScalarTower A P Q] [IsLocalization T Q]
  (h : R ≃ₐ[A] P) (H : Submonoid.map h M = T)

include H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M`, `T` respectively,
an isomorphism `h : R ≃ₐ[A] P` such that `h(M) = T` induces an isomorphism of localizations
`S ≃ₐ[A] Q`. -/
@[simps!]
/-
**IsLocalization.algEquivOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：algEquivOfAlgEquiv : S ≃ₐ[A] Q where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S`, `Q` are localizations of `R` and `P` at submonoids `M`, `T` respectively
,
an isomorphism `h : R ≃ₐ[A] P` such that `h(M) = T` induces an isomorphism of lo
calizations
`S ≃ₐ[A] Q`.
-/
noncomputable def algEquivOfAlgEquiv : S ≃ₐ[A] Q where
  __ := ringEquivOfRingEquiv S Q h.toRingEquiv H
  commutes' _ := by dsimp; rw [IsScalarTower.algebraMap_apply A R S, map_eq,
    RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]

variable {S Q h}
/-
**IsLocalization.algEquivOfAlgEquiv_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion`。
形式化陈述：algEquivOfAlgEquiv_eq_map : (algEquivOfAlgEquiv S Q h H : S ->+* Q) = map 
Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem algEquivOfAlgEquiv_eq_map :
    (algEquivOfAlgEquiv S Q h H : S →+* Q) =
      map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalization.algEquivOfAlgEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：algEquivOfAlgEquiv_eq (x : R) : algEquivOfAlgEquiv S Q h H ((algebraMap R 
S) x) = algebraMap P Q (h x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.algEquivOfAlgEquiv_apply`：∀ {A : Type u_4} [inst : CommSe
miring A] {R : Type u_5} [inst_1 : CommSemiring R] [inst_2 : Algebra A R]   {M :
 Submonoid R} (S : Type u_6) …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivOfAlgEquiv_eq (x : R) :
    algEquivOfAlgEquiv S Q h H ((algebraMap R S) x) = algebraMap P Q (h x) := by
  simp

set_option backward.isDefEq.respectTransparency false in
set_option linter.docPrime false in
/-
**IsLocalization.algEquivOfAlgEquiv_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizatio
n`。
形式化陈述：algEquivOfAlgEquiv_mk' (x : R) (y : M) : algEquivOfAlgEquiv S Q h H (mk' S
 x y) = mk' Q (h x) ⟨h y, show h y in T from H ▸ Set.mem_image_of_mem h y.2⟩
参数：x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.algEquivOfAlgEquiv_apply`：∀ {A : Type u_4} [inst : CommSe
miring A] {R : Type u_5} [inst_1 : CommSemiring R] [inst_2 : Algebra A R]   {M :
 Submonoid R} (S : Type u_6) …
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivOfAlgEquiv_mk' (x : R) (y : M) :
    algEquivOfAlgEquiv S Q h H (mk' S x y) =
      mk' Q (h x) ⟨h y, show h y ∈ T from H ▸ Set.mem_image_of_mem h y.2⟩ := by
  simp [map_mk']
/-
**IsLocalization.algEquivOfAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：algEquivOfAlgEquiv_symm : (algEquivOfAlgEquiv S Q h H).symm = algEquivOfAl
gEquiv Q S h.symm (show Submonoid.map h.symm T = M by rw [← H]; rw [← Submonoid.
map_coe_toMulEquiv]; rw [AlgEquiv.symm_toMulEquiv]; rw [← Submonoid.comap_equiv_
eq_map_symm]; rw [← Submonoid.map_coe_toMulEquiv]; rw [Submonoid.comap_map_eq_of
_injective (h : R ≃* P).injective])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem algEquivOfAlgEquiv_symm : (algEquivOfAlgEquiv S Q h H).symm =
    algEquivOfAlgEquiv Q S h.symm (show Submonoid.map h.symm T = M by
      rw [← H, ← Submonoid.map_coe_toMulEquiv, AlgEquiv.symm_toMulEquiv,
        ← Submonoid.comap_equiv_eq_map_symm, ← Submonoid.map_coe_toMulEquiv,
        Submonoid.comap_map_eq_of_injective (h : R ≃* P).injective]) := rfl

end AlgEquivOfAlgEquiv

section smul

variable {R : Type*} [CommSemiring R] {S : Submonoid R}
variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
variable {M' : Type*} [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

/-- If `x` in a `R' = S⁻¹ R`-module `M'`, then for a submodule `N'` of `M'`,
`s • x ∈ N'` if and only if `x ∈ N'` for some `s` in S. -/
/-
**IsLocalization.smul_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization`。
形式化陈述：smul_mem_iff {N' : Submodule R' M'} {x : M'} {s : S} : s • x in N' ↔ x in 
N'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.smul_mem_iff_of_isUnit`：smul_mem_iff_of_isUnit (hr : IsUnit r)
 : r • x in p ↔ x in p
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Submodule.smul_of_tower_mem`：smul_of_tower_mem [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (h : x in p) : r • x in p

--- 原说明 ---
If `x` in a `R' = S⁻¹ R`-module `M'`, then for a submodule `N'` of `M'`,
`s • x ∈ N'` if and only if `x ∈ N'` for some `s` in S.
-/
lemma smul_mem_iff {N' : Submodule R' M'} {x : M'} {s : S} :
    s • x ∈ N' ↔ x ∈ N' := by
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.smul_of_tower_mem N' s h⟩
  rwa [← Submodule.smul_mem_iff_of_isUnit (r := algebraMap R R' s) N' (map_units R' s),
    algebraMap_smul]

end smul

section Units

/-
**IsLocalization.of_le_isUnit_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `IsLocaliza
tion`。
形式化陈述：of_le_isUnit_of_bijective {M : Submonoid R} (hM : Algebra.algebraMapSubmon
oid S M <= IsUnit.submonoid S) (h : Function.Bijective (algebraMap R S)) : IsLoc
alization M S where map_units y
参数：hM : Algebra.algebraMapSubmonoid S M <= IsUnit.submonoid S；h : Function.Bijec
tive (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma of_le_isUnit_of_bijective {M : Submonoid R}
    (hM : Algebra.algebraMapSubmonoid S M ≤ IsUnit.submonoid S)
    (h : Function.Bijective (algebraMap R S)) :
    IsLocalization M S where
  map_units y := hM ⟨_, y.prop, rfl⟩
  surj y := by
    obtain ⟨x, rfl⟩ := h.surjective y
    use ⟨x, 1⟩
    simp
  exists_of_eq {x y} hxy := ⟨1, by simp [h.injective hxy]⟩
/-
**IsLocalization.of_le_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization`。
形式化陈述：of_le_isUnit {S : Submonoid R} (hS : S <= IsUnit.submonoid R) : IsLocaliza
tion S R
参数：hS : S <= IsUnit.submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.of_le_isUnit_of_bijective`：of_le_isUnit_of_bijective {M :
 Submonoid R} (hM : Algebra.algebraMapSubmonoid S M <= IsUnit.submonoid S) (h : 
Function.Bijective (algebraMap…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMapSubmonoid_self`：algebraMapSubmonoid_self (M : Submonoi
d R) : Algebra.algebraMapSubmonoid R M = M
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma of_le_isUnit {S : Submonoid R} (hS : S ≤ IsUnit.submonoid R) : IsLocalization S R :=
  of_le_isUnit_of_bijective (by simpa) Function.bijective_id

@[deprecated (since := "2026-04-15")]
alias at_units := of_le_isUnit
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (IsUnit.submonoid R) R := of_le_isUnit le_rfl
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (Algebra.algebraMapSubmonoid S (IsUnit.submonoid R)) S :=
  IsLocalization.of_le_isUnit Algebra.algebraMapSubmonoid_isUnit_le

variable (R M)

set_option backward.isDefEq.respectTransparency false in
/-- The localization at a module of units is isomorphic to the ring. -/
/-
**IsLocalization.atUnits** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：atUnits (H : M <= IsUnit.submonoid R) : R ≃ₐ[R] S
参数：H : M <= IsUnit.submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization at a module of units is isomorphic to the ring.
-/
noncomputable def atUnits (H : M ≤ IsUnit.submonoid R) : R ≃ₐ[R] S := by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [map_mul, ← eq, ← hu, mul_assoc, ← map_mul]
    simp

end Units

end IsLocalization

section

variable (M N)

/-
**isLocalization_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor; constructor
  · intro y
    convert! (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S → P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff, ← IsLocalization.eq_iff_exists M S, ← h.symm.commutes, ←
      h.symm.commutes]
    exact id

variable {M} in
/-
**self** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem self (H : M ≤ IsUnit.submonoid R) : IsLocalization M R :=
  isLocalization_of_algEquiv _ (atUnits _ _ (S := Localization M) H).symm
/-
**isLocalization_iff_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩
/-
**isLocalization_iff_of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔
      haveI := (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }

variable (S) in
/-- If an algebra is simultaneously localizations for two submonoids, then an arbitrary algebra
is a localization of one submonoid iff it is a localization of the other. -/
/-
**isLocalization_iff_of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an algebra is simultaneously localizations for two submonoids, then an arbitr
ary algebra
is a localization of one submonoid iff it is a localization of the other.
-/
theorem isLocalization_iff_of_isLocalization [IsLocalization M S] [IsLocalization N S]
    [Algebra R P] : IsLocalization M P ↔ IsLocalization N P :=
  ⟨fun _ ↦ isLocalization_of_algEquiv N (algEquiv M S P),
    fun _ ↦ isLocalization_of_algEquiv M (algEquiv N S P)⟩
/-
**iff_of_le_of_exists_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iff_of_le_of_exists_dvd (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ n ∈ N, ∃ m ∈ M, n ∣ m) :
    IsLocalization M S ↔ IsLocalization N S :=
  have : IsLocalization N (Localization M) := of_le_of_exists_dvd _ _ h₁ h₂
  isLocalization_iff_of_isLocalization _ _ (Localization M)

end

variable (M)

/-- If `S₁` is the localization of `R` at `M₁` and `S₂` is the localization of
`R` at `M₂`, then every localization `T` of `S₂` at `M₁` is also a localization of
`S₁` at `M₂`, in other words `M₁⁻¹M₂⁻¹R` can be identified with `M₂⁻¹M₁⁻¹R`. -/
/-
**commutes** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S₁` is the localization of `R` at `M₁` and `S₂` is the localization of
`R` at `M₂`, then every localization `T` of `S₂` at `M₁` is also a localization 
of
`S₁` at `M₂`, in other words `M₁⁻¹M₂⁻¹R` can be identified with `M₂⁻¹M₁⁻¹R`.
-/
lemma commutes (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (M₁ M₂ : Submonoid R)
    [IsLocalization M₁ S₁] [IsLocalization M₂ S₂]
    [IsLocalization (Algebra.algebraMapSubmonoid S₂ M₁) T] :
    IsLocalization (Algebra.algebraMapSubmonoid S₁ M₂) T where
  map_units := by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨a, ha⟩)
  surj a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units _ ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T, ← hz, map_mul, ← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc, hr, mul_assoc, hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul, ← map_mul, mul_assoc, mul_comm _ c, ha, map_mul, map_mul]
    ring

variable (Rₘ Sₙ Rₘ' Sₙ' : Type*) [CommSemiring Rₘ] [CommSemiring Sₙ] [CommSemiring Rₘ']
  [CommSemiring Sₙ'] [Algebra R Rₘ] [Algebra S Sₙ] [Algebra R Rₘ'] [Algebra S Sₙ'] [Algebra R Sₙ]
  [Algebra Rₘ Sₙ] [Algebra Rₘ' Sₙ'] [Algebra R Sₙ'] (N : Submonoid S) [IsLocalization M Rₘ]
  [IsLocalization N Sₙ] [IsLocalization M Rₘ'] [IsLocalization N Sₙ'] [IsScalarTower R Rₘ Sₙ]
  [IsScalarTower R S Sₙ] [IsScalarTower R Rₘ' Sₙ'] [IsScalarTower R S Sₙ']
/-
**algEquiv_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquiv_comp_algebraMap : (algEquiv N Sₙ Sₙ' : _ →+* Sₙ').comp (algebraMap Rₘ Sₙ) =
      (algebraMap Rₘ' Sₙ').comp (algEquiv M Rₘ Rₘ') := by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    ← AlgEquiv.restrictScalars_apply R, AlgEquiv.commutes]

variable {Rₘ} in
/-
**algEquiv_comp_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquiv_comp_algebraMap_apply (x : Rₘ) :
    (algEquiv N Sₙ Sₙ' : _ →+* Sₙ').comp (algebraMap Rₘ Sₙ) x =
    (algebraMap Rₘ' Sₙ').comp (algEquiv M Rₘ Rₘ') x := by
  rw [algEquiv_comp_algebraMap M Rₘ Sₙ Rₘ']


end IsLocalization

namespace Localization

open IsLocalization

/-
**Localization.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_natCast (m : Nat) : (mk m 1 : Localization M) = m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Localization.mk_algebraMap`：mk_algebraMap {A : Type*} [CommSemiring A] [
Algebra A R] (m : A) : mk (algebraMap A R m) 1 = algebraMap A (Localization M) m
-/
theorem mk_natCast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℕ) _

variable [IsLocalization M S]

section

variable (S) (M)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps!]
/-
**Localization.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：algEquiv : Localization M ≃ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization of `R` at `M` as a quotient type is isomorphic to any other loc
alization.
-/
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _

/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
@[instance_reducible]
/-
**Localization._root_.IsLocalization.unique** 是 Mathlib 中的一个定义，位于命名空间 `Localizat
ion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization of a singleton is a singleton. Cannot be an instance due to met
avariables.
-/
noncomputable def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique

end

nonrec theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _

nonrec theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _

/-
**Localization.algEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `Localization.algEquiv_mk'`：∀ {R : Type u_1} [inst : CommSemiring R] {M :
 Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] 
[inst_3 : IsLoc…
-/
theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', algEquiv_mk']
/-
**Localization.algEquiv_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x 
y
参数：x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `Localization.algEquiv_symm_mk'`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra 
R S] [inst_3 : IsLoc…
-/
theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk', algEquiv_symm_mk']
/-
**Localization.coe_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Localization`。
形式化陈述：coe_algEquiv : (Localization.algEquiv M S : Localization M ->+* S) = IsLoc
alization.map (M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma coe_algEquiv :
    (Localization.algEquiv M S : Localization M →+* S) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl
/-
**Localization.coe_algEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `Localization`。
形式化陈述：coe_algEquiv_symm : ((Localization.algEquiv M S).symm : S ->+* Localizatio
n M) = IsLocalization.map (M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma coe_algEquiv_symm :
    ((Localization.algEquiv M S).symm : S →+* Localization M) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

end Localization

open IsLocalization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
/-
**IsField.localization_map_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing R
ₘ] {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocal
ization M Rₘ] : Function.Bijective (algebraMap R Rₘ)
参数：hM : (0 : R) ∉ M；hR : IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nonZeroDivisors_of_noZeroDivisors`：le_nonZeroDivisors_of_noZeroDiviso
rs {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) : S <= M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If `R` is a field, then localizing at a submonoid not containing `0` adds no new
 elements.
-/
theorem IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) := by
  let := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
/-
**Field.localization_map_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M
 : Submonoid K} (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] : Functi
on.Bijective (algebraMap K Kₘ)
参数：hM : (0 : K) ∉ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.localization_map_bijective`：IsField.localization_map_bijective {
R Rₘ : Type*} [CommRing R] [CommRing Rₘ] {M : Submonoid R} (hM : (0 : R) ∉ M) (h
R : IsField R) [Algebra …
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R

--- 原说明 ---
If `R` is a field, then localizing at a submonoid not containing `0` adds no new
 elements.
-/
theorem Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM

-- this looks weird due to the `letI` inside the above lemma, but trying to do it the other
-- way round causes issues with defeq of instances, so this is actually easier.
section Algebra

variable {Rₘ Sₘ : Type*} [CommSemiring Rₘ] [CommSemiring Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
include S
section

variable (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebraMap R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraMapSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
@[instance_reducible]
/-
**localizationAlgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：localizationAlgebra : Algebra Rₘ Sₘ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M
`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebraMap R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire sq
uare commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps
.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraM
apSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ 
Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra (Localization M)
    (Localization (Algebra.algebraMapSubmonoid S M)) := localizationAlgebra M S

-- This is not an instance, because the discrimination tree key is `IsScalarTower _ _ _ _ _ _`, so
-- it would cause significant slowdowns.
/-
**isScalarTower_localizationAlgebra** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isScalarTower_localizationAlgebra [Algebra R Sₘ] [IsScalarTower R S Sₘ] : 
letI : Algebra Rₘ Sₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isScalarTower_localizationAlgebra [Algebra R Sₘ] [IsScalarTower R S Sₘ] :
    letI : Algebra Rₘ Sₘ := localizationAlgebra M S
    IsScalarTower R Rₘ Sₘ :=
  letI : Algebra Rₘ Sₘ := localizationAlgebra M S
  .of_algebraMap_eq' <| by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R S Sₘ]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R (Localization M) (Localization (Algebra.algebraMapSubmonoid S M)) :=
  isScalarTower_localizationAlgebra _ _

end

section

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable (S Rₘ Sₘ)

/-
**IsLocalization.map_units_map_submonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y
)
参数：y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
-/
theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) := by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩

-- can't be simp, as `S` only appears on the RHS
/-
**IsLocalization.algebraMap_mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.algebraMap_mk' (x : R) (y : M) : algebraMap Rₘ Sₘ (IsLocali
zation.mk' Rₘ x y) = IsLocalization.mk' Sₘ (algebraMap R S x) ⟨algebraMap R S y,
 Algebra.mem_algebraMapSubmonoid_of_mem y⟩
参数：x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.mul_mk'_eq_mk'_of_mul`：∀ {R : Type u_1} [inst : CommSemir
ing R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Al
gebra R S] [inst_3 : IsLoc…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsLocalization.mk'_mul_cancel_left`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
-/
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, ←
    IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ Sₘ,
    IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← map_mul, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)

variable (M)

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
/-
**IsLocalization.algebraMap_eq_map_map_submonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.algebraMap_eq_map_map_submonoid : algebraMap Rₘ Sₘ = map Sₘ
 (algebraMap R S) (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le
_comap_map)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.map_unique`：map_unique (j : S ->+* Q) (hj : forall x : R,
 j (algebraMap R S x) = algebraMap P Q (g x)) : map Q g hy = j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)

--- 原说明 ---
If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  Eq.symm <|
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ, ← IsScalarTower.algebraMap_apply R Rₘ Sₘ]

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
/-
**IsLocalization.algebraMap_apply_eq_map_map_submonoid** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) : algebraMap Rₘ S
ₘ x = map Sₘ (algebraMap R S) (show _ <= (Algebra.algebraMapSubmonoid S M).comap
 _ from M.le_comap_map) x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.algebraMap_eq_map_map_submonoid`：IsLocalization.algebraMa
p_eq_map_map_submonoid : algebraMap Rₘ Sₘ = map Sₘ (algebraMap R S) (show _ <= (
Algebra.algebraMapSubmonoid S M).com…

--- 原说明 ---
If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x
/-
**IsLocalization.lift_algebraMap_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.lift_algebraMap_eq_algebraMap : IsLocalization.lift (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.lift_unique`：lift_unique {j : S ->+* P} (hj : forall x, j
 ((algebraMap R S) x) = g x) : lift hg = j
· 使用定理 `IsLocalization.map_units_map_submonoid`：IsLocalization.map_units_map_sub
monoid (y : M) : IsUnit (algebraMap R Sₘ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
-/
theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    IsLocalization.lift (M := M) (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm

end

variable (Rₘ Sₘ)

/-
**localizationAlgebraMap_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：localizationAlgebraMap_def : @algebraMap Rₘ Sₘ _ _ (localizationAlgebra M 
S) = map Sₘ (algebraMap R S) (show _ <= (Algebra.algebraMapSubmonoid S M).comap 
_ from M.le_comap_map)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localizationAlgebraMap_def :
    @algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S) =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  rfl

/-- Injectivity of the underlying `algebraMap` descends to the algebra induced by localization. -/
/-
**localizationAlgebra_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) 
: Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S))
参数：hRS : Function.Injective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_injective_of_injective`：map_injective_of_injective (h
 : Function.Injective g) [IsLocalization (M.map g) Q] : Function.Injective (map 
Q g M.le_comap_map : S -> Q)

--- 原说明 ---
Injectivity of the underlying `algebraMap` descends to the algebra induced by lo
calization.
-/
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (Algebra.algebraMapSubmonoid R M) Rₘ := by
  simpa

end Algebra

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]

namespace IsLocalization

variable (M) in
/--
Another version of `IsLocalization.map_injective_of_injective` that is more general for the choice
of the localization submonoid but requires it does not contain zero.
-/
/-
**IsLocalization.map_injective_of_injective'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation`。
形式化陈述：map_injective_of_injective' {f : R ->+* S} {Rₘ : Type*} [CommRing Rₘ] [Alg
ebra R Rₘ] [IsLocalization M Rₘ] (Sₘ : Type*) {N : Submonoid S} [CommRing Sₘ] [A
lgebra S Sₘ] [IsLocalization N Sₘ] (hf : M <= Submonoid.comap f N) (hN : 0 ∉ N) 
[IsDomain S] (hf' : Function.Injective f) : Function.Injective (map Sₘ f hf : Rₘ
 ->+* Sₘ)
参数：Sₘ : Type*；hf : M <= Submonoid.comap f N；hN : 0 ∉ N；hf' : Function.Injective 
f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Another version of `IsLocalization.map_injective_of_injective` that is more gene
ral for the choice
of the localization submonoid but requires it does not contain zero.
-/
theorem map_injective_of_injective' {f : R →+* S} {Rₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] (Sₘ : Type*) {N : Submonoid S} [CommRing Sₘ] [Algebra S Sₘ]
    [IsLocalization N Sₘ] (hf : M ≤ Submonoid.comap f N) (hN : 0 ∉ N) [IsDomain S]
    (hf' : Function.Injective f) :
    Function.Injective (map Sₘ f hf : Rₘ →+* Sₘ) := by
  refine (injective_iff_map_eq_zero (map Sₘ f hf)).mpr fun x h ↦ ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  aesop (add simp [map_mk', mk'_eq_zero_iff])

end IsLocalization

/-
**Localization.mk_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Localization.mk_intCast (m : Int) : (mk m 1 : Localization M) = m
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Localization.mk_algebraMap`：mk_algebraMap {A : Type*} [CommSemiring A] [
Algebra A R] (m : A) : mk (algebraMap A R m) 1 = algebraMap A (Localization M) m
-/
theorem Localization.mk_intCast (m : ℤ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℤ) _
/-
**Localization.r_iff_of_le_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Localization.r_iff_of_le_nonZeroDivisors (hM : M <= nonZeroDivisors R) (a 
c : R) (b d : M) : Localization.r _ (a, b) (c, d) ↔ a * d = b * c
参数：hM : M <= nonZeroDivisors R；a c : R；b d : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Setoid.mk.congr_simp`：∀ {α : Sort u} (r r_1 : α → α → Prop) (e_r : r = r
_1) (iseqv : Equivalence r),   { r := r, iseqv := iseqv } = { r := r_1, iseqv :=
 ⋯ }
· 使用定理 `Localization.r_eq_r'`：r_eq_r' : r S = r' S
· 使用定理 `Con.mk.congr_simp`：∀ {M : Type u_1} [inst : Mul M] (toSetoid toSetoid_1 
: Setoid M) (e_toSetoid : toSetoid = toSetoid_1)   (mul' : ∀ {w x y z : M}, toSe
toid w …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Localization.r_iff_of_le_nonZeroDivisors (hM : M ≤ nonZeroDivisors R) (a c : R) (b d : M) :
    Localization.r _ (a, b) (c, d) ↔ a * d = b * c := by
  simp only [Localization.r_eq_r', Localization.r', Subtype.exists, exists_prop, Con.rel_mk]
  refine ⟨fun ⟨u, hu, h⟩ ↦ ?_,
    fun h ↦ ⟨1, Submonoid.one_mem M, by simpa only [one_mul, mul_comm a] using h⟩⟩
  have hu' : u ∈ nonZeroDivisors R := hM hu
  simp only [mem_nonZeroDivisors_iff, mul_comm, and_self] at hu'
  rw [← sub_eq_zero]
  apply hu'
  rwa [mul_sub, sub_eq_zero, mul_comm a]

end CommRing

section Algebra

-- This is not tagged with `@[ext]` because `A` and `W` cannot be inferred.
/-
**IsLocalization.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.algHom_ext {R A L B : Type*} [CommSemiring R] [CommSemiring
 A] [CommSemiring L] [Semiring B] (W : Submonoid A) [Algebra A L] [IsLocalizatio
n W L] [Algebra R A] [Algebra R L] [IsScalarTower R A L] [Algebra R B] {f g : L 
->ₐ[R] B} (h : f.comp (Algebra.algHom R A L) = g.comp (Algebra.algHom R A L)) : 
f = g
参数：W : Submonoid A；h : f.comp (Algebra.algHom R A L) = g.comp (Algebra.algHom R 
A L)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHom.ext_iff`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [i
nst_…
-/
theorem IsLocalization.algHom_ext {R A L B : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring L] [Semiring B]
    (W : Submonoid A) [Algebra A L] [IsLocalization W L]
    [Algebra R A] [Algebra R L] [IsScalarTower R A L] [Algebra R B]
    {f g : L →ₐ[R] B} (h : f.comp (Algebra.algHom R A L) = g.comp (Algebra.algHom R A L)) :
    f = g :=
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext W <| RingHom.ext <| AlgHom.ext_iff.mp h

-- This is a more specific case where the domain is `Localization W`, so this is tagged
-- `@[ext high]` so that it will be automatically applied before the default extensionality lemmas
-- which compare every element.
/-
**Localization.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : CommSemiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : 
Algebra R B] (W : Submonoid A) {f g : Localization W →ₐ[R] B},   f.comp (Algebra
.algHom R A (Localization W)) = g.comp (Algebra.algHom R A (Localization W)) → f
 = g
参数：W : Submonoid A；Algebra.algHom R A (Localization W)；Algebra.algHom R A (Local
ization W)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.algHom_ext`：IsLocalization.algHom_ext {R A L B : Type*} [
CommSemiring R] [CommSemiring A] [CommSemiring L] [Semiring B] (W : Submonoid A)
 [Algebra A L] …
-/
@[ext high] theorem Localization.algHom_ext {R A B : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (W : Submonoid A)
    {f g : Localization W →ₐ[R] B}
    (h : f.comp (Algebra.algHom R A _) = g.comp (Algebra.algHom R A _)) :
    f = g :=
  IsLocalization.algHom_ext W h

section extend

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  (S : Type*) [CommSemiring S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- For an algebra homomorphism `f : A →ₐ[R] B`, if `A` and `B` are algebras over a localization
`S` of `R`, then `f` is automatically an `S`-algebra homomorphism. -/
/-
**AlgHom.extendScalarsOfIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.extendScalarsOfIsLocalization (f : A ->ₐ[R] B) : A ->ₐ[S] B where _
_
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an algebra homomorphism `f : A →ₐ[R] B`, if `A` and `B` are algebras over a 
localization
`S` of `R`, then `f` is automatically an `S`-algebra homomorphism.
-/
def AlgHom.extendScalarsOfIsLocalization (f : A →ₐ[R] B) : A →ₐ[S] B where
  __ := f
  commutes' := by
    let f := f.comp (IsScalarTower.toAlgHom R S A)
    let g := IsScalarTower.toAlgHom R S B
    have : f.toRingHom.comp (algebraMap R S) = g.toRingHom.comp (algebraMap R S) := by simp
    suffices f = g by rwa [DFunLike.ext_iff] at this
    apply IsLocalization.algHom_ext M
    rwa [DFunLike.ext_iff] at this ⊢

@[simp]
/-
**AlgHom.extendScalarsOfIsLocalization_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.extendScalarsOfIsLocalization_apply (f : A ->ₐ[R] B) (a : A) : f.ex
tendScalarsOfIsLocalization S M a = f a
参数：f : A ->ₐ[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AlgHom.extendScalarsOfIsLocalization_apply (f : A →ₐ[R] B) (a : A) :
    f.extendScalarsOfIsLocalization S M a = f a :=
  rfl

/-- For an algebra isomorphism `f : A ≃ₐ[R] B`, if `A` and `B` are algebras over a localization
`S` of `R`, then `f` is automatically an `S`-algebra isomorphism. -/
@[simps]
/-
**AlgEquiv.extendScalarsOfIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.extendScalarsOfIsLocalization (f : A ≃ₐ[R] B) : A ≃ₐ[S] B where _
_
参数：f : A ≃ₐ[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
For an algebra isomorphism `f : A ≃ₐ[R] B`, if `A` and `B` are algebras over a l
ocalization
`S` of `R`, then `f` is automatically an `S`-algebra isomorphism.
-/
def AlgEquiv.extendScalarsOfIsLocalization (f : A ≃ₐ[R] B) : A ≃ₐ[S] B where
  __ := f.toAlgHom.extendScalarsOfIsLocalization S M
  __ := f

end extend

end Algebra

