/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!

# The meta properties of finite ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finite_localizationPreserves` : If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a
  finite `R' = M⁻¹R`-algebra.
* `finite_ofLocalizationSpan` : `S` is a finite `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite `Rᵣ`-algebra.

-/

public section


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

/-
**RingHom.finite_stableUnderComposition** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finite_stableUnderComposition : StableUnderComposition @Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) 
(hf : f.Finite) : (g.comp f).Finite
-/
theorem finite_stableUnderComposition : StableUnderComposition @Finite := by
  introv R hf hg
  exact hg.comp hf
/-
**RingHom.finite_respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finite_respectsIso : RespectsIso @Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用定理 `RingHom.finite_stableUnderComposition`：finite_stableUnderComposition : S
tableUnderComposition @Finite
· 使用定理 `RingHom.Finite.of_surjective`：of_surjective (f : A ->+* B) (hf : Surject
ive f) : f.Finite
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem finite_respectsIso : RespectsIso @Finite := by
  apply finite_stableUnderComposition.respectsIso
  intros
  exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective
/-
**RingHom.finite_containsIdentities** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：finite_containsIdentities : ContainsIdentities @Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.id`：id : Finite (RingHom.id A)
-/
lemma finite_containsIdentities : ContainsIdentities @Finite := Finite.id
/-
**RingHom.finite_isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finite_isStableUnderBaseChange : IsStableUnderBaseChange @Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.finite_respectsIso`：finite_respectsIso : RespectsIso @Finite
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem finite_isStableUnderBaseChange : IsStableUnderBaseChange @Finite := by
  refine IsStableUnderBaseChange.mk finite_respectsIso ?_
  simp only [finite_algebraMap]
  intros
  infer_instance

end RingHom

open scoped Pointwise

universe u

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

/-- If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a finite `R' = M⁻¹R`-algebra. -/
/-
**RingHom.finite_localizationPreserves** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.finite_localizationPreserves : RingHom.LocalizationPreserves @Ring
Hom.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMapSubmonoid.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Type u_4) [inst_1 : Semiring S] [inst_2 : Algebra R S] (M : Submonoid R)
,   Algebra.algebraMap…
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […

--- 原说明 ---
If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a finite `R' = M⁻¹R`-algebra
.
-/
theorem RingHom.finite_localizationPreserves : RingHom.LocalizationPreserves @RingHom.Finite := by
  introv R hf
  let := f.toAlgebra
  let := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  let := f'.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map).symm
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) S' := by
    rwa [Algebra.algebraMapSubmonoid, RingHom.algebraMap_toAlgebra]
  have : Module.Finite R S := hf
  exact .of_isLocalization R S M
/-
**RingHom.localization_away_map_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.localization_away_map_finite (R S R' S' : Type u) [CommRing R] [Co
mmRing S] [CommRing R'] [CommRing S'] [Algebra R R'] (f : R ->+* S) [Algebra S S
'] (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] (hf : f.Fin
ite) : (IsLocalization.Away.map R' S' f r).Finite
参数：R S R' S' : Type u；f : R ->+* S；r : R；f r；hf : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用定理 `RingHom.finite_localizationPreserves`：RingHom.finite_localizationPreserv
es : RingHom.LocalizationPreserves @RingHom.Finite
-/
theorem RingHom.localization_away_map_finite (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R R'] (f : R →+* S) [Algebra S S']
    (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.Finite) : (IsLocalization.Away.map R' S' f r).Finite :=
  finite_localizationPreserves.away f r _ _ hf

/-- `S` is a finite `R`-algebra if there exists a set `{ r }` that
  spans `R` such that `Sᵣ` is a finite `Rᵣ`-algebra. -/
/-
**RingHom.finite_ofLocalizationSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.finite_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.Fi
nite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ofLocalizationSpan_iff_finite`：RingHom.ofLocalizationSpan_iff_fi
nite : RingHom.OfLocalizationSpan @P ↔ RingHom.OfLocalizationFiniteSpan @P
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
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
· 使用定理 `IsLocalization.smul_mem_finsetIntegerMultiple_span`：IsLocalization.smul_
mem_finsetIntegerMultiple_span [Algebra R S] [Algebra R S'] [IsScalarTower R S S
'] [IsLocalization (M.map (algebraMap R …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.finsetIntegerMultiple.congr_simp`：∀ {R : Type u_1} [inst 
: CommSemiring R] (M M_1 : Submonoid R) (e_M : M = M_1) {S : Type u_2} [inst_1 :
 CommSemiring S]   [inst_2 : Algebra …
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
`S` is a finite `R`-algebra if there exists a set `{ r }` that
  spans `R` such that `Sᵣ` is a finite `Rᵣ`-algebra.
-/
theorem RingHom.finite_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.Finite := by
  classical
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- We first setup the instances
  let := f.toAlgebra
  let := fun r : s => (Localization.awayMap f r).toAlgebra
  have (r : s) : IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S))
      (Localization.Away (f r)) := by
    rw [Submonoid.map_powers]; exact Localization.isLocalization
  have : ∀ r : s, IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
    fun r => IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
  -- By the hypothesis, we may find a finite generating set for each `Sᵣ`. This set can then be
  -- lifted into `R` by multiplying a sufficiently large power of `r`. I claim that the union of
  -- these generates `S`.
  constructor
  replace H := fun r => (H r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  -- It suffices to show that `r ^ n • x ∈ span T` for each `r : s`, since `{ r ^ n }` spans `R`.
  -- This then follows from the fact that each `x : R` is a linear combination of the generating set
  -- of `Sᵣ`. By multiplying a sufficiently large power of `r`, we can cancel out the `r`s in the
  -- denominators of both the generating set and the coefficients.
  rintro x -
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set R) hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_span_of_mem_localization_span (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r))) (algebraMap S _ x)
      (by rw [s₂ r]; trivial)
  dsimp only at hn₁
  rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S, ← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.smul_mem_finsetIntegerMultiple_span (Submonoid.powers (r : R))
      (Localization.Away (f r)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, ← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Submodule.span R (sf x : Set S)) r hn₂
