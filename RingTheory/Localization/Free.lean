/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Free modules and localization

## Main result

- `Module.FinitePresentation.exists_free_localizedModule_powers`:
  If `M` is a finitely presented `R`-module
  such that `Mₛ` is free over `Rₛ` for some `S : Submonoid R`,
  then `Mᵣ` is already free over `Rᵣ` for some `r ∈ S`.

In the file `Mathlib.RingTheory.Spectrum.Prime.FreeLocus`, we deduce that the free
locus of a finitely presented module is open and its rank is locally constant.
-/

public section

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (S : Submonoid R) [AddCommGroup N'] [Module R N']

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

include f in
/--
If `M` is a finitely presented `R`-module,
then any `Rₛ`-basis of `Mₛ` for some `S : Submonoid R` can be lifted to
a `Rᵣ`-basis of `Mᵣ` for some `r ∈ S`.
-/
/-
**Module.FinitePresentation.exists_basis_localizedModule_powers** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：Module.FinitePresentation.exists_basis_localizedModule_powers (Rₛ) [CommRi
ng Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [IsLocalization S R
ₛ] [Module.FinitePresentation R M] {I} [Finite I] (b : Basis I Rₛ M') : exists (
r : R) (hr : r in S) (b' : Basis I (Localization (.powers r)) (LocalizedModule.A
way r M)), forall i, (LocalizedModule.lift (.powers r) f fun s => IsLocalizedMod
ule.map_units f ⟨s.1, SetLike.le_def.mp (Submonoid.powers_le.mpr hr) s.2⟩) (b' i
) = b i
参数：Rₛ；b : Basis I Rₛ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.finitePresentation_of_projective`：Module.finitePresentation_of_pr
ojective [Projective R M] [Module.Finite R M] : FinitePresentation R M
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `instIsLocalizedModuleFinsuppLinearMap`：∀ (R : Type u_1) [inst : CommSemi
ring R] (S : Submonoid R) (M : Type u_3) [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] {M' : Ty…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用引理 `Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule`：Module
.FinitePresentation.exists_lift_equiv_of_isLocalizedModule [Module.FinitePresent
ation R M] [Module.FinitePresentation R N] (l : M' ≃ₗ[…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `IsLocalizedModule.iso_symm_comp`：iso_symm_comp : (iso S f).symm.toLinear
Map.comp f = LocalizedModule.mkLinearMap S M
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` is a finitely presented `R`-module,
then any `Rₛ`-basis of `Mₛ` for some `S : Submonoid R` can be lifted to
a `Rᵣ`-basis of `Mᵣ` for some `r ∈ S`.
-/
lemma Module.FinitePresentation.exists_basis_localizedModule_powers
    (Rₛ) [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M']
    [IsLocalization S Rₛ] [Module.FinitePresentation R M]
    {I} [Finite I] (b : Basis I Rₛ M') :
    ∃ (r : R) (hr : r ∈ S)
      (b' : Basis I (Localization (.powers r)) (LocalizedModule.Away r M)),
      ∀ i, (LocalizedModule.lift (.powers r) f fun s ↦ IsLocalizedModule.map_units f
        ⟨s.1, SetLike.le_def.mp (Submonoid.powers_le.mpr hr) s.2⟩) (b' i) = b i := by
  have : Module.FinitePresentation R (I →₀ R) := Module.finitePresentation_of_projective _ _
  obtain ⟨r, hr, e, he⟩ := Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule S f
    (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ)) (b.repr.restrictScalars R)
  let e' := IsLocalizedModule.iso (.powers r) (Finsupp.mapRange.linearMap (α := I)
    (Algebra.linearMap R (Localization (.powers r))))
  refine ⟨r, hr, .ofRepr (e ≪≫ₗ ?_), ?_⟩
  · exact
    { __ := e',
      toLinearMap := e'.extendScalarsOfIsLocalization (.powers r) (Localization (.powers r)) }
  · intro i
    have : e'.symm _ = _ := LinearMap.congr_fun (IsLocalizedModule.iso_symm_comp (.powers r)
      (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization (.powers r)))))
      (Finsupp.single i 1)
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply,
      map_one, LocalizedModule.mkLinearMap_apply] at this
    change LocalizedModule.lift _ _ _ (e.symm (e'.symm _)) = _
    replace he := LinearMap.congr_fun he (e.symm (e'.symm (Finsupp.single i 1)))
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply] at he
    apply b.repr.injective
    rw [← he, Basis.repr_self, this, LocalizedModule.lift_mk]
    simp

include f in
/--
If `M` is a finitely presented `R`-module
such that `Mₛ` is free over `Rₛ` for some `S : Submonoid R`,
then `Mᵣ` is already free over `Rᵣ` for some `r ∈ S`.
-/
/-
**Module.FinitePresentation.exists_free_localizedModule_powers** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：Module.FinitePresentation.exists_free_localizedModule_powers (Rₛ) [CommRin
g Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [Nontrivial Rₛ] [IsL
ocalization S Rₛ] [Module.FinitePresentation R M] [Module.Free Rₛ M'] : exists r
, r in S ∧ Module.Free (Localization (.powers r)) (LocalizedModule.Away r M) ∧ M
odule.finrank (Localization (.powers r)) (LocalizedModule.Away r M) = Module.fin
rank Rₛ M'
参数：Rₛ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.of_isLocalizedModule`：of_isLocalizedModule [Module.Finite 
R M] : Module.Finite Rₚ Mₚ
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Module.FinitePresentation.exists_basis_localizedModule_powers`：Module.Fi
nitePresentation.exists_basis_localizedModule_powers (Rₛ) [CommRing Rₛ] [Algebra
 R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [IsLo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_nat_card_basis`：finrank_eq_nat_card_basis (h : Basis ι
 R M) : finrank R M = Nat.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R

--- 原说明 ---
If `M` is a finitely presented `R`-module
such that `Mₛ` is free over `Rₛ` for some `S : Submonoid R`,
then `Mᵣ` is already free over `Rᵣ` for some `r ∈ S`.
-/
lemma Module.FinitePresentation.exists_free_localizedModule_powers
    (Rₛ) [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [Nontrivial Rₛ]
    [IsLocalization S Rₛ] [Module.FinitePresentation R M] [Module.Free Rₛ M'] :
    ∃ r, r ∈ S ∧
      Module.Free (Localization (.powers r)) (LocalizedModule.Away r M) ∧
      Module.finrank (Localization (.powers r)) (LocalizedModule.Away r M) =
        Module.finrank Rₛ M' := by
  let I := Module.Free.ChooseBasisIndex Rₛ M'
  let b : Basis I Rₛ M' := Module.Free.chooseBasis Rₛ M'
  have : Module.Finite Rₛ M' := Module.Finite.of_isLocalizedModule S (Rₚ := Rₛ) f
  obtain ⟨r, hr, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers S f Rₛ b
  have := (show Localization (.powers r) →+* Rₛ from IsLocalization.map (M := .powers r) (T := S) _
    (RingHom.id _) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  refine ⟨r, hr, .of_basis b', ?_⟩
  rw [Module.finrank_eq_nat_card_basis b, Module.finrank_eq_nat_card_basis b']
