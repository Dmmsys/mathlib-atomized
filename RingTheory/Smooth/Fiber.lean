/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Etale.Locus

/-!

# Flat and smooth fibers imply smooth

## Main results
- `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`:
  Let `(R, m, k)` be a local ring, `S` be a local `R`-algebra that is flat,
  essentially of finite presentation, and `k ⊗[R] S` is `k`-formally smooth.
  Then `S` is `R`-formally smooth.
- `Algebra.mem_smoothLocus_of_formallySmooth_fiber`:
  Let `S` be a flat and finitely presented `R`-algebra, and `q` be a prime of `S` lying over `p`.
  If `κ(p) ⊗[R] S` is `κ(p)`-smooth, then `S` is smooth at `q`.
- `Algebra.Smooth.of_formallySmooth_fiber`:
  Flat and finitely presented and smooth fibers imply smooth.
- `Algebra.Etale.of_formallyUnramified_of_flat`:
  Flat and finitely presented and (formally) unramified implies etale.

## Note

For the converse that smooth implies flat, see `Mathlib/RingTheory/Smooth/Flat.lean`.

-/

open TensorProduct IsLocalRing

@[expose] public section

namespace Algebra

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

variable {R S P : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
variable [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]

section IsLocalRing

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallySmooth 𝓀[R] (𝓀[R] ⊗[R] S)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] TensorProduct.rightAlgebra in
/--
Let `(R, m, k)` be a local ring, `(S, M, K)` be a local `R`-algebra that is `R`-flat such that
`k ⊗[R] S` is `k`-formally smooth.

Suppose there exists an `R`-presentation `S = P/I` with `I` finitely generated, and that
`P` is `R`-formally smooth and `Ω[P⁄R]` is `P`-finite free.

Then `S` is `R`-formally smooth.

Such `P` always exists when `S` is essentially of finite presentation over `R`.
See `FormallySmooth.of_formallySmooth_residueField_tensor`.
-/
/-
**Algebra.FormallySmooth.of_formallySmooth_residueField_tensor_aux** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `(R, m, k)` be a local ring, `(S, M, K)` be a local `R`-algebra that is `R`-
flat such that
`k ⊗[R] S` is `k`-formally smooth.

Suppose there exists an `R`-presentation `S = P/I` with `I` finitely generated, 
and that
`P` is `R`-formally smooth and `Ω[P⁄R]` is `P`-finite free.

Then `S` is `R`-formally smooth.

Such `P` always exists when `S` is essentially of finite presentation over `R`.
See `FormallySmooth.of_formallySmooth_residueField_tensor`.
-/
private lemma FormallySmooth.of_formallySmooth_residueField_tensor_aux
    [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S := by
  /-
  From the given presentation `0 → I → P → S → 0`, we construct the presentation
  `0 → k ⊗ᵣ I → k ⊗ᵣ P → k ⊗ᵣ S → 0` using the flatness of `S`.
  We also need the fact that `k ⊗ᵣ S` is also local with residue field `K`.
  -/
  let Sp := 𝓀[R] ⊗[R] S
  let Pp := 𝓀[R] ⊗[R] P
  let φ : Pp →ₐ[𝓀[R]] Sp := Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ψ : Sp →ₐ[R] 𝓀[S] := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom _ _ _)
    (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  algebraize [φ.toRingHom, (φ.toRingHom.comp (algebraMap P Pp)), ψ.toRingHom,
    ψ.toRingHom.comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  have : IsScalarTower P S Sp := .of_algebraMap_eq' rfl
  have : IsScalarTower S Sp 𝓀[S] := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ψ, Sp]
  have : IsScalarTower P Sp 𝓀[S] := .to₁₃₄ _ S _ _
  have : IsScalarTower P Pp 𝓀[S] := .to₁₂₄ _ _ Sp _
  let ePp : Pp ≃ₐ[P] P ⊗[R] 𝓀[R] := { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₀ : Ω[Pp⁄𝓀[R]] ≃ₗ[Pp] Pp ⊗[P] Ω[P⁄R] :=
    (KaehlerDifferential.tensorKaehlerEquiv R 𝓀[R] P Pp).symm
  have : Module.Free Pp Ω[Pp⁄𝓀[R]] := .of_equiv e₀.symm
  have : Module.Finite Pp Ω[Pp⁄𝓀[R]] := .of_surjective e₀.symm.toLinearMap e₀.symm.surjective
  let e₁ : RingHom.ker φ ≃ₗ[Pp] Pp ⊗[P] RingHom.ker (algebraMap P S) :=
    kerTensorProductMapIdToAlgHomEquiv _ _ _ _ h₁
  have h₁' : Function.Surjective φ := LinearMap.lTensor_surjective _ h₁
  have h₂' : (RingHom.ker φ).FG := by
    suffices Module.Finite Pp (RingHom.ker φ) from (Submodule.fg_top _).mp this.1
    have : Module.Finite P (RingHom.ker (algebraMap P S)) := ⟨(Submodule.fg_top _).mpr h₂⟩
    exact .equiv e₁.symm
  have h₃ : 𝓂[Sp] ≤ RingHom.ker ψ := by
    intro x hx
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective _ _ _ (by exact residue_surjective) x
    have : ¬IsUnit x := fun h ↦ hx <| h.map TensorProduct.includeRight
    simpa [ψ, Sp]
  /-
  The key is then to use jacobi criterion `FormallySmooth.iff_injective_cotangentComplexBaseChange`.
  Applying the criterion to `0 → I → P → S → 0` and `0 → k ⊗ᵣ I → k ⊗ᵣ P → k ⊗ᵣ S → 0`,
  the goal becomes the injectivity of `K ⊗ₛ I → K ⊗ₚ Ω[P/R]`,
  while the assumption that `S` is smooth at the maximal ideal translates to the injectivity of
  `K ⊗[k ⊗ᵣ S] (k ⊗ᵣ I) → K ⊗[k ⊗ᵣ P] Ω[k ⊗ᵣ P/R]`.
  -/
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField (P := P) h₁ h₂]
  have := (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
    (R := 𝓀[R]) _ _ h₁' h₂' h₃).mp inferInstance
  -- But `K ⊗[k ⊗ᵣ P] Ω[k ⊗ᵣ P/R] = K ⊗[k ⊗ᵣ P] ((k ⊗ᵣ P) ⊗[P] Ω[P/R]) = K ⊗[P] Ω[P/R]`,
  let eᵣ : 𝓀[S] ⊗[Pp] Ω[Pp⁄𝓀[R]] ≃ₗ[S] 𝓀[S] ⊗[P] Ω[P⁄R] :=
    (AlgebraTensorModule.congr (.refl 𝓀[S] _) e₀).restrictScalars S ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange P Pp Sp 𝓀[S] Ω[P⁄R]).restrictScalars S
  -- and `K ⊗[k ⊗ᵣ S] (k ⊗ᵣ I) = K ⊗[k ⊗ᵣ P] ((k ⊗ᵣ P) ⊗[P] S) = K ⊗[P] S`.
  let eₗ : 𝓀[S] ⊗[Pp] RingHom.ker φ ≃ₗ[S] 𝓀[S] ⊗[P] RingHom.ker (algebraMap P S) :=
    (AlgebraTensorModule.congr (.refl 𝓀[S] 𝓀[S]) e₁).restrictScalars S ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange P Pp Sp 𝓀[S] _).restrictScalars S
  -- It remains to check that the two maps are equal under the identifications above.
  convert! (eᵣ.injective.comp this).comp eₗ.symm.injective
  ext x
  dsimp
  induction x with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y _ _ => simp only [LinearEquiv.map_add, LinearMap.map_add, *]
  | tmul x y =>
  dsimp [eₗ, eᵣ, e₁, KaehlerDifferential.cotangentComplexBaseChange,
    TensorProduct.one_def, Pp, smul_tmul']
  rw [kerTensorProductMapIdToAlgHomEquiv_symm_apply]
  simp [e₀, Pp, ← TensorProduct.one_def]

/--
Let `(R, m, k)` be a local ring, `S` be a local `R`-algebra that is flat,
essentially of finite presentation, and `k ⊗[R] S` is `k`-formally smooth.
Then `S` is `R`-formally smooth.

Since we don't have an "essentially of finite presentation" type class yet, we explicitly require a
`P` that is of finite presentation over `R` and that `S` is a localization of it.
-/
/-
**Algebra.FormallySmooth.of_formallySmooth_residueField_tensor** 是 Mathlib 中的一个定
理，位于命名空间 `Algebra.FormallySmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {P : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Algebra R S]   [Module.Flat R S] [inst_4 : CommRing P] 
[inst_5 : Algebra R P] [inst_6 : Algebra P S] [IsScalarTower R P S]   [inst_8 : 
IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]   [Algebra.Formally
Smooth (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField R
) S)]   (M : Submonoid P) [IsLocalization M S] [Algebra.FinitePresentation R P],
 Algebra.FormallySmooth R S
参数：algebraMap R S；IsLocalRing.ResidueField R；TensorProduct R (IsLocalRing.Residu
eField R) S；M : Submonoid P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.lift_mk'`：lift_mk' (x y) : lift hg (mk' S x y) = g x * ↑(
IsUnit.liftRight (g.toMonoidHom.domRestrict M) hg y)⁻¹
· 使用定理 `Units.coe_liftRight`：coe_liftRight {f : M ->* N} {g : M -> Nˣ} (h : fora
ll x, ↑(g x) = f x) (x) : (liftRight f g h x : N) = f x
· 使用定理 `IsLocalization.mk'_spec_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S]
 [inst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.FinitePresentation.ker_fG_of_surjective`：ker_fG_of_surjective (f
 : A ->ₐ[R] B) (hf : Function.Surjective f) [FinitePresentation R A] [FinitePres
entation R B] : (RingHom.ker f.toRing…
· 使用定理 `Algebra.FinitePresentation.mvPolynomial`：∀ (R : Type w₁) (A : Type w₂) [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Finit
ePresentation R A] (ι : Type …
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
Let `(R, m, k)` be a local ring, `S` be a local `R`-algebra that is flat,
essentially of finite presentation, and `k ⊗[R] S` is `k`-formally smooth.
Then `S` is `R`-formally smooth.

Since we don't have an "essentially of finite presentation" type class yet, we e
xplicitly require a
`P` that is of finite presentation over `R` and that `S` is a localization of it
.
-/
lemma FormallySmooth.of_formallySmooth_residueField_tensor (M : Submonoid P)
    [IsLocalization M S] [Algebra.FinitePresentation R P] : Algebra.FormallySmooth R S := by
  /-
  By the fact that `S` is essentially of finite presentation, we get
  `S = (P/I)[M⁻¹] = P[M⁻¹]/I[M⁻¹]`, where `P` is a polynomial ring and `M` some submonoid of `P/I`.
  We then apply `FormallySmooth.of_formallySmooth_residueField_tensor_aux` to this presentation.
  -/
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] S := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P S).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := M) _ ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  have hfP : (RingHom.ker fP).FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
    convert! this.map (algebraMap _ P')
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M' x
    obtain ⟨a, ha, e⟩ : ∃ a ∈ M, a * f₀ x = 0 := by
      simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff M] using hx
    obtain ⟨a, rfl⟩ := hf₀ a
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨a, ha, by simpa⟩
  algebraize [fP.toRingHom]
  have : FormallyEtale (MvPolynomial (Fin n) R) P' := .of_isLocalization M'
  have : FormallySmooth R P' := .comp _ (MvPolynomial (Fin n) R) _
  have : Module.Free P' Ω[P'⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  exact FormallySmooth.of_formallySmooth_residueField_tensor_aux (R := R) (S := S) hf₁ hfP

end IsLocalRing

-- It is not hard to generalize the proof to get the full generality of the stacks tag.
-- The hard part is figuring out the right way to state the result. Hence we refrain from this
-- generalization until we have an application.
@[stacks 00TF "We require the whole fiber to be smooth instead"]
/-
**Algebra.IsSmoothAt.of_formallySmooth_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
IsSmoothAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Module.Flat R S]   [Algebra.FinitePresentation R S] (p :
 Ideal R) (q : Ideal S) [inst_5 : p.IsPrime] [inst_6 : q.IsPrime] [q.LiesOver p]
   [Algebra.FormallySmooth p.ResidueField (p.Fiber S)], Algebra.IsSmoothAt R q
参数：p : Ideal R；q : Ideal S；p.Fiber S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.map_algebraMap`：∀ {R : Type u} {S : Type v} {A : Type w} {B : Typ
e u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] 
[inst_3 : S…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.primeCompl.congr_simp`：∀ {α : Type u} [inst : Semiring α] (P P_1 :
 Ideal α) (e_P : P = P_1) [hp : P.IsPrime], P.primeCompl = P_1.primeCompl
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsScalarTower.to₁₃₄`：∀ (M : Type u_9) (N : Type u_10) (P : Type u_11) (Q
 : Type u_12) [inst : SMul M N] [inst_1 : SMul M P]   [inst_2 : SMul M Q] [inst_
3 : SMul …
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `instIsScalarTowerLocalizationAlgebraMapSubmonoid`：∀ {R : Type u_1} [inst
 : CommSemiring R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   
[inst_2 : Algebra R S], IsScalarTower …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.isLocalization_of_submonoid_le`：isLocalization_of_submono
id_le (M N : Submonoid R) (h : M <= N) [IsLocalization M S] [IsLocalization N T]
 [Algebra S T] [IsScalarTower R S T…
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Algebra.TensorProduct.instSMulCommClassTensorProduct_1`：∀ {R : Type uR} 
{A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_
2 : Algebra R A]   [inst_3 : CommSemiring B]…
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `Algebra.FormallySmooth.instTensorProduct`：∀ {R : Type u_4} [inst : CommR
ing R] {A : Type u_5} [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6
)   [inst_3 : CommRing B] [ins…
（共 48 条，此处仅展示前 30 条）
-/
lemma IsSmoothAt.of_formallySmooth_fiber
    [Algebra.FinitePresentation R S] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] [FormallySmooth p.ResidueField (p.Fiber S)] :
    Algebra.IsSmoothAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : FormallySmooth 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) := by
    let : Algebra S (𝓀[Rp] ⊗[R] S) := TensorProduct.rightAlgebra
    have : FormallySmooth 𝓀[Rp] ((𝓀[Rp] ⊗[R] S) ⊗[S] Sq) :=
      .comp _ (𝓀[Rp] ⊗[R] S) _
    let e : 𝓀[Rp] ⊗[R] S ≃ₐ[S] S ⊗[R] 𝓀[Rp] :=
      { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
    let e' : (𝓀[Rp] ⊗[R] S) ⊗[S] Sq ≃ₐ[R] 𝓀[Rp] ⊗[Rp] Sq :=
      ((TensorProduct.comm _ _ _).restrictScalars R).trans <|
      ((TensorProduct.congr (.refl (R := S)) e).restrictScalars R).trans <|
      ((TensorProduct.cancelBaseChange _ _ S _ _).restrictScalars R).trans <|
      (TensorProduct.comm _ _ _).trans (TensorProduct.equivOfCompatibleSMul ..)
    have : e'.toAlgHom.comp (IsScalarTower.toAlgHom R p.ResidueField _) =
        IsScalarTower.toAlgHom _ _ _ := by ext
    let e'' : (𝓀[Rp] ⊗[R] S) ⊗[S] Sq ≃ₐ[𝓀[Rp]] 𝓀[Rp] ⊗[Rp] Sq :=
      { __ := e', commutes' r := congr($this r) }
    exact .of_equiv e''
  have := FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq
/-
**Algebra.Smooth.of_formallySmooth_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smoo
th`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Module.Flat R S]   [Algebra.FinitePresentation R S],   (
∀ (I : Ideal R) [inst_5 : I.IsPrime], Algebra.FormallySmooth I.ResidueField (I.F
iber S)) → Algebra.Smooth R S
参数：∀ (I : Ideal R) [inst_5 : I.IsPrime], Algebra.FormallySmooth I.ResidueField (
I.Fiber S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.smoothLocus_eq_univ_iff`：smoothLocus_eq_univ_iff [FinitePresenta
tion R A] : smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Algebra.IsSmoothAt.of_formallySmooth_fiber`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Fla
t R S]   [Algebra.FinitePresenta…
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
lemma Smooth.of_formallySmooth_fiber [Algebra.FinitePresentation R S]
    (H : ∀ (I : Ideal R) [I.IsPrime], FormallySmooth I.ResidueField (I.Fiber S)) :
    Algebra.Smooth R S := by
  refine ⟨smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q ↦ ?_), ‹_›⟩
  exact .of_formallySmooth_fiber (q.asIdeal.under R) _

attribute [local instance] FormallyEtale.of_formallyUnramified_of_field in
@[stacks 08WD "(3) => (1)"]
/-
**Algebra.Etale.of_formallyUnramified_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.Etale`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FinitePresentation R S] [Module.Flat R S] [Alg
ebra.FormallyUnramified R S], Algebra.Etale R S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Smooth.of_formallySmooth_fiber`：∀ {R : Type u_1} {S : Type u_2} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Flat R 
S]   [Algebra.FinitePresenta…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用引理 `Algebra.FormallyEtale.of_formallyUnramified_of_field`：of_formallyUnramif
ied_of_field [EssFiniteType K A] [FormallyUnramified K A] : FormallyEtale K A
· 使用定理 `Algebra.EssFiniteType.baseChange`：∀ (R : Type u_1) (S : Type u_2) (T : T
ype u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst
_3 : Algebra R S] [ins…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`：∀ {R : Type
 v} {A : Type u} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A
}   [self : Algebra.FormallyUnramified R A], Subs…
· 使用定理 `Algebra.FormallySmooth.subsingleton_h1Cotangent`：∀ {R : Type u} {A : Typ
e v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : 
Algebra.FormallySmooth R A], Subsingl…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
-/
lemma Etale.of_formallyUnramified_of_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S] [FormallyUnramified R S] :
    Etale R S :=
  have : Smooth R S := .of_formallySmooth_fiber inferInstance
  ⟨⟨inferInstance, inferInstance⟩, ‹_›⟩
/-
**Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsEtaleAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Module.Flat R S]   [Algebra.FinitePresentation R S] (q :
 Ideal S) [inst_5 : q.IsPrime] [Algebra.IsUnramifiedAt R q],   Algebra.IsEtaleAt
 R q
参数：q : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.exists_unramified_of_isUnramifiedAt`：exists_unramified_of_isUnra
mifiedAt [Algebra.FiniteType R A] (p : Ideal A) [p.IsPrime] [IsUnramifiedAt R p]
 : exists f ∉ p, Algebra.Unramifi…
· 使用定理 `Algebra.Etale.of_formallyUnramified_of_flat`：∀ {R : Type u_4} {S : Type 
u_5} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FinitePresentation R S] [Module.…
· 使用定理 `instFinitePresentationAway`：∀ {R : Type u_1} [inst : CommRing R] {S : Ty
pe u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FinitePresentati
on R S] (f : S),…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Algebra.basicOpen_subset_etaleLocus_iff`：basicOpen_subset_etaleLocus_iff
 {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq etaleLocus R A ↔ Algebra.Formal
lyEtale R (Localization.Away …
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
-/
lemma IsEtaleAt.of_isUnramifiedAt_of_flat
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] [IsUnramifiedAt R q] :
    IsEtaleAt R q := by
  obtain ⟨f, hfp, H⟩ := exists_unramified_of_isUnramifiedAt (R := R) q
  change ⟨q, ‹_›⟩ ∈ etaleLocus R S
  suffices Algebra.Etale R (Localization.Away f) from
    (basicOpen_subset_etaleLocus_iff (R := R) (f := f)).mpr inferInstance hfp
  exact .of_formallyUnramified_of_flat

end Algebra

