/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Support

/-!

# Hom(N,M) is subsingleton iff there exists a smul regular element of M in ann(N)

Let `M` and `N` be `R`-modules. In this section we prove that `Hom(N,M)` is subsingleton iff
there exist `r : R`, such that `IsSMulRegular M r` and `r ∈ ann(N)`.
This is the case if `Depth[I](M) = 0`.

## Main statements

* `IsSMulRegular.subsingleton_linearMap_iff` : for `R` module `N M`, `Hom(N, M) = 0`
  iff there is a `M`-regular in `Module.annihilator R N`.

-/

public section

open IsLocalRing LinearMap Module

namespace IsSMulRegular

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-
**IsSMulRegular.linearMap_subsingleton_of_mem_annihilator** 是 Mathlib 中的一个引理，位于命
名空间 `IsSMulRegular`。
形式化陈述：linearMap_subsingleton_of_mem_annihilator {r : R} (reg : IsSMulRegular M r
) (mem_ann : r in Module.annihilator R N) : Subsingleton (N ->ₗ[R] M)
参数：reg : IsSMulRegular M r；mem_ann : r in Module.annihilator R N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma linearMap_subsingleton_of_mem_annihilator {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Module.mem_annihilator.mp mem_ann x, map_zero]
  simpa using reg this
/-
**IsSMulRegular.subsingleton_linearMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsSMulRegu
lar`。
形式化陈述：subsingleton_linearMap_iff [IsNoetherianRing R] [Module.Finite R M] [Modul
e.Finite R N] : Subsingleton (N ->ₗ[R] M) ↔ exists r in Module.annihilator R N, 
IsSMulRegular M r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `IsSMulRegular.zero`：zero [sM : Subsingleton M] : IsSMulRegular M (0 : R)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `associatedPrimes.nonempty`：associatedPrimes.nonempty [IsNoetherianRing R
] [Nontrivial M] : (associatedPrimes R M).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ideal.subset_union_prime_finite`：subset_union_prime_finite {R ι : Type*}
 [CommRing R] {s : Set ι} (hs : s.Finite) {f : ι -> Ideal R} (a b : ι) (hp : for
all i in s, i != a ->…
· 使用定理 `associatedPrimes.finite`：associatedPrimes.finite : (associatedPrimes A M
).Finite
· 使用定理 `IsAssociatedPrime.isPrime`：IsAssociatedPrime.isPrime (h : IsAssociatedPr
ime I M) : I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `biUnion_associatedPrimes_eq_compl_regular`：biUnion_associatedPrimes_eq_c
ompl_regular [IsNoetherianRing R] : ⋃ p in associatedPrimes R M, p = { r : R | I
sSMulRegular M r }ᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.mem_support_iff_of_finite`：Module.mem_support_iff_of_finite : p i
n Module.support R M ↔ Module.annihilator R M <= p.asIdeal
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`：top_ne_ideal_smu
l_of_le_jacobson_annihilator [Nontrivial M] [Module.Finite R M] {I} (h : I <= (M
odule.annihilator R M).jacobson) : (⊤ : Subm…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Module.mem_support_iff`：Module.mem_support_iff : p in Module.support R M
 ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `isAssociatedPrime_iff`：isAssociatedPrime_iff [IsNoetherianRing R] : IsAs
sociatedPrime I M ↔ I.IsPrime ∧ exists x : M, I = colon ⊥ {x}
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)
· 使用定理 `AssociatedPrimes.mem_iff`：AssociatedPrimes.mem_iff : I in associatedPrim
es R M ↔ IsAssociatedPrime I M
· 使用引理 `Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPr
imes`：mem_associatedPrimes_atPrime_of_mem_associatedPrimes {p : Ideal R} [p.IsPr
ime] (ass : p in associatedPrimes R M) : maximalIdeal (Localizatio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 62 条，此处仅展示前 30 条）
-/
lemma subsingleton_linearMap_iff [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] :
    Subsingleton (N →ₗ[R] M) ↔ ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  refine ⟨fun hom0 ↦ ?_, fun ⟨r, mem_ann, reg⟩ ↦
    linearMap_subsingleton_of_mem_annihilator reg mem_ann⟩
  cases subsingleton_or_nontrivial M
  · exact ⟨0, ⟨Submodule.zero_mem (Module.annihilator R N), IsSMulRegular.zero⟩⟩
  · by_contra! h
    have hexist : ∃ p ∈ associatedPrimes R M, Module.annihilator R N ≤ p := by
      rcases associatedPrimes.nonempty R M with ⟨Ia, hIa⟩
      apply (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) Ia Ia _).mp
      · rw [biUnion_associatedPrimes_eq_compl_regular R M]
        exact fun r hr ↦ h r hr
      · exact fun I hin _ _ ↦ IsAssociatedPrime.isPrime hin
    rcases hexist with ⟨p, pass, hp⟩
    let _ := pass.isPrime
    let p' : PrimeSpectrum R := ⟨p, pass.isPrime⟩
    have loc_ne_zero : p' ∈ Module.support R N := Module.mem_support_iff_of_finite.mpr hp
    rw [Module.mem_support_iff] at loc_ne_zero
    let Rₚ := Localization.AtPrime p
    let Nₚ := LocalizedModule.AtPrime p'.asIdeal N
    let Mₚ := LocalizedModule.AtPrime p'.asIdeal M
    let Nₚ' := Nₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)
    have ntr : Nontrivial Nₚ' :=
      Submodule.Quotient.nontrivial_iff.mpr <| .symm <|
        Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator <|
          IsLocalRing.maximalIdeal_le_jacobson _
    let Mₚ' := Mₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Mₚ)
    let _ : Module p.ResidueField Nₚ' :=
      Module.instQuotientIdealSubmoduleHSMulTop Nₚ (maximalIdeal (Localization.AtPrime p))
    have := isAssociatedPrime_iff.mp <| AssociatedPrimes.mem_iff.mp
      (associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes pass)
    rcases this.2 with ⟨x, hx⟩
    have : Nontrivial (Module.Dual p.ResidueField Nₚ') := by simpa using ntr
    rcases exists_ne (α := Module.Dual p.ResidueField Nₚ') 0 with ⟨g, hg⟩
    let to_res' : Nₚ' →ₗ[Rₚ] p.ResidueField := {
      __ := g
      map_smul' r x := by
        simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
        convert! g.map_smul (Ideal.Quotient.mk _ r) x }
    let to_res : Nₚ →ₗ[Rₚ] p.ResidueField :=
      to_res'.comp ((maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)).mkQ
    replace hx : maximalIdeal (Localization.AtPrime p) = (toSpanSingleton _ _ x).ker :=
      hx.trans (by simp [SetLike.ext_iff])
    let i : p.ResidueField →ₗ[Rₚ] Mₚ :=
      Submodule.liftQ _ (LinearMap.toSpanSingleton Rₚ Mₚ x) (le_of_eq hx)
    have inj1 : Function.Injective i :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hx.symm))
    let f := i.comp to_res
    have f_ne0 : f ≠ 0 := by
      intro eq0
      absurd hg
      apply LinearMap.ext
      intro np'
      induction np' using Submodule.Quotient.induction_on with | _ np
      change to_res np = 0
      apply inj1
      change f np = _
      simp [eq0]
    absurd hom0
    let _ := Module.finitePresentation_of_finite R N
    contrapose f_ne0
    exact (Module.FinitePresentation.linearEquivMapExtendScalars
      p'.asIdeal.primeCompl).symm.map_eq_zero_iff.mp (Subsingleton.eq_zero _)

end IsSMulRegular

