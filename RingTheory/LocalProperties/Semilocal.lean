/-
Copyright (c) 2025 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
module

public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# Local properties for semilocal rings

This file proves some local properties for a semilocal ring `R` (a ring with
finitely many maximal ideals).

## Main results

* `Module.Finite.of_isLocalized_maximal`: A module `M` over a semilocal ring `R` is finite if its
  localization at every maximal ideal is finite.
* `IsNoetherianRing.of_isLocalization_maximal`: A semilocal ring `R` is Noetherian if its
  localization at every maximal ideal is a Noetherian ring.
* `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal`: A semilocal
  integral domain `A` is a PID if its localization at every maximal ideal is a PID.
-/

public section

section CommSemiring

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

section IsLocalized

include f in
/-- A module `M` over a semilocal ring `R` is finite if
its localization at every maximal ideal is finite. -/
/-
**Module.Finite.of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Finite.of_isLocalized_maximal (H : forall (P : Ideal R) [P.IsMaxima
l], Module.Finite (Rₚ P) (Mₚ P)) : Module.Finite R M
参数：H : forall (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Submodule.eq_top_of_localization_maximal`：Submodule.eq_top_of_localizati
on_maximal (N : Submodule R M) (h : forall (P : Ideal R) [P.IsMaximal], N.locali
zed' (Rₚ P) P.primeCompl (f P)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.localized'_span`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3
} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : A
ddCommMonoid M]…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.FinsetCoe.canLift`：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s
) Subtype.val fun a => a ∈ s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用引理 `IsLocalization.smul_mem_iff`：smul_mem_iff {N' : Submodule R' M'} {x : M'
} {s : S} : s • x in N' ↔ x in N'
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…

--- 原说明 ---
A module `M` over a semilocal ring `R` is finite if
its localization at every maximal ideal is finite.
-/
theorem Module.Finite.of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) :
    Module.Finite R M := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose s hs using fun P : MaximalSpectrum R ↦ (H P.1).fg_top
  choose frac hfrac using fun P : MaximalSpectrum R ↦ IsLocalizedModule.surj P.1.primeCompl (f P.1)
  use Finset.biUnion Finset.univ fun P ↦ Finset.image (frac P · |>.1) (s P)
  refine Submodule.eq_top_of_localization_maximal Rₚ Mₚ f _ fun P hP ↦ ?_
  rw [eq_top_iff, ← hs ⟨P, hP⟩, Submodule.localized'_span, Submodule.span_le]
  intro x hx
  lift x to s ⟨P, hP⟩ using hx
  rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := (frac ⟨P, hP⟩ x).2), hfrac]
  exact Submodule.subset_span ⟨_, by simpa using ⟨_, _, x.2, rfl⟩, rfl⟩

variable {M} in
/-- A submodule `N` of a module `M` over a semilocal ring `R` is finitely generated if
its localization at every maximal ideal is finitely generated. -/
/-
**Submodule.fg_of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.fg_of_isLocalized_maximal (N : Submodule R M) (H : forall (P : I
deal R) [P.IsMaximal], (Submodule.localized' (Rₚ P) P.primeCompl (f P) N).FG) : 
N.FG
参数：N : Submodule R M；H : forall (P : Ideal R) [P.IsMaximal], (Submodule.localize
d' (Rₚ P) P.primeCompl (f P) N).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.Finite.of_isLocalized_maximal`：Module.Finite.of_isLocalized_maxim
al (H : forall (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) : Modul
e.Finite R M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
A submodule `N` of a module `M` over a semilocal ring `R` is finitely generated 
if
its localization at every maximal ideal is finitely generated.
-/
theorem Submodule.fg_of_isLocalized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (Submodule.localized' (Rₚ P) P.primeCompl (f P) N).FG) :
    N.FG := by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  exact .of_isLocalized_maximal _ _ _ (fun P ↦ N.toLocalized' (Rₚ P) P.primeCompl (f P)) H

end IsLocalized

section Localized

/-
**Module.Finite.of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Finite.of_localized_maximal (H : forall (P : Ideal R) [P.IsMaximal]
, Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) : 
Module.Finite R M
参数：H : forall (P : Ideal R) [P.IsMaximal], Module.Finite (Localization P.primeCo
mpl) (LocalizedModule P.primeCompl M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.Finite.of_isLocalized_maximal`：Module.Finite.of_isLocalized_maxim
al (H : forall (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) : Modul
e.Finite R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
-/
theorem Module.Finite.of_localized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  .of_isLocalized_maximal M _ _ (fun _ _ ↦ LocalizedModule.mkLinearMap _ _) H

variable {M} in
/-
**Submodule.fg_of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.fg_of_localized_maximal (N : Submodule R M) (H : forall (P : Ide
al R) [P.IsMaximal], (N.localized P.primeCompl).FG) : N.FG
参数：N : Submodule R M；H : forall (P : Ideal R) [P.IsMaximal], (N.localized P.prim
eCompl).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.fg_of_isLocalized_maximal`：Submodule.fg_of_isLocalized_maximal
 (N : Submodule R M) (H : forall (P : Ideal R) [P.IsMaximal], (Submodule.localiz
ed' (Rₚ P) P.primeCompl (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
-/
theorem Submodule.fg_of_localized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (N.localized P.primeCompl).FG) :
    N.FG := N.fg_of_isLocalized_maximal _ _ _ H

end Localized

section IsLocalization

/-- A semilocal ring `R` is Noetherian if
its localization at every maximal ideal is a Noetherian ring. -/
/-
**IsNoetherianRing.of_isLocalization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherianRing.of_isLocalization_maximal (H : forall (P : Ideal R) [P.Is
Maximal], IsNoetherianRing (Rₚ P)) : IsNoetherianRing R where noetherian N
参数：H : forall (P : Ideal R) [P.IsMaximal], IsNoetherianRing (Rₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.fg_of_isLocalized_maximal`：Submodule.fg_of_isLocalized_maximal
 (N : Submodule R M) (H : forall (P : Ideal R) [P.IsMaximal], (Submodule.localiz
ed' (Rₚ P) P.primeCompl (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…

--- 原说明 ---
A semilocal ring `R` is Noetherian if
its localization at every maximal ideal is a Noetherian ring.
-/
theorem IsNoetherianRing.of_isLocalization_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], IsNoetherianRing (Rₚ P)) :
    IsNoetherianRing R where
  noetherian N := Submodule.fg_of_isLocalized_maximal
    Rₚ Rₚ (fun P _ => Algebra.linearMap R (Rₚ P)) N fun _ _ ↦ IsNoetherian.noetherian _

end IsLocalization

end CommSemiring

section CommRing

section IsLocalization

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]

/-- A semilocal integral domain `A` is a PID if its localization at every maximal ideal is a PID. -/
/-
**isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal [IsDom
ain R] (hpid : forall (P : Ideal R) [P.IsMaximal], IsPrincipalIdealRing (Rₚ P)) 
: IsPrincipalIdealRing R
参数：hpid : forall (P : Ideal R) [P.IsMaximal], IsPrincipalIdealRing (Rₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsNoetherianRing.of_isLocalization_maximal`：IsNoetherianRing.of_isLocali
zation_maximal (H : forall (P : Ideal R) [P.IsMaximal], IsNoetherianRing (Rₚ P))
 : IsNoetherianRing R where noet…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `IsIntegrallyClosed.of_isLocalization_maximal`：IsIntegrallyClosed.of_isLo
calization_maximal [IsDomain R] (h : forall (P : Ideal R) [P.IsMaximal], IsInteg
rallyClosed (Rₚ P)) : IsIntegrally…
· 使用定理 `IsLocalization.isDomain_of_atPrime`：isDomain_of_atPrime (S : Type*) [Com
mSemiring S] [Algebra A S] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime S P
] : IsDomain S
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用引理 `Ring.krullDimLE_of_isLocalization_maximal`：Ring.krullDimLE_of_isLocaliza
tion_maximal {n : Nat} (h : forall (P : Ideal R) [P.IsMaximal], Ring.KrullDimLE 
n (Rₚ P)) : Ring.KrullDimLE n R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.krullDimLE_one_iff_of_noZeroDivisors`：Ring.krullDimLE_one_iff_of_no
ZeroDivisors [NoZeroDivisors R] : Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I !=
 ⊥ -> I.IsPrime -> I.IsMaximal
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MaximalSpectrum.range_asIdeal`：range_asIdeal : Set.range MaximalSpectrum
.asIdeal = {J : Ideal R | J.IsMaximal}
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `IsPrincipalIdealRing.of_finite_maximals`：IsPrincipalIdealRing.of_finite_
maximals [IsDedekindDomain R] (h : {I : Ideal R | I.IsMaximal}.Finite) : IsPrinc
ipalIdealRing R

--- 原说明 ---
A semilocal integral domain `A` is a PID if its localization at every maximal id
eal is a PID.
-/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal [IsDomain R]
    (hpid : ∀ (P : Ideal R) [P.IsMaximal], IsPrincipalIdealRing (Rₚ P)) :
    IsPrincipalIdealRing R := by
  have : IsNoetherianRing R :=
    IsNoetherianRing.of_isLocalization_maximal Rₚ fun P _ => inferInstance
  have : IsIntegrallyClosed R := by
    refine IsIntegrallyClosed.of_isLocalization_maximal Rₚ fun P hP => ?_
    have : IsDomain (Rₚ P) := IsLocalization.isDomain_of_atPrime (Rₚ P) P
    infer_instance
  have : Ring.KrullDimLE 1 R :=
    Ring.krullDimLE_of_isLocalization_maximal Rₚ fun P _ => inferInstance
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors] at this
  have dedekind : IsDedekindDomain R := { maximalOfPrime := this _ }
  have hp_finite : {P : Ideal R | P.IsMaximal}.Finite := by
    rw [← MaximalSpectrum.range_asIdeal]
    exact Set.finite_range MaximalSpectrum.asIdeal
  exact IsPrincipalIdealRing.of_finite_maximals hp_finite

end IsLocalization

end CommRing

