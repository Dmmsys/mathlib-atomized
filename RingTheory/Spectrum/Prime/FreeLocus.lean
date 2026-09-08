/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.Support

/-!

# The free locus of a module

## Main definitions and results

Let `M` be a finitely presented `R`-module.
- `Module.freeLocus`: The set of points `x` in `Spec R` such that `Mₓ` is free over `Rₓ`.
- `Module.freeLocus_eq_univ_iff`:
  The free locus is the whole `Spec R` if and only if `M` is projective.
- `Module.basicOpen_subset_freeLocus_iff`: `D(f)` is contained in the free locus if and only if
  `M_f` is projective over `R_f`.
- `Module.rankAtStalk`: The function `Spec R → ℕ` sending `x` to `rank_{Rₓ} Mₓ`.
- `Module.isLocallyConstant_rankAtStalk`:
  If `M` is flat over `R`, then `rankAtStalk` is locally constant.

-/

@[expose] public section

universe uR uM

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

open PrimeSpectrum TensorProduct

/-- The free locus of a module, i.e. the set of primes `p` such that `Mₚ` is free over `Rₚ`. -/
/-
**Module.freeLocus** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：freeLocus : Set (PrimeSpectrum R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free locus of a module, i.e. the set of primes `p` such that `Mₚ` is free ov
er `Rₚ`.
-/
def freeLocus : Set (PrimeSpectrum R) :=
  { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

variable {R M}
/-
**Module.mem_freeLocus** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：mem_freeLocus {p} : p in freeLocus R M ↔ Module.Free (Localization.AtPrime
 p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_freeLocus {p} : p ∈ freeLocus R M ↔
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
  Iff.rfl

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-
**Module.mem_freeLocus_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：mem_freeLocus_of_isLocalization (p : PrimeSpectrum R) (Rₚ Mₚ) [CommRing Rₚ
] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] [AddCommGroup Mₚ] [Module
 R Mₚ] (f : M ->ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f] [Module Rₚ M
ₚ] [IsScalarTower R Rₚ Mₚ] : p in freeLocus R M ↔ Module.Free Rₚ Mₚ
参数：p : PrimeSpectrum R；Rₚ Mₚ；f : M ->ₗ[R] Mₚ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Module.Free.iff_of_equiv`：iff_of_equiv {R R' M M'} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ' : R…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalization.algEquiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_id_mk'`：map_id_mk' {Q : Type*} [CommSemiring Q] [Alge
bra R Q] [IsLocalization M Q] (x) (y : M) : map Q (RingHom.id R) (le_refl M) (mk
' S x y) = mk' …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
-/
lemma mem_freeLocus_of_isLocalization (p : PrimeSpectrum R)
    (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]
    [AddCommGroup Mₚ] [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ Mₚ := by
  set e := (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  apply Module.Free.iff_of_equiv (σ := e)
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-
**Module.mem_freeLocus_iff_tensor** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：mem_freeLocus_iff_tensor (p : PrimeSpectrum R) (Rₚ) [CommRing Rₚ] [Algebra
 R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] : p in freeLocus R M ↔ Module.Free 
Rₚ (Rₚ otimes[R] M)
参数：p : PrimeSpectrum R；Rₚ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Module.mem_freeLocus_of_isLocalization`：mem_freeLocus_of_isLocalization 
(p : PrimeSpectrum R) (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPri
me Rₚ p.asIdeal] [AddCommGro…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma mem_freeLocus_iff_tensor (p : PrimeSpectrum R)
    (Rₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ (Rₚ ⊗[R] M) := by
  exact mem_freeLocus_of_isLocalization p Rₚ (f := TensorProduct.mk R Rₚ M 1)
/-
**Module.freeLocus_congr** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：freeLocus_congr {M'} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') : fr
eeLocus R M = freeLocus R M'
参数：e : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Module.mem_freeLocus_of_isLocalization`：mem_freeLocus_of_isLocalization 
(p : PrimeSpectrum R) (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPri
me Rₚ p.asIdeal] [AddCommGro…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
-/
lemma freeLocus_congr {M'} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    freeLocus R M = freeLocus R M' := by
  ext p
  exact mem_freeLocus_of_isLocalization _ _ _
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-
**Module.comap_freeLocus_le** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：comap_freeLocus_le {A} [CommRing A] [Algebra R A] : comap (algebraMap R A)
 ⁻¹' freeLocus R M <= freeLocus A (A otimes[R] M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.mem_freeLocus_iff_tensor`：mem_freeLocus_iff_tensor (p : PrimeSpec
trum R) (Rₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] 
: p in freeLocus R M …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
-/
lemma comap_freeLocus_le {A} [CommRing A] [Algebra R A] :
    comap (algebraMap R A) ⁻¹' freeLocus R M ≤ freeLocus A (A ⊗[R] M) := by
  intro p hp
  let Rₚ := Localization.AtPrime (comap (algebraMap R A) p).asIdeal
  let Aₚ := Localization.AtPrime p.asIdeal
  rw [Set.mem_preimage, mem_freeLocus_iff_tensor _ Rₚ] at hp
  rw [mem_freeLocus_iff_tensor _ Aₚ]
  let algebra : Algebra Rₚ Aₚ := (Localization.localRingHom
    (comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) rfl).toAlgebra
  have : IsScalarTower R Rₚ Aₚ := IsScalarTower.of_algebraMap_eq'
    (by simp [Rₚ, Aₚ, algebra, RingHom.algebraMap_toAlgebra, Localization.localRingHom,
        ← IsScalarTower.algebraMap_eq])
  let e := AlgebraTensorModule.cancelBaseChange R Rₚ Aₚ Aₚ M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R A Aₚ Aₚ M).symm
  exact .of_equiv e
/-
**Module.freeLocus_localization** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：freeLocus_localization (S : Submonoid R) : freeLocus (Localization S) (Loc
alizedModule S M) = comap (algebraMap R _) ⁻¹' freeLocus R M
参数：S : Submonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.localization_isScalarTower_of_submonoid_le`：localization_
isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M <= N) [IsLocalization M
 S] [IsLocalization N T] : @IsScalarTower R S T…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.isLocalization_of_submonoid_le`：isLocalization_of_submono
id_le (M N : Submonoid R) (h : M <= N) [IsLocalization M S] [IsLocalization N T]
 [Algebra S T] [IsScalarTower R S T…
· 使用定理 `IsLocalization.isLocalization_of_is_exists_mul_mem`：isLocalization_of_is
_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M <= N) (h' : fora
ll x : N, exists m : R, m * x in M) : Is…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
（共 36 条，此处仅展示前 30 条）
-/
lemma freeLocus_localization (S : Submonoid R) :
    freeLocus (Localization S) (LocalizedModule S M) =
      comap (algebraMap R _) ⁻¹' freeLocus R M := by
  ext p
  simp only [Set.mem_preimage]
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : S ≤ p'.primeCompl := fun x hx H ↦
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x, hx⟩))
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeCompl M
  let : Algebra (Localization S) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S p'.primeCompl hp'
  have : IsScalarTower R (Localization S) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime Rₚ p.asIdeal := by
    have := IsLocalization.isLocalization_of_submonoid_le (Localization S) Rₚ _ _ hp'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap R (Localization S)) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  let : Module (Localization S) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization S) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [p', Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization S) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap p'.primeCompl M)).extendScalarsOfIsLocalization S
    (Localization S)
  have : IsLocalizedModule p.asIdeal.primeCompl l := by
    have : IsLocalizedModule p'.primeCompl (l.restrictScalars R) :=
      inferInstanceAs (IsLocalizedModule p'.primeCompl
        (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap p'.primeCompl M)))
    have : IsLocalizedModule (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p'.primeCompl ..
    apply IsLocalizedModule.of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  rw [mem_freeLocus_of_isLocalization (R := Localization S) p Rₚ Mₚ l]
  rfl
/-
**Module.freeLocus_eq_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：freeLocus_eq_univ_iff [Module.FinitePresentation R M] : freeLocus R M = Se
t.univ ↔ Module.Projective R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Module.projective_of_localization_maximal`：Module.projective_of_localiza
tion_maximal (H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Loc
alization.AtPrime I) (Localized…
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
-/
lemma freeLocus_eq_univ_iff [Module.FinitePresentation R M] :
    freeLocus R M = Set.univ ↔ Module.Projective R M := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H ↦ Module.projective_of_localization_maximal fun I hI ↦
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x ↦ Module.free_of_flat_of_isLocalRing⟩
/-
**Module.freeLocus_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：freeLocus_eq_univ [Module.Finite R M] [Module.Flat R M] : freeLocus R M = 
Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
-/
lemma freeLocus_eq_univ [Module.Finite R M] [Module.Flat R M] :
    freeLocus R M = Set.univ := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact fun x ↦ Module.free_of_flat_of_isLocalRing
/-
**Module.basicOpen_subset_freeLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f : R} : (
basicOpen f : Set (PrimeSpectrum R)) subseteq freeLocus R M ↔ Module.Projective 
(Localization.Away f) (LocalizedModule.Away f M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.freeLocus_eq_univ_iff`：freeLocus_eq_univ_iff [Module.FinitePresen
tation R M] : freeLocus R M = Set.univ ↔ Module.Projective R M
· 使用定理 `instFinitePresentationLocalizationLocalizedModule`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   (S : Submonoid R) [Module.Finit…
· 使用引理 `Module.freeLocus_localization`：freeLocus_localization (S : Submonoid R) 
: freeLocus (Localization S) (LocalizedModule S M) = comap (algebraMap R _) ⁻¹' 
freeLocus R M
· 使用定理 `Set.preimage_eq_univ_iff`：preimage_eq_univ_iff {f : α -> β} {s} : f ⁻¹' 
s = univ ↔ range f subseteq s
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f : R} :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆ freeLocus R M ↔
      Module.Projective (Localization.Away f) (LocalizedModule.Away f M) := by
  rw [← freeLocus_eq_univ_iff, freeLocus_localization,
    Set.preimage_eq_univ_iff, localization_away_comap_range _ f]
/-
**Module.isOpen_freeLocus** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：isOpen_freeLocus [Module.FinitePresentation R M] : IsOpen (freeLocus R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Module.FinitePresentation.exists_free_localizedModule_powers`：Module.Fin
itePresentation.exists_free_localizedModule_powers (Rₛ) [CommRing Rₛ] [Algebra R
 Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [Nontr…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用引理 `Module.basicOpen_subset_freeLocus_iff`：basicOpen_subset_freeLocus_iff [M
odule.FinitePresentation R M] {f : R} : (basicOpen f : Set (PrimeSpectrum R)) su
bseteq freeLocus R M ↔ Modu…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
lemma isOpen_freeLocus [Module.FinitePresentation R M] :
    IsOpen (freeLocus R M) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨basicOpen r, basicOpen_subset_freeLocus_iff.mpr inferInstance, (basicOpen r).2, hr⟩

variable (M) in
/-- The rank of `M` at the stalk of `p` is the rank of `Mₚ` as a `Rₚ`-module. -/
noncomputable
/-
**Module.rankAtStalk** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：rankAtStalk (p : PrimeSpectrum R) : Nat
参数：p : PrimeSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rankAtStalk (p : PrimeSpectrum R) : ℕ :=
  Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)
/-
**Module.isLocallyConstant_rankAtStalk_freeLocus** 是 Mathlib 中的一个引理，位于命名空间 `Modu
le`。
形式化陈述：isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M] : 
IsLocallyConstant (fun x : freeLocus R M => rankAtStalk M x.1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocallyConstant.iff_exists_open`：iff_exists_open (f : X -> Y) : IsLoca
llyConstant f ↔ forall x, exists U : Set X, IsOpen U ∧ x in U ∧ forall x' in U, 
f x' = f x
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Module.FinitePresentation.exists_free_localizedModule_powers`：Module.Fin
itePresentation.exists_free_localizedModule_powers (Rₛ) [CommRing Rₛ] [Algebra R
 Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [Nontr…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.localization_isScalarTower_of_submonoid_le`：localization_
isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M <= N) [IsLocalization M
 S] [IsLocalization N T] : @IsScalarTower R S T…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.isLocalization_of_submonoid_le`：isLocalization_of_submono
id_le (M N : Submonoid R) (h : M <= N) [IsLocalization M S] [IsLocalization N T]
 [Algebra S T] [IsScalarTower R S T…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `IsLocalizedModule.of_restrictScalars`：IsLocalizedModule.of_restrictScala
rs (S : Submonoid R) {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Mo
dule A N] [IsScalarTower R…
· 使用定理 `Module.finrank_of_isLocalizedModule_of_free`：Module.finrank_of_isLocaliz
edModule_of_free (Rₛ : Type*) {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Comm
Ring Rₛ] [Algebra R Rₛ] [Module R…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M] :
    IsLocallyConstant (fun x : freeLocus R M ↦ rankAtStalk M x.1) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  refine ⟨Subtype.val ⁻¹' basicOpen f, (basicOpen f).2.preimage continuous_subtype_val, hf, ?_⟩
  rintro ⟨p, hp''⟩ hp
  let p' := Algebra.algebraMapSubmonoid (Localization (.powers f)) p.asIdeal.primeCompl
  have hp' : Submonoid.powers f ≤ p.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl]
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  let : Algebra (Localization.Away f) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p.asIdeal.primeCompl hp'
  have : IsScalarTower R (Localization.Away f) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  let : Module (Localization.Away f) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization.Away f) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
    (Localization.Away f)
  have : IsLocalization p' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
  have : IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R) :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
    ((IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))))
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
  have := Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
  simp [Rₚ, rankAtStalk, this, hf'']
/-
**Module.isLocallyConstant_rankAtStalk** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Flat
 R M] : IsLocallyConstant (rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.freeLocus_eq_univ`：freeLocus_eq_univ [Module.Finite R M] [Module.
Flat R M] : freeLocus R M = Set.univ
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocallyConstant.comp_continuous`：comp_continuous [TopologicalSpace Y] 
{g : Y -> Z} {f : X -> Y} (hg : IsLocallyConstant g) (hf : Continuous f) : IsLoc
allyConstant (g ∘ f)
· 使用引理 `Module.isLocallyConstant_rankAtStalk_freeLocus`：isLocallyConstant_rankAt
Stalk_freeLocus [Module.FinitePresentation R M] : IsLocallyConstant (fun x : fre
eLocus R M => rankAtStalk M x.1)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
lemma isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (rankAtStalk (R := R) M) := by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
  convert! isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

@[simp]
/-
**Module.rankAtStalk_eq_zero_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] : rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.finrank_zero_of_subsingleton`：Module.finrank_zero_of_subsingleton
 [Subsingleton M] : finrank R M = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `LocalizedModule.instSubsingleton`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommRing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsing
leton M] (S : Submonoi…
-/
lemma rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] :
    rankAtStalk (R := R) M = 0 := by
  ext p
  exact Module.finrank_zero_of_subsingleton
/-
**Module.nontrivial_of_rankAtStalk_pos** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：nontrivial_of_rankAtStalk_pos (h : 0 < rankAtStalk (R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_eq_zero_of_subsingleton`：rankAtStalk_eq_zero_of_subsi
ngleton [Subsingleton M] : rankAtStalk (R
-/
lemma nontrivial_of_rankAtStalk_pos (h : 0 < rankAtStalk (R := R) M) :
    Nontrivial M := by
  by_contra! hn
  simp at h
/-
**Module.rankAtStalk_eq_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃
ₗ[R] N) : rankAtStalk (R
参数：e : M ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
-/
lemma rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N := by
  ext p
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) _ e |>.finrank_eq

/-- If `M` is `R`-free, its rank at stalks is constant and agrees with the `R`-rank of `M`. -/
@[simp]
/-
**Module.rankAtStalk_eq_finrank_of_free** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_eq_finrank_of_free [Module.Free R M] : rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.finrank_of_isLocalizedModule_of_free`：Module.finrank_of_isLocaliz
edModule_of_free (Rₛ : Type*) {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Comm
Ring Rₛ] [Algebra R Rₛ] [Module R…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` is `R`-free, its rank at stalks is constant and agrees with the `R`-rank 
of `M`.
-/
lemma rankAtStalk_eq_finrank_of_free [Module.Free R M] :
    rankAtStalk (R := R) M = Module.finrank R M := by
  ext p
  simp [rankAtStalk, finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]
/-
**Module.rankAtStalk_self** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_self [Nontrivial R] : rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_eq_finrank_of_free`：rankAtStalk_eq_finrank_of_free [M
odule.Free R M] : rankAtStalk (R
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rankAtStalk_self [Nontrivial R] : rankAtStalk (R := R) R = 1 := by
  simp

open LocalizedModule Localization

/-- The rank of `Π i, M i` at a prime `p` is the sum of the ranks of `M i` at `p`. -/
/-
**Module.rankAtStalk_pi** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι -> Type*) [forall i, AddCommG
roup (M i)] [forall i, Module R (M i)] [forall i, Module.Flat R (M i)] [forall i
, Module.Finite R (M i)] (p : PrimeSpectrum R) : rankAtStalk (Π i, M i) p = ∑ᶠ i
, rankAtStalk (M i) p
参数：M : ι -> Type*；M i；M i；M i；M i；p : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_pi_fintype`：Module.finrank_pi_fintype {ι : Type v} [Finty
pe ι] {M : ι -> Type w} [forall i : ι, AddCommMonoid (M i)] [forall i : ι, Modul
e R (M i)] [for…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `finsum_eq_sum_of_fintype`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCom
mMonoid M] [inst_1 : Fintype α] (f : α → M), ∑ᶠ (i : α), f i = ∑ i, f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rank of `Π i, M i` at a prime `p` is the sum of the ranks of `M i` at `p`.
-/
lemma rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)]
    [∀ i, Module.Finite R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (Π i, M i) p = ∑ᶠ i, rankAtStalk (M i) p := by
  cases nonempty_fintype ι
  let f : (Π i, M i) →ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    .pi (fun i ↦ mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (mkLinearMap _ _) f |>.extendScalarsOfIsLocalization p.asIdeal.primeCompl _
  have (i : ι) : Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M i)) :=
    free_of_flat_of_isLocalRing
  simp_rw [rankAtStalk, e.finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]
/-
**Module.rankAtStalk_eq_finrank_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 `Module`
。
形式化陈述：rankAtStalk_eq_finrank_tensorProduct (p : PrimeSpectrum R) : rankAtStalk M
 p = finrank (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ot
imes[R] M)
参数：p : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rankAtStalk.eq_1`：∀ {R : Type uR} (M : Type uM) [inst : CommRing 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : PrimeSpectrum R
),   Module.r…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
lemma rankAtStalk_eq_finrank_tensorProduct (p : PrimeSpectrum R) :
    rankAtStalk M p =
      finrank (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) := by
  let e : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  rw [rankAtStalk, e.finrank_eq]

variable [Flat R M] [Module.Finite R M]

attribute [local instance] free_of_flat_of_isLocalRing
/-
**Module.rankAtStalk_eq_zero_iff_notMem_support** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e`。
形式化陈述：rankAtStalk_eq_zero_iff_notMem_support (p : PrimeSpectrum R) : rankAtStalk
 M p = 0 ↔ p ∉ support R M
参数：p : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.notMem_support_iff`：Module.notMem_support_iff : p ∉ Module.suppor
t R M ↔ Subsingleton (LocalizedModule p.asIdeal.primeCompl M)
· 使用引理 `Module.subsingleton_of_rank_zero`：subsingleton_of_rank_zero (h : Module.
rank R M = 0) : Subsingleton M
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.finrank_zero_of_subsingleton`：Module.finrank_zero_of_subsingleton
 [Subsingleton M] : finrank R M = 0
-/
lemma rankAtStalk_eq_zero_iff_notMem_support (p : PrimeSpectrum R) :
    rankAtStalk M p = 0 ↔ p ∉ support R M := by
  rw [notMem_support_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ Module.finrank_zero_of_subsingleton⟩
  apply subsingleton_of_rank_zero (R := Localization.AtPrime p.asIdeal)
  dsimp [rankAtStalk] at h
  simp [← finrank_eq_rank, h]
/-
**Module.rankAtStalk_pos_iff_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_pos_iff_mem_support (p : PrimeSpectrum R) : 0 < rankAtStalk M 
p ↔ p in support R M
参数：p : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `Module.rankAtStalk_eq_zero_iff_notMem_support`：rankAtStalk_eq_zero_iff_n
otMem_support (p : PrimeSpectrum R) : rankAtStalk M p = 0 ↔ p ∉ support R M
-/
lemma rankAtStalk_pos_iff_mem_support (p : PrimeSpectrum R) :
    0 < rankAtStalk M p ↔ p ∈ support R M :=
  Nat.pos_iff_ne_zero.trans (rankAtStalk_eq_zero_iff_notMem_support _).not_left
/-
**Module.rankAtStalk_eq_zero_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Module`
。
形式化陈述：rankAtStalk_eq_zero_iff_subsingleton : rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.support_eq_empty_iff`：Module.support_eq_empty_iff : Module.suppor
t R M = ∅ ↔ Subsingleton M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_eq_zero_iff_notMem_support`：rankAtStalk_eq_zero_iff_n
otMem_support (p : PrimeSpectrum R) : rankAtStalk M p = 0 ↔ p ∉ support R M
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用引理 `Module.rankAtStalk_eq_zero_of_subsingleton`：rankAtStalk_eq_zero_of_subsi
ngleton [Subsingleton M] : rankAtStalk (R
-/
lemma rankAtStalk_eq_zero_iff_subsingleton :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  rw [← rankAtStalk_eq_zero_iff_notMem_support, h, Pi.zero_apply]

variable (M) in
/-- The rank of `M × N` at `p` is equal to the sum of the ranks. -/
/-
**Module.rankAtStalk_prod** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_prod (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R 
N] [Module.Finite R N] : rankAtStalk (R
参数：N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_prod`：Module.finrank_prod [Module.Finite R M] [Module.Fin
ite R M'] : finrank R (M × M') = finrank R M + finrank R M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rank of `M × N` at `p` is equal to the sum of the ranks.
-/
lemma rankAtStalk_prod (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R N] [Module.Finite R N] :
    rankAtStalk (R := R) (M × N) = rankAtStalk M + rankAtStalk N := by
  ext p
  let e : LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
      (.prodMap (mkLinearMap _ M) (mkLinearMap _ N)) |>.extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  simp [rankAtStalk, e.finrank_eq]
/-
**Module.rankAtStalk_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_baseChange {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSp
ectrum S) : rankAtStalk (S otimes[R] M) p = rankAtStalk M (p.comap (algebraMap R
 S))
参数：p : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.instLiesOverAsIdealComapAlgebraMap`：∀ {R : Type u} {S : Ty
pe v} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]  
 (p : PrimeSpectrum S), p.asIdeal.Lies…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rankAtStalk.eq_1`：∀ {R : Type uR} (M : Type uM) [inst : CommRing 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : PrimeSpectrum R
),   Module.r…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_baseChange`：Module.finrank_baseChange : finrank R (R otim
es[S] M') = finrank S M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
-/
lemma rankAtStalk_baseChange {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum S) :
    rankAtStalk (S ⊗[R] M) p = rankAtStalk M (p.comap (algebraMap R S)) := by
  let q : PrimeSpectrum R := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  let e : LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime q.asIdeal]
        LocalizedModule q.asIdeal.primeCompl M :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R S _ _ M) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ M).symm)
  rw [rankAtStalk, e.finrank_eq]
  apply Module.finrank_baseChange
/-
**Module.rankAtStalk_isBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_isBaseChange {S Mₛ : Type*} [CommRing S] [Algebra R S] [AddCom
mGroup Mₛ] [Module R Mₛ] [Module S Mₛ] [IsScalarTower R S Mₛ] {f : M ->ₗ[R] Mₛ} 
(hf : IsBaseChange S f) (p : PrimeSpectrum S) : rankAtStalk Mₛ p = rankAtStalk M
 (p.comap (algebraMap R S))
参数：hf : IsBaseChange S f；p : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Module.rankAtStalk_eq_of_equiv`：rankAtStalk_eq_of_equiv {N : Type*} [Add
CommGroup N] [Module R N] (e : M ≃ₗ[R] N) : rankAtStalk (R
· 使用引理 `Module.rankAtStalk_baseChange`：rankAtStalk_baseChange {S : Type*} [CommR
ing S] [Algebra R S] (p : PrimeSpectrum S) : rankAtStalk (S otimes[R] M) p = ran
kAtStalk M (p.comap…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rankAtStalk_isBaseChange {S Mₛ : Type*} [CommRing S] [Algebra R S] [AddCommGroup Mₛ]
    [Module R Mₛ] [Module S Mₛ] [IsScalarTower R S Mₛ] {f : M →ₗ[R] Mₛ} (hf : IsBaseChange S f)
    (p : PrimeSpectrum S) : rankAtStalk Mₛ p = rankAtStalk M (p.comap (algebraMap R S)) := by
  simp [rankAtStalk_eq_of_equiv hf.equiv.symm, rankAtStalk_baseChange]

variable (M) in
/-
**Module.rankAtStalk_eq_of_le_of_finite_of_flat** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e`。
形式化陈述：rankAtStalk_eq_of_le_of_finite_of_flat {p q : PrimeSpectrum R} (hpq : p <=
 q) : rankAtStalk M p = rankAtStalk M q
参数：hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.localization_comap_range`：localization_comap_range [Algebr
a R S] (M : Submonoid R) [IsLocalization M S] : Set.range (comap (algebraMap R S
)) = { p | Disjoint (M : Set…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_compl_left_iff`：disjoint_compl_left_iff : Disjoint xᶜ y ↔ y <= 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.rankAtStalk_isBaseChange`：rankAtStalk_isBaseChange {S Mₛ : Type*}
 [CommRing S] [Algebra R S] [AddCommGroup Mₛ] [Module R Mₛ] [Module S Mₛ] [IsSca
larTower R S Mₛ] {f :…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用引理 `LocalizedModule.isBaseChange`：LocalizedModule.isBaseChange : IsBaseChang
e (Localization S) (LocalizedModule.mkLinearMap S M)
· 使用引理 `Module.rankAtStalk_eq_finrank_of_free`：rankAtStalk_eq_finrank_of_free [M
odule.Free R M] : rankAtStalk (R
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rankAtStalk_eq_of_le_of_finite_of_flat {p q : PrimeSpectrum R} (hpq : p ≤ q) :
    rankAtStalk M p = rankAtStalk M q := by
  let S := Localization.AtPrime q.asIdeal
  obtain ⟨P, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
    exact disjoint_compl_left_iff.mpr hpq
  rw [← rankAtStalk_isBaseChange (LocalizedModule.isBaseChange q.asIdeal.primeCompl M),
    rankAtStalk_eq_finrank_of_free]
  simp [rankAtStalk]

variable (M) in
/-
**Module.rankAtStalk_eq_of_le_of_finite_of_flat'** 是 Mathlib 中的一个引理，位于命名空间 `Modu
le`。
形式化陈述：rankAtStalk_eq_of_le_of_finite_of_flat' {p q : Ideal R} [hp : p.IsPrime] [
hq : q.IsPrime] (hpq : p <= q) : rankAtStalk M ⟨p, hp⟩ = rankAtStalk M ⟨q, hq⟩
参数：hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.rankAtStalk_eq_of_le_of_finite_of_flat`：rankAtStalk_eq_of_le_of_f
inite_of_flat {p q : PrimeSpectrum R} (hpq : p <= q) : rankAtStalk M p = rankAtS
talk M q
-/
lemma rankAtStalk_eq_of_le_of_finite_of_flat' {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime]
    (hpq : p ≤ q) : rankAtStalk M ⟨p, hp⟩ = rankAtStalk M ⟨q, hq⟩ :=
  rankAtStalk_eq_of_le_of_finite_of_flat M hpq

/-- See `rankAtStalk_tensorProduct_of_isScalarTower` for a hetero-basic version. -/
/-
**Module.rankAtStalk_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_tensorProduct (N : Type*) [AddCommGroup N] [Module R N] [Modul
e.Finite R N] [Module.Flat R N] : rankAtStalk (M otimes[R] N) = rankAtStalk M * 
rankAtStalk (R
参数：N : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_eq_finrank_tensorProduct`：rankAtStalk_eq_finrank_tens
orProduct (p : PrimeSpectrum R) : rankAtStalk M p = finrank (Localization.AtPrim
e p.asIdeal) (Localization.AtPrim…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_tensorProduct`：Module.finrank_tensorProduct : finrank R (
M otimes[S] M') = finrank R M * finrank S M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i

--- 原说明 ---
See `rankAtStalk_tensorProduct_of_isScalarTower` for a hetero-basic version.
-/
lemma rankAtStalk_tensorProduct (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Flat R N] : rankAtStalk (M ⊗[R] N) = rankAtStalk M * rankAtStalk (R := R) N := by
  ext p
  let e : Localization.AtPrime p.asIdeal ⊗[R] (M ⊗[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal ⊗[R] M) ⊗[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal ⊗[R] N) :=
    (AlgebraTensorModule.assoc _ _ _ _ _ _).symm ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm
  rw [rankAtStalk_eq_finrank_tensorProduct, e.finrank_eq, finrank_tensorProduct,
    ← rankAtStalk_eq_finrank_tensorProduct, ← rankAtStalk_eq_finrank_tensorProduct, Pi.mul_apply]
/-
**Module.rankAtStalk_tensorProduct_of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 `M
odule`。
形式化陈述：rankAtStalk_tensorProduct_of_isScalarTower {S : Type*} [CommRing S] [Algeb
ra R S] (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R 
S N] [Module.Finite S N] [Module.Flat S N] (p : PrimeSpectrum S) : rankAtStalk (
N otimes[R] M) p = rankAtStalk N p * rankAtStalk M (p.comap (algebraMap R S))
参数：N : Type*；p : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Module.rankAtStalk_eq_of_equiv`：rankAtStalk_eq_of_equiv {N : Type*} [Add
CommGroup N] [Module R N] (e : M ≃ₗ[R] N) : rankAtStalk (R
· 使用引理 `Module.rankAtStalk_tensorProduct`：rankAtStalk_tensorProduct (N : Type*) 
[AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N] : rankAtStal
k (M otimes[R] N) = ra…
· 使用引理 `Module.rankAtStalk_baseChange`：rankAtStalk_baseChange {S : Type*} [CommR
ing S] [Algebra R S] (p : PrimeSpectrum S) : rankAtStalk (S otimes[R] M) p = ran
kAtStalk M (p.comap…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rankAtStalk_tensorProduct_of_isScalarTower {S : Type*} [CommRing S] [Algebra R S]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat S N] (p : PrimeSpectrum S) :
    rankAtStalk (N ⊗[R] M) p = rankAtStalk N p * rankAtStalk M (p.comap (algebraMap R S)) := by
  simp [rankAtStalk_eq_of_equiv (AlgebraTensorModule.cancelBaseChange R S S N M).symm,
    rankAtStalk_tensorProduct, rankAtStalk_baseChange]

/-- The rank of a module `M` at a prime `p` is equal to the dimension
of `κ(p) ⊗[R] M` as a `κ(p)`-module. -/
/-
**Module.rankAtStalk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rankAtStalk_eq (p : PrimeSpectrum R) : rankAtStalk M p = finrank p.asIdeal
.ResidueField (p.asIdeal.Fiber M)
参数：p : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_baseChange`：Module.finrank_baseChange : finrank R (R otim
es[S] M') = finrank S M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用引理 `Module.rankAtStalk_eq_finrank_tensorProduct`：rankAtStalk_eq_finrank_tens
orProduct (p : PrimeSpectrum R) : rankAtStalk M p = finrank (Localization.AtPrim
e p.asIdeal) (Localization.AtPrim…

--- 原说明 ---
The rank of a module `M` at a prime `p` is equal to the dimension
of `κ(p) ⊗[R] M` as a `κ(p)`-module.
-/
lemma rankAtStalk_eq (p : PrimeSpectrum R) :
    rankAtStalk M p = finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  let k := p.asIdeal.ResidueField
  let e : k ⊗[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal ⊗[R] M) ≃ₗ[k]
      k ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [← e.finrank_eq, finrank_baseChange, rankAtStalk_eq_finrank_tensorProduct]

/-- Variant of `Module.rankAtStalk_eq` for better rewriting. -/
/-
**Module._root_.Ideal.finrank_fiber_eq_rankAtStalk** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `Module.rankAtStalk_eq` for better rewriting.
-/
lemma _root_.Ideal.finrank_fiber_eq_rankAtStalk (p : Ideal R) [hp : p.IsPrime] :
    finrank p.ResidueField (p.Fiber M) = rankAtStalk M ⟨p, hp⟩ :=
  (rankAtStalk_eq ⟨p, hp⟩).symm
/-
**Module._root_.Ideal.finrank_fiber_eq_finrank** 是 Mathlib 中的一个引理，位于命名空间 `Module
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Ideal.finrank_fiber_eq_finrank [IsDomain R] (p : Ideal R) [p.IsPrime] :
    finrank p.ResidueField (p.Fiber M) = finrank R M := by
  let K := FractionRing R
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  rw [p.finrank_fiber_eq_rankAtStalk, rankAtStalk, ← (isBaseChange Rp Mp K).finrank_eq,
    (((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp K Mp _)).finrank_eq,
    (AlgebraTensorModule.cancelBaseChange R Rp K K M).finrank_eq, (isBaseChange R M K).finrank_eq]

end Module

