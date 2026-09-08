/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu, Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The fiber of a ring homomorphism at a prime ideal

## Main results

* `Ideal.Fiber`: `p.Fiber S` is the fiber of a prime `p` of `R` in an `R`-algebra `S`,
  defined to be `κ(p) ⊗ S`.
* `PrimeSpectrum.preimageHomeomorphFiber` : We show that there is a homeomorphism between the
  fiber of the induced map `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal `p` and
  the prime spectrum of `p.Fiber S`.
-/

@[expose] public section

open Algebra TensorProduct nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (ResidueField R ⊗[R] S) :=
  let eSp : ResidueField R ⊗[R] S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.comm _ _ _).trans
      ((TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
  have : Nontrivial (IsLocalRing.ResidueField R ⊗[R] S) := by
    rw [eSp.nontrivial_congr, Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).lt_top).ne
  .of_surjective' TensorProduct.includeRight.toRingHom
    (TensorProduct.mk_surjective _ _ _ residue_surjective)

namespace Ideal

/-
**Ideal.ResidueField.exists_smul_eq_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Re
sidueField`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : p.IsPrime] (x : TensorProduct R
 S p.ResidueField), ∃ r ∉ p, ∃ s, r • x = s ⊗ₜ[R] 1
参数：p : Ideal R；x : TensorProduct R S p.ResidueField。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.SurjectiveOnStalks.exists_mul_eq_tmul`：∀ {R : Type u_1} [inst : 
CommRing R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRi
ng T]   [inst_3 : Algebra R T] [ins…
· 使用引理 `Ideal.surjectiveOnStalks_residueField`：Ideal.surjectiveOnStalks_residueF
ield (I : Ideal R) [I.IsPrime] : (algebraMap R I.ResidueField).SurjectiveOnStalk
s
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Algebra.TensorProduct.includeRight_apply`：includeRight_apply (b : B) : (
includeRight : B ->ₐ[R] A otimes[R] B) b = 1 otimesₜ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
（共 33 条，此处仅展示前 30 条）
-/
lemma ResidueField.exists_smul_eq_tmul_one
    (x : S ⊗[R] p.ResidueField) : ∃ r ∉ p, ∃ s, r • x = s ⊗ₜ[R] 1 := by
  obtain ⟨t, r, a, hrt, e⟩ := RingHom.SurjectiveOnStalks.exists_mul_eq_tmul
    p.surjectiveOnStalks_residueField x ⊥ isPrime_bot
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl t
  simp only [smul_def, Submodule.mem_bot, mul_eq_zero, algebraMap_residueField_eq_zero,
    IsLocalRing.residue_eq_zero_iff, not_or, IsLocalization.AtPrime.mk'_mem_maximal_iff] at hrt
  refine ⟨r * y, p.primeCompl.mul_mem hrt.1 hrt.2, y • a, ?_⟩
  rw [Algebra.smul_def, ← Algebra.TensorProduct.includeRight.commutes, smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.includeRight_apply]
  simpa [← tmul_smul, Submonoid.smul_def, ← smul_mul_assoc, smul_comm _ r,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← algebraMap.coe_smul,
    ← IsScalarTower.algebraMap_apply] using congr(t • $e)

/-- The fiber of a prime `p` of `R` in an `R`-algebra `S`, defined to be `κ(p) ⊗ S`.

See `PrimeSpectrum.preimageHomeomorphFiber` for the homeomorphism between the spectrum of it
and the actual set-theoretic fiber of `PrimeSpectrum S → PrimeSpectrum R` at `p`. -/
/-
**Ideal.Fiber** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal`。
形式化陈述：Fiber (p : Ideal R) [p.IsPrime] (S : Type*) [AddCommGroup S] [Module R S] 
: Type _
参数：p : Ideal R；S : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of a prime `p` of `R` in an `R`-algebra `S`, defined to be `κ(p) ⊗ S`.

See `PrimeSpectrum.preimageHomeomorphFiber` for the homeomorphism between the sp
ectrum of it
and the actual set-theoretic fiber of `PrimeSpectrum S → PrimeSpectrum R` at `p`
.
-/
abbrev Fiber (p : Ideal R) [p.IsPrime] (S : Type*) [AddCommGroup S] [Module R S] : Type _ :=
  p.ResidueField ⊗[R] S
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (q : Ideal (p.Fiber S)) [q.IsPrime] : q.LiesOver p :=
  .trans _ (⊥ : Ideal p.ResidueField) _

/-- If `q` is a prime ideal of `p.Fiber S`,  then the localization `(p.Fiber S)_q` is an algebra
over the localization `R_p` since `p.Fiber S` is already an `R_p`-algebra. This `R_p`-algebra
/-
**Ideal.on** 是 Mathlib 中的一个结构，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `(p.Fiber S)_q` agrees with the one coming from the fact that `q` lies over `p`. -/
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q` is a prime ideal of `p.Fiber S`,  then the localization `(p.Fiber S)_q` i
s an algebra
over the localization `R_p` since `p.Fiber S` is already an `R_p`-algebra. This 
`R_p`-algebra
structure on `(p.Fiber S)_q` agrees with the one coming from the fact that `q` l
ies over `p`.
-/
instance (q : Ideal (p.Fiber S)) [q.IsPrime] : Localization.AtPrime.IsLiesOverAlgebra p q where
  algebraMap_eq := (Localization.localRingHom_unique p q _ (Ideal.over_def q p) fun _ ↦ rfl).symm
/-
**Ideal.Fiber.exists_smul_eq_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Fiber`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : p.IsPrime] (x : p.Fiber S), ∃ r
 ∉ p, ∃ s, r • x = 1 ⊗ₜ[R] s
参数：p : Ideal R；x : p.Fiber S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ResidueField.exists_smul_eq_tmul_one`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal 
R)   [inst_3 : p.IsPrime] (x : T…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
-/
lemma Fiber.exists_smul_eq_one_tmul (x : p.Fiber S) : ∃ r ∉ p, ∃ s, r • x = 1 ⊗ₜ[R] s := by
  obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one _
    (Algebra.TensorProduct.comm _ _ _ x)
  refine ⟨r, hr, s, by simpa using congr((Algebra.TensorProduct.comm _ _ _).symm $e)⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`. -/
/-
**Ideal.Fiber.algEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Fiber`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           (p : Ideal R) →    
         [inst_3 : p.IsPrime] →               p.Fiber S ≃ₐ[S]                 Lo
calization (Algebra.algebraMapSubmonoid S p.primeCompl) ⧸                   Idea
l.map                     (algebraMap (Localization p.primeCompl) (Localization 
(Algebra.algebraMapSubmonoid S p.primeCompl)))                     (IsLocalRing.
maximalIdeal (Localization p.primeCompl))
参数：p : Ideal R；Algebra.algebraMapSubmonoid S p.primeCompl；algebraMap (Localizati
on p.primeCompl) (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))；IsL
ocalRing.maximalIdeal (Localization p.primeCompl)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`.
-/
noncomputable def Fiber.algEquivQuotient :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    p.Fiber S ≃ₐ[S] Sp ⧸ pSp :=
  (commRight R S p.ResidueField).symm.trans <| (tensorQuotientEquiv S _ S _).trans <|
    { __ := Ideal.quotientEquiv _ _ (Localization.tensorLeftAlgEquiv p.primeCompl S) (by
        rw [← Ideal.map_coe includeRight, Ideal.map_map]
        congr
        ext
        simp [Localization.tensorLeftAlgEquiv_apply_one_tmul p.primeCompl])
      commutes' := by simp }

/-- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`. -/
/-
**Ideal.Fiber.algEquivAux** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`.
-/
noncomputable def Fiber.algEquivAux₁ :
    letI Sp := Localization (algebraMapSubmonoid S p.primeCompl)
    letI pS := p.map (algebraMap R S)
    letI : Algebra S (p.Fiber S) := rightAlgebra
    p.Fiber S ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp) :=
  letI : Algebra S (p.Fiber S) := rightAlgebra
  (Fiber.algEquivQuotient p).trans <| quotientEquivAlgOfEq S <| by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R S, ← map_map]

/-- The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a localization. -/
/-
**Ideal.Fiber.algEquivAux** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a local
ization.
-/
noncomputable def Fiber.algEquivAux₂ (q : Ideal (p.Fiber S)) [q.IsPrime] :
    letI r := q.comap includeRight
    letI Sr := Localization.AtPrime r
    letI pS := p.map (algebraMap R S)
    Localization.AtPrime q ≃ₐ[R] Sr ⧸ pS.map (algebraMap S Sr) :=
  letI : Algebra S (p.Fiber S) := rightAlgebra
  letI Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  letI pS := p.map (algebraMap R S)
  letI SpS := S ⧸ pS
  letI r := q.comap includeRight
  letI Sr := Localization.AtPrime r
  letI e₁ : p.Fiber S ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp) := algEquivAux₁ p
  letI q' : Ideal (Sp ⧸ pS.map (algebraMap S Sp)) := q.comap e₁.symm
  haveI : (q'.under SpS).LiesOver r := under_liesOver_of_liesOver SpS q' (q.under S)
  haveI : algebraMapSubmonoid SpS r.primeCompl = (q'.under SpS).primeCompl :=
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective (q'.under SpS) r Quotient.mk_surjective
  haveI : IsLocalization (algebraMapSubmonoid SpS r.primeCompl) (Localization.AtPrime q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (algebraMapSubmonoid SpS (algebraMapSubmonoid S p.primeCompl)) (Localization.AtPrime q') q'
  haveI := IsScalarTower.to₁₃₄ R S SpS (Localization.AtPrime q')
  haveI := IsScalarTower.to₁₃₄ R S SpS (Sr ⧸ pS.map (algebraMap S Sr))
  ((Localization.localAlgEquiv q' q e₁.symm rfl).symm.restrictScalars R).trans
    ((IsLocalization.algEquiv (algebraMapSubmonoid SpS r.primeCompl) (Localization.AtPrime q')
      (Sr ⧸ pS.map (algebraMap S Sr))).restrictScalars R)

/-- The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a localization. -/
/-
**Ideal.Fiber.localizationAlgEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Fibe
r`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           (p : Ideal R) →    
         [inst_3 : p.IsPrime] →               (q : Ideal (p.Fiber S)) →         
        [inst_4 : q.IsPrime] →                   [inst_5 :                      
 Algebra (Localization.AtPrime p)                         (Localization.AtPrime 
(Ideal.comap Algebra.TensorProduct.includeRight q))] →                     [Loca
lization.AtPrime.IsLiesOverAlgebra p (Ideal.comap Algebra.TensorProduct.includeR
ight q)] →                       Localization.AtPrime q ≃ₐ[Localization.AtPrime 
p]                         Localization.AtPrime (Ideal.comap Algebra.TensorProdu
ct.includeRight q) ⧸                           Ideal.map                        
     (algebraMap R (Localization.AtPrime (Ideal.comap Algebra.TensorProduct.incl
udeRight q))) p
参数：p : Ideal R；q : Ideal (p.Fiber S)；Localization.AtPrime p；Localization.AtPrime
 (Ideal.comap Algebra.TensorProduct.includeRight q)；Ideal.comap Algebra.TensorPr
oduct.includeRight q；Ideal.comap Algebra.TensorProduct.includeRight q；algebraMap
 R (Localization.AtPrime (Ideal.comap Algebra.TensorProduct.includeRight q))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a local
ization.
-/
noncomputable def Fiber.localizationAlgEquivQuotient (q : Ideal (p.Fiber S)) [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime (q.comap includeRight))]
    [Localization.AtPrime.IsLiesOverAlgebra p (q.comap includeRight)] :
    letI r := q.comap includeRight
    letI Sr := Localization.AtPrime r
    Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Sr ⧸ p.map (algebraMap R Sr) :=
  ((algEquivAux₂ p q).extendScalarsOfIsLocalization (Localization.AtPrime p) p.primeCompl).trans
    (quotientEquivAlgOfEq (Localization.AtPrime p) (map_map _ _))

end Ideal

@[deprecated (since := "2026-05-11")] alias Fiber.algEquivQuotient := Ideal.Fiber.algEquivQuotient

set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/-- The fiber `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal
`p : PrimeSpectrum R` is in bijection with the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps]
/-
**PrimeSpectrum.preimageEquivFiber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeSpectrum.preimageEquivFiber (p : PrimeSpectrum R) : comap (algebraMap
 R S) ⁻¹' {p} ≃ PrimeSpectrum (p.asIdeal.Fiber S) where toFun q
参数：p : PrimeSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal
`p : PrimeSpectrum R` is in bijection with the prime spectrum of `κ(p) ⊗[R] S`.
-/
noncomputable def PrimeSpectrum.preimageEquivFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ PrimeSpectrum (p.asIdeal.Fiber S) where
  toFun q := ⟨RingHom.ker (Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId _ _) congr($(q.2.symm).asIdeal))
      (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _).toRingHom, RingHom.ker_isPrime _⟩
  invFun q := ⟨q.comap Algebra.TensorProduct.includeRight.toRingHom, by
    simp only [AlgHom.toRingHom_eq_coe, Set.mem_preimage, ← comap_comp_apply,
      AlgHom.comp_algebraMap_of_tower]
    exact (residueField_comap _).le ⟨q.comap (algebraMap _ _), rfl⟩⟩
  left_inv q := by ext x; simp
  right_inv q := by
    ext x
    obtain ⟨r, hr, s, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ x
    have := @PrimeSpectrum.isPrime -- times out if removed
    rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), iff_comm,
      ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), ← Algebra.smul_def, e]
    · simp
    · rw [← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal]
      convert! hr
      exact (residueField_comap _).le ⟨q.comap (algebraMap _ _), rfl⟩
    · simpa [-Algebra.algebraMap_self, -AlgHom.commutes, -AlgHom.map_algebraMap,
        -Ideal.ResidueField.map_algebraMap]

variable (R S) in
/-- The `OrderIso` between the fiber of `PrimeSpectrum S → PrimeSpectrum R` at a prime
ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
/-
**PrimeSpectrum.preimageOrderIsoFiber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeSpectrum.preimageOrderIsoFiber (p : PrimeSpectrum R) : comap (algebra
Map R S) ⁻¹' {p} ≃o PrimeSpectrum (p.asIdeal.Fiber S) where toEquiv
参数：p : PrimeSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `OrderIso` between the fiber of `PrimeSpectrum S → PrimeSpectrum R` at a pri
me
ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`.
-/
noncomputable def PrimeSpectrum.preimageOrderIsoFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃o PrimeSpectrum (p.asIdeal.Fiber S) where
  toEquiv := preimageEquivFiber R S p
  map_rel_iff' {q₁ q₂} := by
    constructor
    · obtain ⟨q₁, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₁
      obtain ⟨q₂, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₂
      simpa using! Ideal.comap_mono
    · intro H x hx
      obtain ⟨r, hr, s, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ x
      rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), ← Algebra.smul_def, e] at hx ⊢
      · replace hx : s ∈ q₁.1.asIdeal := by simpa using! hx
        simpa using! H hx
      · rw [← q₂.2] at hr; simpa [IsScalarTower.algebraMap_apply R S q₂.1.asIdeal.ResidueField]
      · rw [← q₁.2] at hr; simpa [IsScalarTower.algebraMap_apply R S q₁.1.asIdeal.ResidueField]

variable (R S) in
/-- The `OrderIso` between the set of primes lying over a prime ideal `p : Ideal R`,
and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
/-
**PrimeSpectrum.primesOverOrderIsoFiber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeSpectrum.primesOverOrderIsoFiber (R S : Type*) [CommRing R] [CommRing
 S] [Algebra R S] (p : Ideal R) [p.IsPrime] : p.primesOver S ≃o PrimeSpectrum (p
.Fiber S)
参数：R S : Type*；p : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `OrderIso` between the set of primes lying over a prime ideal `p : Ideal R`,
and the prime spectrum of `κ(p) ⊗[R] S`.
-/
noncomputable def PrimeSpectrum.primesOverOrderIsoFiber (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    p.primesOver S ≃o PrimeSpectrum (p.Fiber S) :=
  .trans ⟨⟨fun q ↦ ⟨⟨q, q.2.1⟩, PrimeSpectrum.ext q.2.2.1.symm⟩,
    fun q ↦ ⟨q.1.asIdeal, ⟨q.1.2, ⟨congr($(q.2).1).symm⟩⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩
    (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p, ‹_›⟩)

/-- The `Homeomorph` between the fiber of `PrimeSpectrum S → PrimeSpectrum R`
at a prime ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
/-
**PrimeSpectrum.preimageHomeomorphFiber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeSpectrum.preimageHomeomorphFiber (R S : Type*) [CommRing R] [CommRing
 S] [Algebra R S] (p : PrimeSpectrum R) : comap (algebraMap R S) ⁻¹' {p} ≃ₜ Prim
eSpectrum (p.asIdeal.Fiber S)
参数：R S : Type*；p : PrimeSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Homeomorph` between the fiber of `PrimeSpectrum S → PrimeSpectrum R`
at a prime ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`.
-/
noncomputable def PrimeSpectrum.preimageHomeomorphFiber (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ₜ PrimeSpectrum (p.asIdeal.Fiber S) := by
  letI H : Topology.IsEmbedding (preimageOrderIsoFiber R S p).symm := by
    refine (Topology.IsEmbedding.of_comp_iff .subtypeVal).mp ?_
    have := PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks _ S _
      (Ideal.surjectiveOnStalks_residueField p.asIdeal)
    exact ((Homeomorph.prodUnique _ _).isEmbedding.comp this).comp
      (homeomorphOfRingEquiv (Algebra.TensorProduct.comm _ _ _).toRingEquiv).isEmbedding
  exact
  { __ := preimageOrderIsoFiber R S p
    continuous_toFun := by
      convert!
        (H.toHomeomorphOfSurjective (preimageOrderIsoFiber R S p).symm.surjective).symm.continuous
      ext1 x
      obtain ⟨x, rfl⟩ := (H.toHomeomorphOfSurjective
        (preimageOrderIsoFiber R S p).symm.surjective).surjective x
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Homeomorph.symm_apply_apply]
      simp
    continuous_invFun := H.continuous }

@[simp]
/-
**PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply (q : PrimeSpectrum (p
.Fiber S)) : (primesOverOrderIsoFiber R S p).symm q = q.1.comap Algebra.TensorPr
oduct.includeRight
参数：q : PrimeSpectrum (p.Fiber S)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply (q : PrimeSpectrum (p.Fiber S)) :
    (primesOverOrderIsoFiber R S p).symm q = q.1.comap Algebra.TensorProduct.includeRight :=
  rfl
