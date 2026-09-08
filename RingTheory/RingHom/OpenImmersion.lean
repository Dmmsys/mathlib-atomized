/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic

/-! # Standard Open Immersion

We define the property `RingHom.IsStandardOpenImmersion` on ring homomorphisms: it means that the
morphism is a localization map away from some element. We also define the equivalent
`Algebra.IsStandardOpenImmersion`.
-/

@[expose] public section

universe u

namespace Algebra

open IsLocalization Away

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  [Algebra R S] [Algebra R T]

/-- A standard open immersion is one that is a localization map away from some element. -/
/-
**Algebra.IsStandardOpenImmersion** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_4) → (S : Type u_5) → [inst : CommSemiring R] → [inst_1 : Comm
Semiring S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A standard open immersion is one that is a localization map away from some eleme
nt.
-/
@[mk_iff] class IsStandardOpenImmersion (R S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] : Prop where
  exists_away (R S) : ∃ r : R, IsLocalization.Away r S

namespace IsStandardOpenImmersion

/-
**Algebra.IsStandardOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsStandard
OpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : R) : IsStandardOpenImmersion R (Localization.Away r) :=
  ⟨r, inferInstance⟩

variable (R S T) in
/-
**Algebra.IsStandardOpenImmersion.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsSta
ndardOpenImmersion`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3) [inst : CommSemiring R] [in
st_1 : CommSemiring S]   [inst_2 : CommSemiring T] [inst_3 : Algebra R S] [inst_
4 : Algebra R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   [Algebra.IsStand
ardOpenImmersion R S] [Algebra.IsStandardOpenImmersion S T], Algebra.IsStandardO
penImmersion R T
参数：R : Type u_1；S : Type u_2；T : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardOpenImmersion.exists_away`：∀ (R : Type u_4) (S : Type 
u_5) {inst : CommSemiring R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S}   
[self : Algebra.IsStandardOpenImm…
· 使用引理 `IsLocalization.Away.of_associated`：of_associated {r r' : R} (h : Associa
ted r r') [IsLocalization.Away r S] : IsLocalization.Away r' S
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `IsLocalization.Away.associated_sec_fst`：associated_sec_fst (s : S) : Ass
ociated (algebraMap R S (IsLocalization.Away.sec x s).1) s
· 使用引理 `IsLocalization.Away.mul'`：mul' (T : Type*) [CommSemiring T] [Algebra S T
] [Algebra R T] [IsScalarTower R S T] (x y : R) [IsLocalization.Away x S] [IsLoc
alization.Away…
-/
@[trans] theorem trans [Algebra S T] [IsScalarTower R S T]
    [IsStandardOpenImmersion R S] [IsStandardOpenImmersion S T] :
    IsStandardOpenImmersion R T :=
  let ⟨r, _⟩ := exists_away R S
  let ⟨s, _⟩ := exists_away S T
  have : Away (algebraMap R S (sec r s).1) T :=
    .of_associated (associated_sec_fst r s).symm
  ⟨r * (sec r s).1, mul' S T r _⟩

open _root_.TensorProduct in
/-
**Algebra.IsStandardOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsStandard
OpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStandardOpenImmersion R T] : IsStandardOpenImmersion S (S ⊗[R] T) :=
  let ⟨r, _⟩ := exists_away R T
  ⟨algebraMap R S r, inferInstance⟩
/-
**Algebra.IsStandardOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsStandard
OpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStandardOpenImmersion R R :=
  ⟨1, IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id⟩
/-
**Algebra.IsStandardOpenImmersion.of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.IsStandardOpenImmersion`。
形式化陈述：of_bijective (h : Function.Bijective (algebraMap R S)) : IsStandardOpenImm
ersion R S
参数：h : Function.Bijective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.isStandardOpenImmersion_iff`：∀ (R : Type u_4) (S : Type u_5) [in
st : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   Algebra
.IsStandardOpenImmersion …
· 使用定理 `IsLocalization.away_of_isUnit_of_bijective`：away_of_isUnit_of_bijective 
{R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] {r : R} 
(hr : IsUnit r) (H : Function.Bi…
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
lemma of_bijective (h : Function.Bijective (algebraMap R S)) :
    IsStandardOpenImmersion R S := by
  rw [Algebra.isStandardOpenImmersion_iff]
  use 1
  apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one h
/-
**Algebra.IsStandardOpenImmersion.of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.IsStandardOpenImmersion`。
形式化陈述：of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T] (e : S ≃ₐ[R] T) [h 
: IsStandardOpenImmersion R S] : IsStandardOpenImmersion R T
参数：e : S ≃ₐ[R] T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.isStandardOpenImmersion_iff`：∀ (R : Type u_4) (S : Type u_5) [in
st : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   Algebra
.IsStandardOpenImmersion …
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
-/
lemma of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T] (e : S ≃ₐ[R] T)
    [h : IsStandardOpenImmersion R S] :
    IsStandardOpenImmersion R T := by
  rw [Algebra.isStandardOpenImmersion_iff] at *
  obtain ⟨r, hr⟩ := h
  use r
  exact IsLocalization.isLocalization_of_algEquiv _ e
/-
**Algebra.IsStandardOpenImmersion.iff_of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.IsStandardOpenImmersion`。
形式化陈述：iff_of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T] (e : S ≃ₐ[R] T)
 : IsStandardOpenImmersion R S ↔ IsStandardOpenImmersion R T
参数：e : S ≃ₐ[R] T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsStandardOpenImmersion.of_algEquiv`：of_algEquiv {T : Type*} [Co
mmSemiring T] [Algebra R T] (e : S ≃ₐ[R] T) [h : IsStandardOpenImmersion R S] : 
IsStandardOpenImmersion R T
-/
lemma iff_of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T]
    (e : S ≃ₐ[R] T) :
    IsStandardOpenImmersion R S ↔ IsStandardOpenImmersion R T :=
  ⟨fun _ ↦ .of_algEquiv e, fun _ ↦ .of_algEquiv e.symm⟩

variable (R S) in
/-
**Algebra.IsStandardOpenImmersion.of_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.IsStandardOpenImmersion`。
形式化陈述：of_isPushout (R' S' : Type*) [CommSemiring R'] [CommSemiring S'] [Algebra 
R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsS
calarTower R S S'] [IsPushout R S R' S'] [IsStandardOpenImmersion R S] : IsStand
ardOpenImmersion R' S'
参数：R' S' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsPushout.comm`：Algebra.IsPushout.comm : Algebra.IsPushout R S R
' S' ↔ Algebra.IsPushout R R' S S'
· 使用引理 `Algebra.IsStandardOpenImmersion.of_algEquiv`：of_algEquiv {T : Type*} [Co
mmSemiring T] [Algebra R T] (e : S ≃ₐ[R] T) [h : IsStandardOpenImmersion R S] : 
IsStandardOpenImmersion R T
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardOpenImmersion.instTensorProduct`：∀ {R : Type u_1} {S :
 Type u_2} {T : Type u_3} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [i
nst_2 : CommSemiring T] [inst_3 : Algeb…
-/
lemma of_isPushout (R' S' : Type*) [CommSemiring R'] [CommSemiring S']
    [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [IsPushout R S R' S'] [IsStandardOpenImmersion R S] :
    IsStandardOpenImmersion R' S' :=
  have : IsPushout R R' S S' := by rwa [IsPushout.comm]
  .of_algEquiv (IsPushout.equiv R _ S _)

end Algebra.IsStandardOpenImmersion

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- A standard open immersion is one that is a localization map away from some element. -/
@[algebraize RingHom.IsStandardOpenImmersion.toAlgebra]
/-
**RingHom.IsStandardOpenImmersion** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → [inst : CommRing R] → [inst_1 : CommRing
 S] → (R →+* S) → Prop
参数：R →+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A standard open immersion is one that is a localization map away from some eleme
nt.
-/
def IsStandardOpenImmersion : Prop :=
  letI := f.toAlgebra
  Algebra.IsStandardOpenImmersion R S
/-
**RingHom.isStandardOpenImmersion_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`
。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S],   (algebraMap R S).IsStandardOpenImmersion ↔ Algebra.IsS
tandardOpenImmersion R S
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.IsStandardOpenImmersion.eq_1`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] (f : R →+* S),   f.IsStandardOpenImmersi
on = Algebra.IsStandardOpe…
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isStandardOpenImmersion_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardOpenImmersion ↔ Algebra.IsStandardOpenImmersion R S := by
  rw [IsStandardOpenImmersion, toAlgebra_algebraMap]

namespace IsStandardOpenImmersion

/-
**RingHom.IsStandardOpenImmersion.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.
IsStandardOpenImmersion`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (r : R)   [IsLocalization.Away r S], (algebraMap R S).IsS
tandardOpenImmersion
参数：r : R；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.isStandardOpenImmersion_algebraMap`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S],   (algebra
Map R S).IsStandardOpenImmersion…
-/
protected lemma algebraMap [Algebra R S] (r : R) [IsLocalization.Away r S] :
    (algebraMap R S).IsStandardOpenImmersion :=
  isStandardOpenImmersion_algebraMap.2 ⟨r, inferInstance⟩
/-
**RingHom.IsStandardOpenImmersion.toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.I
sStandardOpenImmersion`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S},   f.IsStandardOpenImmersion → Algebra.IsStandardOpenImmersion R S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgebra {f : R →+* S} (hf : f.IsStandardOpenImmersion) :
    @Algebra.IsStandardOpenImmersion R S _ _ f.toAlgebra :=
  letI := f.toAlgebra; hf

/-- A bijective ring map is a standard open immersion. -/
/-
**RingHom.IsStandardOpenImmersion.of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m.IsStandardOpenImmersion`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S},   Function.Bijective ⇑f → f.IsStandardOpenImmersion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.away_of_isUnit_of_bijective`：away_of_isUnit_of_bijective 
{R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] {r : R} 
(hr : IsUnit r) (H : Function.Bi…
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)

--- 原说明 ---
A bijective ring map is a standard open immersion.
-/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.IsStandardOpenImmersion :=
  letI := f.toAlgebra
  ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hf⟩

variable (R) in
/-- The identity map of a ring is a standard open immersion. -/
/-
**RingHom.IsStandardOpenImmersion.id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStanda
rdOpenImmersion`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R], (RingHom.id R).IsStandardOpenImmersi
on
参数：R : Type u_1；RingHom.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardOpenImmersion.of_bijective`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   Function.Biject
ive ⇑f → f.IsStandardOpenImmersion
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)

--- 原说明 ---
The identity map of a ring is a standard open immersion.
-/
lemma id : (RingHom.id R).IsStandardOpenImmersion :=
  of_bijective Function.bijective_id

variable {f g} in
/-- The composition of two standard open immersions is a standard open immersion. -/
/-
**RingHom.IsStandardOpenImmersion.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStan
dardOpenImmersion`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   {f : R →+* S} {g : S →+* T},   f.IsStanda
rdOpenImmersion → g.IsStandardOpenImmersion → (g.comp f).IsStandardOpenImmersion
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.IsStandardOpenImmersion.trans`：∀ (R : Type u_1) (S : Type u_2) (
T : Type u_3) [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Comm
Semiring T] [inst_3 : Algeb…
· 使用定理 `RingHom.IsStandardOpenImmersion.toAlgebra`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.IsStandardOpenIm
mersion → Algebra.IsStandardOpe…

--- 原说明 ---
The composition of two standard open immersions is a standard open immersion.
-/
lemma comp (hf : f.IsStandardOpenImmersion) (hg : g.IsStandardOpenImmersion) :
    (g.comp f).IsStandardOpenImmersion := by
  algebraize [f, g, g.comp f]
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  exact .trans _ S _
/-
**RingHom.IsStandardOpenImmersion.containsIdentities** 是 Mathlib 中的一个定理，位于命名空间 `
RingHom.IsStandardOpenImmersion`。
形式化陈述：RingHom.ContainsIdentities fun {R S} [CommRing R] [CommRing S] => RingHom.
IsStandardOpenImmersion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardOpenImmersion.id`：∀ (R : Type u_1) [inst : CommRing R]
, (RingHom.id R).IsStandardOpenImmersion
-/
theorem containsIdentities : ContainsIdentities.{u} IsStandardOpenImmersion := id
/-
**RingHom.IsStandardOpenImmersion.stableUnderComposition** 是 Mathlib 中的一个定理，位于命名
空间 `RingHom.IsStandardOpenImmersion`。
形式化陈述：RingHom.StableUnderComposition fun {R S} [CommRing R] [CommRing S] => Ring
Hom.IsStandardOpenImmersion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardOpenImmersion.comp`：∀ {R : Type u_1} {S : Type u_2} {T
 : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   {
f : R →+* S} {g : S →+* T}…
-/
theorem stableUnderComposition : StableUnderComposition.{u} IsStandardOpenImmersion := @comp
/-
**RingHom.IsStandardOpenImmersion.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
.IsStandardOpenImmersion`。
形式化陈述：RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => RingHom.IsStand
ardOpenImmersion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用定理 `RingHom.IsStandardOpenImmersion.stableUnderComposition`：RingHom.StableUn
derComposition fun {R S} [CommRing R] [CommRing S] => RingHom.IsStandardOpenImme
rsion
· 使用定理 `RingHom.IsStandardOpenImmersion.of_bijective`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   Function.Biject
ive ⇑f → f.IsStandardOpenImmersion
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
theorem respectsIso : RespectsIso.{u} IsStandardOpenImmersion :=
  stableUnderComposition.respectsIso fun e ↦ of_bijective e.bijective
/-
**RingHom.IsStandardOpenImmersion.isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命
名空间 `RingHom.IsStandardOpenImmersion`。
形式化陈述：RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] => Rin
gHom.IsStandardOpenImmersion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.IsStandardOpenImmersion.respectsIso`：RingHom.RespectsIso fun {R 
S} [CommRing R] [CommRing S] => RingHom.IsStandardOpenImmersion
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.isStandardOpenImmersion_algebraMap`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S],   (algebra
Map R S).IsStandardOpenImmersion…
· 使用定理 `Algebra.IsStandardOpenImmersion.instTensorProduct`：∀ {R : Type u_1} {S :
 Type u_2} {T : Type u_3} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [i
nst_2 : CommSemiring T] [inst_3 : Algeb…
-/
theorem isStableUnderBaseChange : IsStableUnderBaseChange.{u} IsStandardOpenImmersion := by
  refine .mk respectsIso ?_
  introv h
  rw [isStandardOpenImmersion_algebraMap] at h ⊢
  infer_instance
/-
**RingHom.IsStandardOpenImmersion.holdsForLocalizationAway** 是 Mathlib 中的一个定理，位于
命名空间 `RingHom.IsStandardOpenImmersion`。
形式化陈述：RingHom.HoldsForLocalizationAway fun {R S} [CommRing R] [CommRing S] => Ri
ngHom.IsStandardOpenImmersion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardOpenImmersion.algebraMap`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (r : R)   [
IsLocalization.Away r S], (algeb…
-/
theorem holdsForLocalizationAway : HoldsForLocalizationAway.{u} IsStandardOpenImmersion := by
  introv R h
  exact .algebraMap r

end IsStandardOpenImmersion

end RingHom

