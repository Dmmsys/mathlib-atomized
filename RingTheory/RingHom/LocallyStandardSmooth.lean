/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth is locally standard smooth

In this file we show that a ring homomorphism is smooth if and only if it is locally standard
smooth.
-/

universe u

public section

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}

/-- Any standard smooth ring homomorphism is smooth. -/
/-
**RingHom.IsStandardSmooth.smooth** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStandardS
mooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S}, f.IsStandardSmooth → f.Smooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Smooth.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R]
 [inst_1 : CommRing S] (f : R →+* S), f.Smooth = Algebra.Smooth R S
· 使用定理 `Algebra.instSmoothOfIsStandardSmooth`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.IsStan
dardSmooth R S], Algebra.S…
· 使用定理 `RingHom.IsStandardSmooth.toAlgebra`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.IsStandardSmooth → Algebra.
IsStandardSmooth R S

--- 原说明 ---
Any standard smooth ring homomorphism is smooth.
-/
lemma IsStandardSmooth.smooth {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : IsStandardSmooth f) : Smooth f := by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

/-- Any smooth ring homomorphism is locally standard smooth. -/
/-
**RingHom.Smooth.locally_isStandardSmooth** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Smo
oth`。
形式化陈述：∀ {R S : Type u} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S}, 
  f.Smooth → RingHom.Locally (fun {R S} [CommRing R] [CommRing S] => RingHom.IsS
tandardSmooth) f
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.IsStandardSmooth。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`：∀ (R : Type u_1) (S 
: Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Al
gebra.Smooth R S],   ∃ s, Ideal.span s =…
· 使用定理 `RingHom.Smooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] {f : R →+* S}, f.Smooth → Algebra.Smooth R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `RingHom.isStandardSmooth_algebraMap`：isStandardSmooth_algebraMap [Algebr
a R S] : (algebraMap R S).IsStandardSmooth ↔ Algebra.IsStandardSmooth R S

--- 原说明 ---
Any smooth ring homomorphism is locally standard smooth.
-/
theorem Smooth.locally_isStandardSmooth (hf : f.Smooth) : Locally IsStandardSmooth f := by
  algebraize [f]
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  refine ⟨s, hs, fun t ht ↦ ?_⟩
  dsimp only
  rw [← f.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_eq, isStandardSmooth_algebraMap]
  exact h t ht

/-- A ring homomorphism is smooth if and only if it is locally standard smooth. -/
/-
**RingHom.smooth_iff_locally_isStandardSmooth** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
`。
形式化陈述：smooth_iff_locally_isStandardSmooth : Smooth f ↔ Locally IsStandardSmooth 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Smooth.locally_isStandardSmooth`：∀ {R S : Type u} [inst : CommRi
ng R] [inst_1 : CommRing S] {f : R →+* S},   f.Smooth → RingHom.Locally (fun {R 
S} [CommRing R] [CommRing S] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.locally_iff_of_localizationSpanTarget`：locally_iff_of_localizati
onSpanTarget (hPi : RespectsIso P) (hPs : OfLocalizationSpanTarget P) {R S : Typ
e u} [CommRing R] [CommRing S] (f :…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用引理 `RingHom.Smooth.propertyIsLocal`：propertyIsLocal : PropertyIsLocal Smooth
 where localizationAwayPreserves
· 使用引理 `RingHom.Smooth.ofLocalizationSpanTarget`：ofLocalizationSpanTarget : OfLo
calizationSpanTarget Smooth
· 使用引理 `RingHom.locally_of_locally`：locally_of_locally {Q : forall {R S : Type u
} [CommRing R] [CommRing S], (R ->+* S) -> Prop} (hPQ : forall {R S : Type u} [C
ommRing R] [Comm…
· 使用定理 `RingHom.IsStandardSmooth.smooth`：∀ {R : Type u_1} {S : Type u_2} [inst :
 CommRing R] [inst_1 : CommRing S] {f : R →+* S}, f.IsStandardSmooth → f.Smooth

--- 原说明 ---
A ring homomorphism is smooth if and only if it is locally standard smooth.
-/
theorem smooth_iff_locally_isStandardSmooth : Smooth f ↔ Locally IsStandardSmooth f := by
  refine ⟨fun hf ↦ hf.locally_isStandardSmooth, fun hf ↦ ?_⟩
  rw [← locally_iff_of_localizationSpanTarget Smooth.propertyIsLocal.respectsIso
    Smooth.ofLocalizationSpanTarget]
  exact locally_of_locally (fun hf ↦ hf.smooth) hf

/-- A ring homomorphism is étale if and only if it is standard smooth of relative dimension `0`. -/
/-
**RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero** 是 Mathlib 中的一个引理，
位于命名空间 `RingHom`。
形式化陈述：etale_iff_isStandardSmoothOfRelativeDimension_zero : Etale f ↔ IsStandardS
moothOfRelativeDimension 0 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`：∀ {R : Type 
u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra 
R S],   Algebra.Etale R S ↔ Algebra.IsStandardSm…

--- 原说明 ---
A ring homomorphism is étale if and only if it is standard smooth of relative di
mension `0`.
-/
lemma etale_iff_isStandardSmoothOfRelativeDimension_zero :
    Etale f ↔ IsStandardSmoothOfRelativeDimension 0 f := by
  algebraize [f]
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

end RingHom

