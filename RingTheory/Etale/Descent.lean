/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange

/-!
# Etale descends along faithfully flat ring maps

In this file we show that smooth, unramified and étale algebras descend along faithfully flat
base change.

## Main results

- `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`: Smooth descends.
- `Algebra.Unramified.of_smooth_tensorProduct_of_faithfullyFlat`: Unramified descends.
- `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`: Etale descends.

We also provide the corresponding `RingHom.CodescendsAlong` lemmas.

## TODOs

- The lemma `Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat` has an
  additional `Algebra.FinitePresentation` assumption, because the proof uses that a flat module
  of finite presentation is projective and the former descends. This also holds without
  the finite presentation assumption, but requires showing that projectivity descends
  along faithfully flat base change, which is due to Raynaud and Gruson
  (see https://stacks.math.columbia.edu/tag/058B).
-/

public section

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]

/-
**Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFl
at** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyUnramified`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [Module.FaithfullyFlat R T]   [Algebra.FormallyUnramified T (TensorProduct 
R T S)], Algebra.FormallyUnramified R S
参数：T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`：∀ {R : Type
 v} {A : Type u} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A
}   [self : Algebra.FormallyUnramified R A], Subs…
· 使用引理 `Module.FaithfullyFlat.lTensor_reflects_triviality`：lTensor_reflects_triv
iality [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Subsingle
ton (M otimes[R] N)] : Subsingleton N
-/
lemma FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
    [FormallyUnramified T (T ⊗[R] S)] :
    FormallyUnramified R S := by
  constructor
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T ⊗[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R T S (T ⊗[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

/-- Formally smooth algebras descend along faithfully flat base change. See the TODO
in the module docstring. -/
proof_wanted FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [FormallySmooth T (T ⊗[R] S)] :
    FormallySmooth R S

/-
**Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat** 是 Mathlib 中的一个定理，位于
命名空间 `Algebra.Smooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [Module.FaithfullyFlat R T] [Algebra.Smooth T (TensorProduct R T S)],   Alg
ebra.Smooth R S
参数：T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithf
ullyFlat`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.formallySmooth_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing
 R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallySmooth R A ↔
 Module.Projecti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
· 使用定理 `Algebra.FormallySmooth.projective_kaehlerDifferential`：∀ {R : Type u} {A
 : Type v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [s
elf : Algebra.FormallySmooth R A], Module.P…
· 使用定理 `Module.Flat.of_flat_tensorProduct`：∀ (R : Type u) (M : Type v) [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (S : Type u_1)
   [inst_3 : CommRing S…
· 使用定理 `Module.FaithfullyFlat.instTensorProduct`：∀ (R : Type u) (M : Type v) [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (S : Typ
e u_1)   [inst_3 : CommRing S…
· 使用定理 `Module.Flat.projective_of_finitePresentation`：projective_of_finitePresen
tation [Flat R M] [FinitePresentation R M] : Projective R M
· 使用定理 `Algebra.instFinitePresentationKaehlerDifferentialOfFinitePresentation`：∀
 {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : A
lgebra R S]   [Algebra.FinitePresentation R S], Module.Fini…
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Algebra.FormallySmooth.subsingleton_h1Cotangent`：∀ {R : Type u} {A : Typ
e v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : 
Algebra.FormallySmooth R A], Subsingl…
· 使用引理 `Module.FaithfullyFlat.lTensor_reflects_triviality`：lTensor_reflects_triv
iality [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Subsingle
ton (M otimes[R] N)] : Subsingleton N
-/
lemma Smooth.of_smooth_tensorProduct_of_faithfullyFlat [Smooth T (T ⊗[R] S)] :
    Smooth R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallySmooth_iff]
  constructor
  · let _ : Algebra T (S ⊗[R] T) := TensorProduct.rightAlgebra
    let e : S ⊗[R] T ≃ₐ[T] T ⊗[R] S :=
      .ofRingEquiv (f := TensorProduct.comm R S T) <| by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth T (S ⊗[R] T) := .of_equiv e.symm
    let e' : (S ⊗[R] T) ⊗[S] Ω[S⁄R] ≃ₗ[S ⊗[R] T] Ω[S ⊗[R] T⁄T] :=
      KaehlerDifferential.tensorKaehlerEquiv R T S (S ⊗[R] T)
    have : Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] Ω[S⁄R]) := .of_linearEquiv e'
    have : Module.Flat S Ω[S⁄R] := Module.Flat.of_flat_tensorProduct _ _ (S ⊗[R] T)
    exact Module.Flat.projective_of_finitePresentation
  · have : Subsingleton (T ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R T (H1Cotangent R S)
/-
**Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat** 是 Mathlib 中
的一个定理，位于命名空间 `Algebra.Unramified`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [Module.FaithfullyFlat R T] [Algebra.Unramified T (TensorProduct R T S)],  
 Algebra.Unramified R S
参数：T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithf
ullyFlat`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`：∀ {R :
 Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
-/
lemma Unramified.of_unramified_tensorProduct_of_faithfullyFlat [Unramified T (T ⊗[R] S)] :
    Unramified R S :=
  ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_finiteType_tensorProduct_of_faithfullyFlat T⟩
/-
**Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.Etale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [Module.FaithfullyFlat R T] [Algebra.Etale T (TensorProduct R T S)],   Alge
bra.Etale R S
参数：T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Etale.iff_formallyUnramified_and_smooth`：∀ {R : Type u} {A : Typ
e v} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra
.Etale R A ↔ Algebra.FormallyUnramifi…
· 使用定理 `Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithf
ullyFlat`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`：∀ {R : Type u_
1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R 
S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `Algebra.Etale.instSmooth`：∀ {R : Type u} {A : Type v} [inst : CommRing R
] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebra.Sm
ooth R A
-/
lemma Etale.of_etale_tensorProduct_of_faithfullyFlat [Etale T (T ⊗[R] S)] :
    Etale R S := by
  rw [Etale.iff_formallyUnramified_and_smooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_smooth_tensorProduct_of_faithfullyFlat T⟩

end Algebra

namespace RingHom

/-
**RingHom.Smooth.codescendsAlong_faithfullyFlat** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.Smooth`。
形式化陈述：RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.Sm
ooth) fun {R S} [CommRing R] [CommRing S] =>   RingHom.FaithfullyFlat
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.Smooth。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用引理 `RingHom.Smooth.respectsIso`：respectsIso : RespectsIso Smooth
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.smooth_algebraMap`：smooth_algebraMap [Algebra R S] : (algebraMap
 R S).Smooth ↔ Algebra.Smooth R S
· 使用定理 `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`：∀ {R : Type u_
1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R 
S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma Smooth.codescendsAlong_faithfullyFlat : CodescendsAlong Smooth FaithfullyFlat := by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_smooth_tensorProduct_of_faithfullyFlat S
/-
**RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat** 是 Mathlib 中的一个定理，位
于命名空间 `RingHom.FormallyUnramified`。
形式化陈述：RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.Fo
rmallyUnramified)   fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFla
t
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.FormallyUnramified。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用引理 `RingHom.FormallyUnramified.respectsIso`：respectsIso : RespectsIso Formal
lyUnramified
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.formallyUnramified_algebraMap`：formallyUnramified_algebraMap [Al
gebra R S] : (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R 
S
· 使用定理 `Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithf
ullyFlat`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma FormallyUnramified.codescendsAlong_faithfullyFlat :
    CodescendsAlong FormallyUnramified FaithfullyFlat := by
  refine .mk _ FormallyUnramified.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [formallyUnramified_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_formallyUnramified_tensorProduct_of_faithfullyFlat S
/-
**RingHom.Etale.codescendsAlong_faithfullyFlat** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m.Etale`。
形式化陈述：RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.Et
ale) fun {R S} [CommRing R] [CommRing S] =>   RingHom.FaithfullyFlat
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.Etale。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用定理 `RingHom.Etale.respectsIso`：RingHom.RespectsIso fun {R S} [CommRing R] [C
ommRing S] => RingHom.Etale
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.etale_algebraMap`：etale_algebraMap [Algebra R S] : (algebraMap R
 S).Etale ↔ Algebra.Etale R S
· 使用定理 `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`：∀ {R : Type u_1}
 {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]
 (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma Etale.codescendsAlong_faithfullyFlat : CodescendsAlong Etale FaithfullyFlat := by
  refine .mk _ Etale.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [etale_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_etale_tensorProduct_of_faithfullyFlat S

end RingHom

