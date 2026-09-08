/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!

# Projective Dimension in ModuleCat

This file deals with preservation of `projectiveDimension` in (semi) linear equivalences.
Previously we only know this for linear equivalence within same universe level, now it works with
all universe level where the ring `R` is small.

## Main Results

* `ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv`: a module `N` satisfy
  `HasProjectiveDimensionLE N n` if it is semi-linear equivalent to a module `M` that
  `HasProjectiveDimensionLE M n`.

* `ModuleCat.projectiveDimension_eq_of_semiLinearEquiv`: `projectiveDimension` is preserved
  under arbitrary semi-linear equivalence.

* `ModuleCat.hasProjectiveDimensionLE_of_linearEquiv`: a module `N` satisfy
  `HasProjectiveDimensionLE N n` if it is linear equivalent to a module `M` that
  `HasProjectiveDimensionLE M n`.

* `ModuleCat.projectiveDimension_eq_of_linearEquiv`: `projectiveDimension` is preserved
  under arbitrary linear equivalence.

-/

public section

universe v v' u u'

variable {R : Type u} [Ring R]

open CategoryTheory Abelian Module

namespace ModuleCat

section

variable [Small.{v} R] {R' : Type u'} [Ring R'] [Small.{v'} R'] (e : R ≃+* R')

variable {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] RingHomInvPair.of_ringEquiv in
/-
**ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv** 是 Mathlib 中的一个引理，位于命名空
间 `ModuleCat`。
形式化陈述：hasProjectiveDimensionLE_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRin
gHom e] N) (n : Nat) [HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N
 n
参数：e' : M ≃ₛₗ[RingHomClass.toRingHom e] N；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.projective_iff_hasProjectiveDimensionLT_one`：projective_i
ff_hasProjectiveDimensionLT_one : Projective X ↔ HasProjectiveDimensionLT X 1
· 使用定理 `IsProjective.iff_projective`：IsProjective.iff_projective [Small.{v} R] (
P : Type v) [AddCommGroup P] [Module R P] : Module.Projective R P ↔ Projective (
of R P)
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
· 使用定理 `ModuleCat.shortExact_projectiveShortComplex`：ModuleCat.shortExact_projec
tiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) : M.projectiveShortComplex.
ShortExact
· 使用定理 `RingHomInvPair.symm`：symm (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHom
InvPair σ₁₂ σ₂₁] : RingHomInvPair σ₂₁ σ₁₂
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Shrink.linearEquiv_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : Small.
{v, u_2} α] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α]   [inst_3 : _root_.
Module R α] (a…
· 使用定理 `RingEquiv.toSemilinearEquiv_apply`：∀ {R : Type u_1} {S : Type u_6} [inst
 : Semiring R] [inst_1 : Semiring S] (f : R ≃+* S) (a : R),   f.toSemilinearEqui
v a = f a
· 使用定理 `Shrink.linearEquiv_symm_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : S
mall.{v, u_2} α] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α]   [inst_3 : _r
oot_.Module R α] (a…
· 使用定理 `Module.Basis.constr_apply`：constr_apply (f : ι -> M') (x : M) : constr (
M'
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
（共 45 条，此处仅展示前 30 条）
-/
lemma hasProjectiveDimensionLE_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N)
    (n : ℕ) [HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n := by
  induction n generalizing M N e' with
  | zero =>
    have : HasProjectiveDimensionLE M 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add] at this ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective] at this ⊢
    exact Projective.of_equiv e'
  | succ n ih =>
    let S := M.projectiveShortComplex
    let S' := N.projectiveShortComplex
    have S_exact := M.shortExact_projectiveShortComplex
    have S'_exact := N.shortExact_projectiveShortComplex
    let eR : Shrink.{v} R ≃ₛₗ[RingHomClass.toRingHom e] Shrink.{v'} R' :=
      ((Shrink.linearEquiv R R).trans e.toSemilinearEquiv).trans (Shrink.linearEquiv R' R').symm
    let e2 : S.X₂ ≃ₛₗ[RingHomClass.toRingHom e] S'.X₂ :=
      (Finsupp.mapDomain.linearEquiv (Shrink R) R e').trans (Finsupp.mapRange.linearEquiv eR)
    have comm : S'.g.hom.comp e2.toLinearMap = e'.toLinearMap.comp S.g.hom := by
      ext m r
      simp [S, S', e2, eR, Basis.constr_apply, map_smulₛₗ]
    have : S.g.hom.ker = Submodule.comap e2.toLinearMap S'.g.hom.ker := by
      rw [← LinearMap.ker_comp, comm, LinearEquiv.ker_comp]
    rw [Submodule.comap_equiv_eq_map_symm] at this
    let eker : S.X₁ ≃ₛₗ[RingHomClass.toRingHom e] S'.X₁ :=
      (LinearEquiv.ofEq _ _ this).trans (e2.symm.submoduleMap S'.g.hom.ker).symm
    have := (S_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp ‹_›
    exact (S'_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr (ih eker)

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.hasProjectiveDimensionLE_of_semiLinearEquiv :=
  hasProjectiveDimensionLE_of_semiLinearEquiv

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-
**ModuleCat.projectiveDimension_eq_of_semiLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 
`ModuleCat`。
形式化陈述：projectiveDimension_eq_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingH
om e] N) : projectiveDimension M = projectiveDimension N
参数：e' : M ≃ₛₗ[RingHomClass.toRingHom e] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv`：hasProjectiveDime
nsionLE_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) (n : Nat) [H
asProjectiveDimensionLE M n] : HasProjectiv…
-/
lemma projectiveDimension_eq_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) :
    projectiveDimension M = projectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e'.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [projectiveDimension_le_iff]
      exact ⟨fun h ↦ hasProjectiveDimensionLE_of_semiLinearEquiv e e' n,
        fun h ↦ hasProjectiveDimensionLE_of_semiLinearEquiv e.symm e'.symm n⟩

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.projectiveDimension_eq_of_semiLinearEquiv :=
  projectiveDimension_eq_of_semiLinearEquiv

end

section

variable [Small.{v} R] [Small.{v'} R] {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}

/-
**ModuleCat.hasProjectiveDimensionLE_of_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `M
oduleCat`。
形式化陈述：hasProjectiveDimensionLE_of_linearEquiv (e : M ≃ₗ[R] N) (n : Nat) [HasProj
ectiveDimensionLE M n] : HasProjectiveDimensionLE N n
参数：e : M ≃ₗ[R] N；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv`：hasProjectiveDime
nsionLE_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) (n : Nat) [H
asProjectiveDimensionLE M n] : HasProjectiv…
-/
lemma hasProjectiveDimensionLE_of_linearEquiv (e : M ≃ₗ[R] N)
    (n : ℕ) [HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n :=
  #adaptation_note /-- 2026-05-20 (kmill) #13807, instances are more eager to apply, but the
  `univ_out_params` attribute for `Small` doesn't seem to restrict local instances, so the
  wrong universe levels are inferred. Added `.{v, v'}`. -/
  hasProjectiveDimensionLE_of_semiLinearEquiv.{v, v'} (RingEquiv.refl R) e n

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.hasProjectiveDimensionLE_of_linearEquiv :=
  hasProjectiveDimensionLE_of_linearEquiv
/-
**ModuleCat.projectiveDimension_eq_of_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Mod
uleCat`。
形式化陈述：projectiveDimension_eq_of_linearEquiv (e : M ≃ₗ[R] N) : projectiveDimensio
n M = projectiveDimension N
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.projectiveDimension_eq_of_semiLinearEquiv`：projectiveDimension
_eq_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) : projectiveDime
nsion M = projectiveDimension N
-/
lemma projectiveDimension_eq_of_linearEquiv (e : M ≃ₗ[R] N) :
    projectiveDimension M = projectiveDimension N :=
  #adaptation_note /-- 2026-05-20 (kmill) #13807, instances are more eager to apply, but the
  `univ_out_params` attribute for `Small` doesn't seem to restrict local instances, so the
  wrong universe levels are inferred. Added `.{v, v'}`. -/
  projectiveDimension_eq_of_semiLinearEquiv.{v, v'} (M := M) (N := N) (RingEquiv.refl R) e

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.projectiveDimension_eq_of_linearEquiv :=
  projectiveDimension_eq_of_linearEquiv

end

/-
**ModuleCat.projectiveDimension_eq_zero_of_projective** 是 Mathlib 中的一个引理，位于命名空间 
`ModuleCat`。
形式化陈述：projectiveDimension_eq_zero_of_projective (M : ModuleCat.{v} R) [Nontrivia
l M] [Projective M] : projectiveDimension M = 0
参数：M : ModuleCat.{v} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma projectiveDimension_eq_zero_of_projective (M : ModuleCat.{v} R) [Nontrivial M]
    [Projective M] : projectiveDimension M = 0 := by
  simpa [projectiveDimension_eq_zero_iff, ModuleCat.isZero_iff_subsingleton,
    not_subsingleton_iff_nontrivial] using ⟨‹_›, ‹_›⟩

end ModuleCat

