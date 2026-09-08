/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Transcendental elements in `MvPolynomial`

This file lists some results on some elements in `MvPolynomial σ R` being transcendental
over the base ring `R` and subrings `MvPolynomial.supported` of `MvPolynomial σ R`.
-/

public section

universe u v w

open Polynomial

namespace MvPolynomial

variable {σ : Type*} (R : Type*) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.transcendental_supported_polynomial_aeval_X** 是 Mathlib 中的一个定理，位于
命名空间 `MvPolynomial`。
形式化陈述：transcendental_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s
) {f : R[X]} (hf : Transcendental R f) : Transcendental (supported R s) (Polynom
ial.aeval (X i : MvPolynomial σ R) f)
参数：h : i ∉ s；hf : Transcendental R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `transcendental_iff_injective`：transcendental_iff_injective {x : A} : Tra
nscendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `MvPolynomial.supportedEquivMvPolynomial_symm_X`：supportedEquivMvPolynomi
al_symm_X (s : Set σ) (i : s) : (↑((supportedEquivMvPolynomial s).symm (X i : Mv
Polynomial s R)) : MvPolynomial σ R)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.algHom_ext'`：algHom_ext' {f g : A[X] ->ₐ[R] B} (hC : f.comp C
AlgHom = g.comp CAlgHom) (hX : f X = g X) : f = g
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `MvPolynomial.optionEquivLeft_symm_apply`：∀ (R : Type u) (S₁ : Type v) [i
nst : CommSemiring R] (a : Polynomial (MvPolynomial S₁ R)),   (MvPolynomial.opti
onEquivLeft R S₁).symm a =   …
· 使用定理 `Polynomial.aevalTower_C`：aevalTower_C (x : R) : aevalTower g y (C x) = g
 x
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `MvPolynomial.optionEquivRight_apply`：∀ (R : Type u) (S₁ : Type v) [inst 
: CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivR
ight R S₁) a =     (MvPol…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.optionEquivRight_symm_apply`：∀ (R : Type u) (S₁ : Type v) [
inst : CommSemiring R] (a : MvPolynomial S₁ (Polynomial R)),   (MvPolynomial.opt
ionEquivRight R S₁).symm a =  …
· 使用定理 `MvPolynomial.aevalTower_X`：aevalTower_X (i : σ) : aevalTower g y (X i) =
 y i
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
（共 41 条，此处仅展示前 30 条）
-/
theorem transcendental_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s)
    {f : R[X]} (hf : Transcendental R f) :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  classical
  rw [transcendental_iff_injective] at hf ⊢
  let g := MvPolynomial.mapAlgHom (R := R) (σ := s) (Polynomial.aeval (R := R) f)
  replace hf : Function.Injective g := MvPolynomial.map_injective _ hf
  let u := (Subalgebra.val _).comp
    ((optionEquivRight R s).symm |>.trans
      (renameEquiv R (Set.subtypeInsertEquivOption h).symm) |>.trans
      (supportedEquivMvPolynomial _).symm).toAlgHom |>.comp
    g |>.comp
    ((optionEquivLeft R s).symm.trans (optionEquivRight R s)).toAlgHom
  let v := ((Polynomial.aeval (R := supported R s)
    (Polynomial.aeval (X i : MvPolynomial σ R) f)).restrictScalars R).comp
      (Polynomial.mapAlgEquiv (supportedEquivMvPolynomial s).symm).toAlgHom
  replace hf : Function.Injective u := by
    simp only [AlgHom.coe_comp, Subalgebra.coe_val,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_trans, Function.comp_assoc, u]
    apply Subtype.val_injective.comp
    simp only [EquivLike.comp_injective]
    apply hf.comp
    simp only [EquivLike.comp_injective, EquivLike.injective]
  have h1 : Polynomial.aeval (X i : MvPolynomial σ R) = ((Subalgebra.val _).comp
      (supportedEquivMvPolynomial _).symm.toAlgHom |>.comp
      (Polynomial.aeval (X ⟨i, s.mem_insert i⟩ : MvPolynomial ↑(insert i s) R))) := by
    ext1; simp
  have h2 : u = v := by
    simp only [u, v, g]
    ext1
    · ext1
      simp [Set.subtypeInsertEquivOption, Subalgebra.algebraMap_eq, optionEquivLeft_symm_apply]
    · simp [Set.subtypeInsertEquivOption, h1, optionEquivLeft_symm_apply]
  simpa only [h2, v, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.injective_comp, AlgHom.coe_restrictScalars'] using hf
/-
**MvPolynomial.transcendental_polynomial_aeval_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：transcendental_polynomial_aeval_X (i : σ) {f : R[X]} (hf : Transcendental 
R f) : Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f)
参数：i : σ；hf : Transcendental R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.transcendental_supported_polynomial_aeval_X`：transcendental
_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s) {f : R[X]} (hf : T
ranscendental R f) : Transcendental (supported…
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `MvPolynomial.C_injective`：C_injective (σ : Type*) (R : Type*) [CommSemir
ing R] : Function.Injective (C : R -> MvPolynomial σ R)
· 使用定理 `MvPolynomial.supported_empty`：supported_empty : supported R (∅ : Set σ) 
= ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isAlgebraic_ringHom_iff_of_comp_eq`：isAlgebraic_ringHom_iff_of_comp_eq (
hg : Function.Injective g) (h : RingHom.comp (algebraMap S B) f = RingHom.comp g
 (algebraMap R A)) {a : …
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
-/
theorem transcendental_polynomial_aeval_X (i : σ) {f : R[X]} (hf : Transcendental R f) :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  have := transcendental_supported_polynomial_aeval_X R (Set.notMem_empty i) hf
  let g := (Algebra.botEquivOfInjective (MvPolynomial.C_injective σ R)).symm.trans
    (Subalgebra.equivOfEq _ _ supported_empty).symm
  rwa [Transcendental, ← isAlgebraic_ringHom_iff_of_comp_eq g (RingHom.id (MvPolynomial σ R))
    Function.injective_id (by ext1; rfl), RingHom.id_apply, ← Transcendental]
/-
**MvPolynomial.transcendental_polynomial_aeval_X_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
形式化陈述：transcendental_polynomial_aeval_X_iff (i : σ) {f : R[X]} : Transcendental 
R (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔ Transcendental R f
参数：i : σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.algHom`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] {B : Type u_2}   [inst_3 : Ring B] [inst_4 
: Algebr…
· 使用定理 `MvPolynomial.transcendental_polynomial_aeval_X`：transcendental_polynomia
l_aeval_X (i : σ) {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polyn
omial.aeval (X i : MvPolynomial σ R)…
-/
theorem transcendental_polynomial_aeval_X_iff (i : σ) {f : R[X]} :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔ Transcendental R f := by
  refine ⟨?_, transcendental_polynomial_aeval_X R i⟩
  simp_rw [Transcendental, not_imp_not]
  exact fun h ↦ h.algHom _
/-
**MvPolynomial.transcendental_supported_polynomial_aeval_X_iff** 是 Mathlib 中的一个定
理，位于命名空间 `MvPolynomial`。
形式化陈述：transcendental_supported_polynomial_aeval_X_iff [Nontrivial R] {i : σ} {s 
: Set σ} {f : R[X]} : Transcendental (supported R s) (Polynomial.aeval (X i : Mv
Polynomial σ R) f) ↔ i ∉ s ∧ Transcendental R f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Polynomial.aeval_mem_adjoin_singleton`：∀ (R : Type u) {A : Type z} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {p : Polynomial 
R}   (x : A), (Polynomial.a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.transcendental_polynomial_aeval_X_iff`：transcendental_polyn
omial_aeval_X_iff (i : σ) {f : R[X]} : Transcendental R (Polynomial.aeval (X i :
 MvPolynomial σ R) f) ↔ Transcendental R…
· 使用定理 `Transcendental.restrictScalars`：Transcendental.restrictScalars (hinj : F
unction.Injective (algebraMap R S)) {x : A} (h : Transcendental S x) : Transcend
ental R x
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.C_injective`：C_injective (σ : Type*) (R : Type*) [CommSemir
ing R] : Function.Injective (C : R -> MvPolynomial σ R)
· 使用定理 `MvPolynomial.transcendental_supported_polynomial_aeval_X`：transcendental
_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s) {f : R[X]} (hf : T
ranscendental R f) : Transcendental (supported…
-/
theorem transcendental_supported_polynomial_aeval_X_iff
    [Nontrivial R] {i : σ} {s : Set σ} {f : R[X]} :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔
    i ∉ s ∧ Transcendental R f := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, hf⟩ ↦ transcendental_supported_polynomial_aeval_X R h hf⟩
  · rw [Transcendental] at h
    contrapose h
    refine isAlgebraic_algebraMap (⟨Polynomial.aeval (X i) f, ?_⟩ : supported R s)
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ h))
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  · rw [← transcendental_polynomial_aeval_X_iff R i]
    refine h.restrictScalars fun _ _ heq ↦ MvPolynomial.C_injective σ R ?_
    simp_rw [← MvPolynomial.algebraMap_eq]
    exact congr($(heq).1)
/-
**MvPolynomial.transcendental_supported_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：transcendental_supported_X {i : σ} {s : Set σ} (h : i ∉ s) : Transcendenta
l (supported R s) (X i : MvPolynomial σ R)
参数：h : i ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `MvPolynomial.transcendental_supported_polynomial_aeval_X`：transcendental
_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s) {f : R[X]} (hf : T
ranscendental R f) : Transcendental (supported…
· 使用定理 `Polynomial.transcendental_X`：Polynomial.transcendental_X : Transcendenta
l R (X (R
-/
theorem transcendental_supported_X {i : σ} {s : Set σ} (h : i ∉ s) :
    Transcendental (supported R s) (X i : MvPolynomial σ R) := by
  simpa using transcendental_supported_polynomial_aeval_X R h (Polynomial.transcendental_X R)
/-
**MvPolynomial.transcendental_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：transcendental_X (i : σ) : Transcendental R (X i : MvPolynomial σ R)
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `MvPolynomial.transcendental_polynomial_aeval_X`：transcendental_polynomia
l_aeval_X (i : σ) {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polyn
omial.aeval (X i : MvPolynomial σ R)…
· 使用定理 `Polynomial.transcendental_X`：Polynomial.transcendental_X : Transcendenta
l R (X (R
-/
theorem transcendental_X (i : σ) : Transcendental R (X i : MvPolynomial σ R) := by
  simpa using transcendental_polynomial_aeval_X R i (Polynomial.transcendental_X R)
/-
**MvPolynomial.transcendental_supported_X_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
形式化陈述：transcendental_supported_X_iff [Nontrivial R] {i : σ} {s : Set σ} : Transc
endental (supported R s) (X i : MvPolynomial σ R) ↔ i ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MvPolynomial.transcendental_supported_polynomial_aeval_X_iff`：transcende
ntal_supported_polynomial_aeval_X_iff [Nontrivial R] {i : σ} {s : Set σ} {f : R[
X]} : Transcendental (supported R s) (Polynomial.a…
-/
theorem transcendental_supported_X_iff [Nontrivial R] {i : σ} {s : Set σ} :
    Transcendental (supported R s) (X i : MvPolynomial σ R) ↔ i ∉ s := by
  simpa [Polynomial.transcendental_X] using
    transcendental_supported_polynomial_aeval_X_iff R (i := i) (s := s) (f := Polynomial.X)

end MvPolynomial

