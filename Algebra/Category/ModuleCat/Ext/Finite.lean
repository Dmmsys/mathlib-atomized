/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# `Ext`-modules between finitely generated modules over Noetherian rings are finitely generated

-/

public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian

/-
**ModuleCat.finite_ext** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ModuleCat.finite_ext [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{
v} R) [Module.Finite R N] [Module.Finite R M] (i : Nat) : Module.Finite R (Ext N
 M i)
参数：N M : ModuleCat.{v} R；i : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `ModuleCat.Algebra.instSMulCommClassCarrier`：∀ {S₀ : Type u₀} [inst : Com
mSemiring S₀] {S : Type u} [inst_1 : Ring S] [inst_2 : Algebra S₀ S] {M : Module
Cat S},   SMulCommClass S S₀ ↑M
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `Module.exists_finite_presentation`：Module.exists_finite_presentation [Sm
all.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : exis
ts (P : Type v) (_ : Ad…
· 使用定理 `LinearMap.shortExact_shortComplexKer`：LinearMap.shortExact_shortComplexK
er {f : M ->ₗ[R] N} (h : Function.Surjective f) : f.shortComplexKer.ShortExact w
here exact
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `precomp_extClass_surjective_of_projective_X₂`：precomp_extClass_surjectiv
e_of_projective_X₂ [Small.{v} R] (M : ModuleCat.{v} R) {S : ShortComplex (Module
Cat.{v} R)} (h : S.ShortExact) (n …
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
-/
instance ModuleCat.finite_ext [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) : Module.Finite R (Ext N M i) := by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module.Finite.of_surjective (exac.extClass.precompOfLinear R M (add_comm 1 n))
      (precomp_extClass_surjective_of_projective_X₂ M exac n)
