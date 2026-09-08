/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Factorizations.Basic

/-!
# Factorization lemma

Let `C` be an abelian category with enough injectives. We show that
any morphism `f : K ⟶ L` between bounded below cochain complexes in `C`
can be factored as `i ≫ p` where `i : K ⟶ L'` is a monomorphism (with
`L'` bounded below) and `p : L' ⟶ L` a quasi-isomorphism that is an epimorphism
with a degreewise injective kernel. (This is part of the factorization axiom CM5
for a model category structure on bounded below cochain complexes (TODO @joelriou).)

-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace cm5b

variable (K L) in
/-- Given a cochain complex `K`, this is a cochain complex `I K` with
zero differentials which in degree `n` consists of the injective
object `Injective.under (K.X n)`. -/
@[simps]
/-
**CochainComplex.cm5b.I** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.cm5b`。
形式化陈述：I : CochainComplex C Int where X n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cochain complex `K`, this is a cochain complex `I K` with
zero differentials which in degree `n` consists of the injective
object `Injective.under (K.X n)`.
-/
noncomputable def I : CochainComplex C ℤ where
  X n := Injective.under (K.X n)
  d _ _ := 0

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Injective ((I K).X n) := by
  dsimp
  infer_instance
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) [K.IsStrictlyGE n] : (I K).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact Injective.isZero_under _ (K.isZero_of_isStrictlyGE n i hi)
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    (mappingCone (𝟙 (I K)) ⊞ L).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapBiprod _ _)
  simp only [HomologicalComplex.eval_obj, biprod_isZero_iff, mappingCone.isZero_X_iff, I_X]
  refine ⟨⟨?_, ?_⟩, L.isZero_of_isStrictlyGE n i hi⟩
  all_goals exact (I K).isZero_of_isStrictlyGE (n + 1) _

variable (K L) in
/-- The second projection `mappingCone (𝟙 (I K)) ⊞ L ⟶ L`. -/
/-
**CochainComplex.cm5b.p** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex.cm5b`。
形式化陈述：p : mappingCone (𝟙 (I K)) ⊞ L ⟶ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection `mappingCone (𝟙 (I K)) ⊞ L ⟶ L`.
-/
noncomputable abbrev p : mappingCone (𝟙 (I K)) ⊞ L ⟶ L := biprod.snd

set_option backward.isDefEq.respectTransparency false in
/-- A lift of a morphism `f : K ⟶ L` between bounded below cochain complexes
as a monomorphism `K ⟶ mappingCone (𝟙 (I K)) ⊞ L`. -/
/-
**CochainComplex.cm5b.i** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.cm5b`。
形式化陈述：i : K ⟶ mappingCone (𝟙 (I K)) ⊞ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lift of a morphism `f : K ⟶ L` between bounded below cochain complexes
as a monomorphism `K ⟶ mappingCone (𝟙 (I K)) ⊞ L`.
-/
noncomputable def i : K ⟶ mappingCone (𝟙 (I K)) ⊞ L :=
  biprod.lift (mappingCone.lift _
    (HomComplex.Cocycle.mk (HomComplex.Cochain.mk (fun p q _ => K.d p q ≫ Injective.ι _)) 2
      (by lia) (by
        ext p q hpq
        simp [HomComplex.δ_v 1 2 (by lia) _ p q hpq (p + 1) (p + 1) (by lia) rfl]))
    (HomComplex.Cochain.ofHoms (fun n => Injective.ι _)) (by cat_disch)) f

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.cm5b.i_f_comp** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.cm5b`。
形式化陈述：i_f_comp (n : Int) : (i f).f n ≫ (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶
 _).f n ≫ (mappingCone.snd (𝟙 (I K))).v n n (add_zero n) = Injective.ι (K.X n)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.biprod_lift_fst_f_assoc`：∀ {C : Type u_1} {ι : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   {c : ComplexShape ι}…
· 使用引理 `CochainComplex.mappingCone.lift_f_snd_v`：lift_f_snd_v (p q : Int) (hpq :
 p + 0 = q) : (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma i_f_comp (n : ℤ) : (i f).f n ≫
    (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _).f n ≫
      (mappingCone.snd (𝟙 (I K))).v n n (add_zero n) = Injective.ι (K.X n) := by
  simp [i]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Mono ((i f).f n) := mono_of_mono_fac (i_f_comp f n)
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (i f) := HomologicalComplex.mono_of_mono_f (i f) inferInstance

@[reassoc (attr := simp)]
/-
**CochainComplex.cm5b.fac** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.cm5b`。
形式化陈述：fac : i f ≫ p K L = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fac : i f ≫ p K L = f := by simp [i]
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Injective ((mappingCone (𝟙 (I K))).X n) :=
  Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (I K)) n (n + 1) rfl).symm
    inferInstance

variable (K L) in
/-
**CochainComplex.cm5b.degreewiseEpiWithInjectiveKernel_p** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.cm5b`。
形式化陈述：degreewiseEpiWithInjectiveKernel_p : degreewiseEpiWithInjectiveKernel (p K
 L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.epiWithInjectiveKernel_iff`：epiWithInjectiveKerne
l_iff {X Y : C} (g : X ⟶ Y) : epiWithInjectiveKernel g ↔ exists (I : C) (_ : Inj
ective I) (f : I ⟶ X) (w : f ≫ g = 0), …
· 使用定理 `CochainComplex.cm5b.instInjectiveXIntMappingConeIdI`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C] 
  [inst_2 : CategoryTheory.EnoughInjectiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.total`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst_2
 : CategoryTheory.Limits…
-/
lemma degreewiseEpiWithInjectiveKernel_p :
    degreewiseEpiWithInjectiveKernel (p K L) := by
  intro n
  rw [epiWithInjectiveKernel_iff]
  refine ⟨(mappingCone (𝟙 (I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_,
    (biprod.fst : (mappingCone (𝟙 (I K))) ⊞ L ⟶ _).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_, ?_, ?_⟩
  all_goals simp [← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply]

variable (K L) in
/-- The second projection `p K L : mappingCone (𝟙 (I K)) ⊞ L ⟶ L` is a homotopy equivalence. -/
/-
**CochainComplex.cm5b.homotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.cm
5b`。
形式化陈述：homotopyEquiv : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection `p K L : mappingCone (𝟙 (I K)) ⊞ L ⟶ L` is a homotopy equi
valence.
-/
noncomputable def homotopyEquiv : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where
  hom := p K L
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ : Homotopy (𝟙 (mappingCone (𝟙 (I K)))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ mappingCone (𝟙 (I K)) ⊞ L)).compLeft
        (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    (Homotopy.ofEq (by simp [p])).trans (h₂.symm.trans (Homotopy.ofEq (by simp)))
  homotopyInvHomId := Homotopy.ofEq (by simp)
/-
**CochainComplex.cm5b.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.cm5b`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso (p K L) := (homotopyEquiv K L).quasiIso_hom

end cm5b

/-
**CochainComplex.cm5b** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：cm5b (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] : exists (L' : 
CochainComplex C Int) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L) (_hi 
: Mono i) (_hp : degreewiseEpiWithInjectiveKernel p) (_hp' : QuasiIso p), i ≫ p 
= f
参数：n : Int；n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `CochainComplex.cm5b.instIsStrictlyGEBiprodIntMappingConeIdIOfHAddOfNat`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.EnoughInjectiv…
· 使用定理 `CochainComplex.cm5b.instMonoIntI`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Categor
yTheory.EnoughInjectiv…
· 使用引理 `CochainComplex.cm5b.degreewiseEpiWithInjectiveKernel_p`：degreewiseEpiWit
hInjectiveKernel_p : degreewiseEpiWithInjectiveKernel (p K L)
· 使用定理 `CochainComplex.cm5b.instQuasiIsoIntP`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.EnoughInjectiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.cm5b.fac`：fac : i f ≫ p K L = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cm5b (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n)
      (i : K ⟶ L') (p : L' ⟶ L) (_hi : Mono i)
      (_hp : degreewiseEpiWithInjectiveKernel p) (_hp' : QuasiIso p),
      i ≫ p = f :=
  ⟨_ , by infer_instance, cm5b.i f, cm5b.p K L, inferInstance,
    cm5b.degreewiseEpiWithInjectiveKernel_p K L, inferInstance, by simp⟩

end CochainComplex

