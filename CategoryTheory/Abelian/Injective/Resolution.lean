/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Tactic.AdaptationNote

/-!
# Abelian categories with enough injectives have injective resolutions

## Main results
When the underlying category is abelian:
* `CategoryTheory.InjectiveResolution.desc`: Given `I : InjectiveResolution X` and
  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a cochain map
  `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwines the descent and
  the original morphism, see `CategoryTheory.InjectiveResolution.desc_commutes`.
* `CategoryTheory.InjectiveResolution.descHomotopy`: Any two such descents are homotopic.
* `CategoryTheory.InjectiveResolution.homotopyEquiv`: Any two injective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.injectiveResolutions`: If every object admits an injective resolution, we can
  construct a functor `injectiveResolutions C : C ⥤ HomotopyCategory C`.

* `CategoryTheory.exact_f_d`: `f` and `Injective.d f` are exact.
* `CategoryTheory.InjectiveResolution.of`: Hence, starting from a monomorphism `X ⟶ J`, where `J`
  is injective, we can apply `Injective.d` repeatedly to obtain an injective resolution of `X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Injective

namespace InjectiveResolution

section

variable [HasZeroObject C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `descFZero` / `descFZero` 的定义

English:
definition descFZero
  signature: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  body: factorThru (f ≫ I.ι.f 0) (J.ι.f 0)

中文:
定义 descFZero
  签名: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  定义体: factorThru (f ≫ I.ι.f 0) (J.ι.f 0)

Depends on / 依赖: factorThru
-/
def descFZero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 0 ⟶ I.cocomplex.X 0 :=
  factorThru (f ≫ I.ι.f 0) (J.ι.f 0)

end

section Abelian

variable [Abelian C]

/--
lemma `exact₀` / 引理 `exact₀`

English:
lemma exact₀
  given: {Z : C} (I : InjectiveResolution Z)
  proof: ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork

中文:
引理 exact₀
  条件: {Z : C} (I : InjectiveResolution Z)
  证明: ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork

Depends on / 依赖: I.isLimitKernelFork, ShortComplex, ShortComplex.exact_of_f_is_kernel, exact_of_f_is_kernel, isLimitKernelFork
-/
lemma exact₀ {Z : C} (I : InjectiveResolution Z) :
    (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
  ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `descFOne` / `descFOne` 的定义

English:
definition descFOne
  signature: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  body: J.exact₀.descToInjective (descFZero f I J ≫ I.cocomplex.d 0 1)
    (by dsimp; simp only [← assoc, descFZero]; simp [assoc])

@[simp]

中文:
定义 descFOne
  签名: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  定义体: J.exact₀.descToInjective (descFZero f I J ≫ I.cocomplex.d 0 1)
    (by dsimp; simp only [← assoc, descFZero]; simp [assoc])

@[simp]

Depends on / 依赖: I.cocomplex.d, J.exact, cocomplex, descFZero, descToInjective
-/
def descFOne {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 1 ⟶ I.cocomplex.X 1 :=
  J.exact₀.descToInjective (descFZero f I J ≫ I.cocomplex.d 0 1)
    (by dsimp; simp only [← assoc, descFZero]; simp [assoc])

@[simp]
/--
theorem `descFOne_zero_comm` / 定理 `descFOne_zero_comm`

English:
theorem descFOne_zero_comm
  statement: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
  proof: by
  apply J.exact₀.comp_descToInjective

中文:
定理 descFOne_zero_comm
  结论: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
  证明: by
  apply J.exact₀.comp_descToInjective

Depends on / 依赖: J.exact, comp_descToInjective
-/
theorem descFOne_zero_comm {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) :
    J.cocomplex.d 0 1 ≫ descFOne f I J = descFZero f I J ≫ I.cocomplex.d 0 1 := by
  apply J.exact₀.comp_descToInjective

/--
Definition of `descFSucc` / `descFSucc` 的定义

English:
definition descFSucc
  signature: {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z) (n : Nat)
  body: ⟨(J.exact_succ n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (J.exact_succ n).comp_descToInjective _ _⟩

中文:
定义 descFSucc
  签名: {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z) (n : 自然数)
  定义体: ⟨(J.exact_succ n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (J.exact_succ n).comp_descToInjective _ _⟩

Depends on / 依赖: I.cocomplex.d, J.exact_succ, cocomplex, comp_descToInjective, descToInjective, exact_succ, reassoc_of
-/
def descFSucc {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z) (n : Nat)
    (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : J.cocomplex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : J.cocomplex.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      J.cocomplex.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(J.exact_succ n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (J.exact_succ n).comp_descToInjective _ _⟩

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  body: CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩

中文:
定义 desc
  签名: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  定义体: CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩

Depends on / 依赖: CochainComplex, CochainComplex.mkHom, descFOne, descFOne_zero_comm, descFSucc, descFZero, w.symm
-/
def desc {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[reassoc (attr := simp)]
/--
theorem `desc_commutes` / 定理 `desc_commutes`

English:
theorem desc_commutes
  statement: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
  proof: by
  ext
  simp [desc, descFOne, descFZero]

@[reassoc (attr := simp)]

中文:
定理 desc_commutes
  结论: {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
  证明: by
  ext
  simp [desc, descFOne, descFZero]

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.op, descFOne, descFZero, natTrans
-/
theorem desc_commutes {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) : J.ι ≫ desc f I J = (CochainComplex.single₀ C).map f ≫ I.ι := by
  ext
  simp [desc, descFOne, descFZero]

@[reassoc (attr := simp)]
/--
lemma `desc_commutes_zero` / 引理 `desc_commutes_zero`

English:
lemma desc_commutes_zero
  statement: {Y Z : C} (f : Z ⟶ Y)
  proof: (HomologicalComplex.congr_hom (desc_commutes f I J) 0).trans (by simp)

中文:
引理 desc_commutes_zero
  结论: {Y Z : C} (f : Z ⟶ Y)
  证明: (HomologicalComplex.congr_hom (desc_commutes f I J) 0).trans (by simp)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, congr_hom, desc_commutes
-/
lemma desc_commutes_zero {Y Z : C} (f : Z ⟶ Y)
    (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.ι.f 0 ≫ (desc f I J).f 0 = f ≫ I.ι.f 0 :=
  (HomologicalComplex.congr_hom (desc_commutes f I J) 0).trans (by simp)

-- Now that we've checked this property of the descent, we can seal away the actual definition.
/--
Definition of `descHomotopyZeroZero` / `descHomotopyZeroZero` 的定义

English:
definition descHomotopyZeroZero
  signature: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  body: I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]

中文:
定义 descHomotopyZeroZero
  签名: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  定义体: I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.f, I.exact, congr_arg, congr_fun, descToInjective
-/
def descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
/--
lemma `comp_descHomotopyZeroZero` / 引理 `comp_descHomotopyZeroZero`

English:
lemma comp_descHomotopyZeroZero
  statement: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  proof: I.exact₀.comp_descToInjective _ _

中文:
引理 comp_descHomotopyZeroZero
  结论: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  证明: I.exact₀.comp_descToInjective _ _

Depends on / 依赖: I.exact, comp_descToInjective
-/
lemma comp_descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ descHomotopyZeroZero f comm = f.f 0 :=
  I.exact₀.comp_descToInjective _ _

/--
Definition of `descHomotopyZeroOne` / `descHomotopyZeroOne` 的定义

English:
definition descHomotopyZeroOne
  signature: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  body: (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]

中文:
定义 descHomotopyZeroOne
  签名: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  定义体: (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.comm, I.exact_succ, J.cocomplex.d, Preadditive, Preadditive.comp_sub, cocomplex, comp_descHomotopyZeroZero_assoc, comp_sub, descHomotopyZeroZero, descToInjective, exact_succ, sub_self
-/
def descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
/--
lemma `comp_descHomotopyZeroOne` / 引理 `comp_descHomotopyZeroOne`

English:
lemma comp_descHomotopyZeroOne
  statement: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  proof: (I.exact_succ 0).comp_descToInjective _ _

中文:
引理 comp_descHomotopyZeroOne
  结论: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  证明: (I.exact_succ 0).comp_descToInjective _ _

Depends on / 依赖: I.exact_succ, comp_descToInjective, exact_succ
-/
lemma comp_descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.d 1 2 ≫ descHomotopyZeroOne f comm =
      f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

/--
Definition of `descHomotopyZeroSucc` / `descHomotopyZeroSucc` 的定义

English:
definition descHomotopyZeroSucc
  signature: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  body: (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub]; rw [← HomologicalComplex.Hom.comm]; rw [w]; rw [Preadditive.add_comp]; rw [Category.assoc]; rw [Category.assoc]; rw [HomologicalComplex.d_comp_d]; rw [comp_zero]; rw [add_ze

中文:
定义 descHomotopyZeroSucc
  签名: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  定义体: (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub]; rw [← HomologicalComplex.Hom.comm]; rw [w]; rw [Preadditive.add_comp]; rw [Category.assoc]; rw [Category.assoc]; rw [HomologicalComplex.d_comp_d]; rw [comp_zero]; rw [add_ze

Depends on / 依赖: Category, Category.assoc, HomologicalComplex, HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d, I.exact_succ, J.cocomplex.d, Preadditive, Preadditive.add_comp, Preadditive.comp_sub, add_comp, add_zero, cocomplex, comp_sub, comp_zero, d_comp_d, descToInjective, exact_succ, sub_self
-/
def descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : Nat) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub]; rw [← HomologicalComplex.Hom.comm]; rw [w]; rw [Preadditive.add_comp]; rw [Category.assoc]; rw [Category.assoc]; rw [HomologicalComplex.d_comp_d]; rw [comp_zero]; rw [add_zero]; rw [sub_self])

@[reassoc (attr := simp)]
/--
lemma `comp_descHomotopyZeroSucc` / 引理 `comp_descHomotopyZeroSucc`

English:
lemma comp_descHomotopyZeroSucc
  statement: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  proof: (I.exact_succ (n + 1)).comp_descToInjective _ _

中文:
引理 comp_descHomotopyZeroSucc
  结论: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  证明: (I.exact_succ (n + 1)).comp_descToInjective _ _

Depends on / 依赖: I.exact_succ, comp_descToInjective, exact_succ
-/
lemma comp_descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : Nat) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ descHomotopyZeroSucc f n g g' w =
      f.f (n + 2) - g' ≫ J.cocomplex.d _ _ :=
  (I.exact_succ (n + 1)).comp_descToInjective _ _

/--
Definition of `descHomotopyZero` / `descHomotopyZero` 的定义

English:
definition descHomotopyZero
  signature: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  body: Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩)

中文:
定义 descHomotopyZero
  签名: {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  定义体: Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩)

Depends on / 依赖: Homotopy, Homotopy.mkCoinductive, add_comm, descHomotopyZeroOne, descHomotopyZeroSucc, descHomotopyZeroZero, mkCoinductive
-/
def descHomotopyZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩)

/--
Definition of `descHomotopy` / `descHomotopy` 的定义

English:
definition descHomotopy
  signature: {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  body: Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))

中文:
定义 descHomotopy
  签名: {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  定义体: Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))

Depends on / 依赖: Homotopy, Homotopy.equivSubZero.invFun, descHomotopyZero, equivSubZero, g_comm, h_comm, invFun
-/
def descHomotopy {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (g h : I.cocomplex ⟶ J.cocomplex) (g_comm : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (h_comm : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))

/--
Definition of `descIdHomotopy` / `descIdHomotopy` 的定义

English:
definition descIdHomotopy
  signature: (X : C) (I : InjectiveResolution X)
  body: by
  apply descHomotopy (𝟙 X) <;> simp

中文:
定义 descIdHomotopy
  签名: (X : C) (I : InjectiveResolution X)
  定义体: by
  apply descHomotopy (𝟙 X) <;> simp

Depends on / 依赖: descHomotopy
-/
def descIdHomotopy (X : C) (I : InjectiveResolution X) :
    Homotopy (desc (𝟙 X) I I) (𝟙 I.cocomplex) := by
  apply descHomotopy (𝟙 X) <;> simp

/--
Definition of `descCompHomotopy` / `descCompHomotopy` 的定义

English:
definition descCompHomotopy
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
  body: by
  apply descHomotopy (f ≫ g) <;> simp

中文:
定义 descCompHomotopy
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
  定义体: by
  apply descHomotopy (f ≫ g) <;> simp

Depends on / 依赖: descHomotopy
-/
def descCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (K : InjectiveResolution Z) :
    Homotopy (desc (f ≫ g) K I) (desc f J I ≫ desc g K J) := by
  apply descHomotopy (f ≫ g) <;> simp

-- We don't care about the actual definitions of these homotopies.
/--
Definition of `homotopyEquiv` / `homotopyEquiv` 的定义

English:
definition homotopyEquiv
  signature: {X : C} (I J : InjectiveResolution X)
  body: desc (𝟙 X) J I
  inv := desc (𝟙 X) I J
homotopyHomInvId := (descCompHomotopy (𝟙 X) (𝟙 X) I J I).symm.trans by
    simpa [id_comp] using descIdHomotopy _ _
homotopyInvHomId := (descCompHomotopy (𝟙 X) (𝟙 X) J I J).symm.trans by
    simpa [id_comp] using descIdHomotopy _ _

@[reassoc (attr := simp)]

中文:
定义 homotopyEquiv
  签名: {X : C} (I J : InjectiveResolution X)
  定义体: desc (𝟙 X) J I
  inv := desc (𝟙 X) I J
homotopyHomInvId := (descCompHomotopy (𝟙 X) (𝟙 X) I J I).symm.trans by
    simpa [id_comp] using descIdHomotopy _ _
homotopyInvHomId := (descCompHomotopy (𝟙 X) (𝟙 X) J I J).symm.trans by
    simpa [id_comp] using descIdHomotopy _ _

@[reassoc (attr := simp)]
-/
def homotopyEquiv {X : C} (I J : InjectiveResolution X) :
    HomotopyEquiv I.cocomplex J.cocomplex where
  hom := desc (𝟙 X) J I
  inv := desc (𝟙 X) I J
homotopyHomInvId := (descCompHomotopy (𝟙 X) (𝟙 X) I J I).symm.trans by
    simpa [id_comp] using descIdHomotopy _ _
homotopyInvHomId := (descCompHomotopy (𝟙 X) (𝟙 X) J I J).symm.trans by
    simpa [id_comp] using descIdHomotopy _ _

@[reassoc (attr := simp)]
/--
theorem `homotopyEquiv_hom_ι` / 定理 `homotopyEquiv_hom_ι`

English:
theorem homotopyEquiv_hom_ι
  given: {X : C} (I J : InjectiveResolution X)
  proof: by simp [homotopyEquiv]

@[reassoc (attr := simp)]

中文:
定理 homotopyEquiv_hom_ι
  条件: {X : C} (I J : InjectiveResolution X)
  证明: by simp [homotopyEquiv]

@[reassoc (attr := simp)]

Depends on / 依赖: homotopyEquiv
-/
theorem homotopyEquiv_hom_ι {X : C} (I J : InjectiveResolution X) :
    I.ι ≫ (homotopyEquiv I J).hom = J.ι := by simp [homotopyEquiv]

@[reassoc (attr := simp)]
/--
theorem `homotopyEquiv_inv_ι` / 定理 `homotopyEquiv_inv_ι`

English:
theorem homotopyEquiv_inv_ι
  given: {X : C} (I J : InjectiveResolution X)
  proof: by simp [homotopyEquiv]

中文:
定理 homotopyEquiv_inv_ι
  条件: {X : C} (I J : InjectiveResolution X)
  证明: by simp [homotopyEquiv]

Depends on / 依赖: homotopyEquiv
-/
theorem homotopyEquiv_inv_ι {X : C} (I J : InjectiveResolution X) :
    J.ι ≫ (homotopyEquiv I J).inv = I.ι := by simp [homotopyEquiv]

end Abelian

end InjectiveResolution

section

variable [Abelian C]

/--
Definition of `injectiveResolution` / `injectiveResolution` 的定义

English:
abbreviation injectiveResolution
  signature: (Z : C) [HasInjectiveResolution Z]
  body: (HasInjectiveResolution.out (Z := Z)).some

中文:
缩写 injectiveResolution
  签名: (Z : C) [HasInjectiveResolution Z]
  定义体: (HasInjectiveResolution.out (Z := Z)).some

Depends on / 依赖: HasInjectiveResolution, HasInjectiveResolution.out
-/
abbrev injectiveResolution (Z : C) [HasInjectiveResolution Z] : InjectiveResolution Z :=
  (HasInjectiveResolution.out (Z := Z)).some

variable (C)
variable [HasInjectiveResolutions C]

/--
Definition of `injectiveResolutions` / `injectiveResolutions` 的定义

English:
definition injectiveResolutions
  signature: : C ⥤ HomotopyCategory C (ComplexShape.up Nat) where
  body: (HomotopyCategory.quotient _ _).obj (injectiveResolution X).cocomplex
  map f := (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descIdHomot

中文:
定义 injectiveResolutions
  签名: : C ⥤ HomotopyCategory C (ComplexShape.up 自然数) where
  定义体: (HomotopyCategory.quotient _ _).obj (injectiveResolution X).cocomplex
  map f := (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descIdHomot

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, cocomplex, injectiveResolution, quotient
-/
def injectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.up Nat) where
  obj X := (HomotopyCategory.quotient _ _).obj (injectiveResolution X).cocomplex
  map f := (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descCompHomotopy
variable {C}

/--
Definition of `InjectiveResolution.iso` / `InjectiveResolution.iso` 的定义

English:
definition InjectiveResolution.iso
  signature: {X : C} (I : InjectiveResolution X)
  body: HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

中文:
定义 InjectiveResolution.iso
  签名: {X : C} (I : InjectiveResolution X)
  定义体: HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.isoOfHomotopyEquiv, homotopyEquiv, isoOfHomotopyEquiv
-/
def InjectiveResolution.iso {X : C} (I : InjectiveResolution X) :
    (injectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj I.cocomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `InjectiveResolution.iso_hom_naturality` / 引理 `InjectiveResolution.iso_hom_naturality`

English:
lemma InjectiveResolution.iso_hom_naturality
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  apply HomotopyCategory.eq_of_homotopy
  apply descHomotopy f
  all_goals aesop

@[reassoc]

中文:
引理 InjectiveResolution.iso_hom_naturality
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  apply HomotopyCategory.eq_of_homotopy
  apply descHomotopy f
  all_goals aesop

@[reassoc]

Depends on / 依赖: HomotopyCategory, HomotopyCategory.eq_of_homotopy, all_goals, descHomotopy, eq_of_homotopy
-/
lemma InjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (injectiveResolutions C).map f ≫ J.iso.hom =
      I.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  apply HomotopyCategory.eq_of_homotopy
  apply descHomotopy f
  all_goals aesop

@[reassoc]
/--
lemma `InjectiveResolution.iso_inv_naturality` / 引理 `InjectiveResolution.iso_inv_naturality`

English:
lemma InjectiveResolution.iso_inv_naturality
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← cancel_mono (J.iso).hom]; rw [Category.assoc]; rw [iso_hom_naturality f I J φ comm]; rw [Iso.inv_hom_id_assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

中文:
引理 InjectiveResolution.iso_inv_naturality
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← cancel_mono (J.iso).hom]; rw [Category.assoc]; rw [iso_hom_naturality f I J φ comm]; rw [Iso.inv_hom_id_assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.inv_hom_id, Iso.inv_hom_id_assoc, J.iso, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, iso_hom_naturality
-/
lemma InjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    I.iso.inv ≫ (injectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ J.iso.inv := by
  rw [← cancel_mono (J.iso).hom]; rw [Category.assoc]; rw [iso_hom_naturality f I J φ comm]; rw [Iso.inv_hom_id_assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

end

section

variable [Abelian C] [EnoughInjectives C]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exact_f_d` / 定理 `exact_f_d`

English:
theorem exact_f_d
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  let α : ShortComplex.mk f (cokernel.π f) (by simp) ⟶ ShortComplex.mk f (d f) (by simp) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Injective.ι _ }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_g_is_cokernel
  apply cokernelIsCokernel

中文:
定理 exact_f_d
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  let α : ShortComplex.mk f (cokernel.π f) (by simp) ⟶ ShortComplex.mk f (d f) (by simp) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Injective.ι _ }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_g_is_cokernel
  apply cokernelIsCokernel

Depends on / 依赖: Injective, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, ShortComplex.exact_of_g_is_cokernel, ShortComplex.mk, cokernel, cokernelIsCokernel, exact_iff_of_epi_of_isIso_of_mono, exact_of_g_is_cokernel
-/
theorem exact_f_d {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (d f) (by simp)).Exact := by
  let α : ShortComplex.mk f (cokernel.π f) (by simp) ⟶ ShortComplex.mk f (d f) (by simp) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Injective.ι _ }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_g_is_cokernel
  apply cokernelIsCokernel

end

namespace InjectiveResolution

/-!
Our goal is to define `InjectiveResolution.of Z : InjectiveResolution Z`.
The `0`-th object in this resolution will just be `Injective.under Z`,
i.e. an arbitrarily chosen injective object with a map from `Z`.
After that, we build the `n+1`-st object as `Injective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `Injective.d`.
-/


variable [Abelian C] [EnoughInjectives C] (Z : C)

-- The construction of the injective resolution `of` would be very, very slow
-- if it were not broken into separate definitions and lemmas

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofCocomplex` / `ofCocomplex` 的定义

English:
definition ofCocomplex
  signature: : CochainComplex C Nat
  body: CochainComplex.mk' (Injective.under Z) (Injective.syzygies (Injective.ι Z))
    (Injective.d (Injective.ι Z)) fun f => ⟨_, Injective.d f, by simp⟩

中文:
定义 ofCocomplex
  签名: : CochainComplex C 自然数
  定义体: CochainComplex.mk' (Injective.under Z) (Injective.syzygies (Injective.ι Z))
    (Injective.d (Injective.ι Z)) fun f => ⟨_, Injective.d f, by simp⟩

Depends on / 依赖: CochainComplex, CochainComplex.mk, Injective, Injective.d, Injective.syzygies, Injective.under, syzygies
-/
def ofCocomplex : CochainComplex C Nat :=
  CochainComplex.mk' (Injective.under Z) (Injective.syzygies (Injective.ι Z))
    (Injective.d (Injective.ι Z)) fun f => ⟨_, Injective.d f, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofCocomplex_d_0_1` / 引理 `ofCocomplex_d_0_1`

English:
lemma ofCocomplex_d_0_1
  proof: by
  simp [ofCocomplex]

中文:
引理 ofCocomplex_d_0_1
  证明: by
  simp [ofCocomplex]

Depends on / 依赖: ofCocomplex
-/
lemma ofCocomplex_d_0_1 :
    (ofCocomplex Z).d 0 1 = d (Injective.ι Z) := by
  simp [ofCocomplex]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofCocomplex_exactAt_succ` / 引理 `ofCocomplex_exactAt_succ`

English:
lemma ofCocomplex_exactAt_succ
  given: (n : Nat)
  proof: by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofCocomplex,
    CochainComplex.mk', CochainComplex.mk, CochainComplex.of_d]
  match n with
  | 0 => apply exact_f_d ((CochainComplex.mk

中文:
引理 ofCocomplex_exactAt_succ
  条件: (n : 自然数)
  证明: by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofCocomplex,
    CochainComplex.mk', CochainComplex.mk, CochainComplex.of_d]
  match n with
  | 0 => apply exact_f_d ((CochainComplex.mk

Depends on / 依赖: CochainComplex, CochainComplex.mk, CochainComplex.mkAux, CochainComplex.of_d, HomologicalComplex, HomologicalComplex.exactAt_iff, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, Injective, exactAt_iff, exact_f_d, ofCocomplex, of_d, shortComplexFunctor
-/
lemma ofCocomplex_exactAt_succ (n : Nat) :
    (ofCocomplex Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofCocomplex,
    CochainComplex.mk', CochainComplex.mk, CochainComplex.of_d]
  match n with
  | 0 => apply exact_f_d ((CochainComplex.mkAux _ _ _
      (d (Injective.ι Z)) (d (d (Injective.ι Z))) _ _ 0).f)
  | n + 1 => apply exact_f_d ((CochainComplex.mkAux _ _ _
      (d (Injective.ι Z)) (d (d (Injective.ι Z))) _ _ (n + 1)).f)

set_option backward.isDefEq.respectTransparency.types false in
instance (n : Nat) : Injective ((ofCocomplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Injective.injective_under

set_option backward.isDefEq.respectTransparency false in
/-- In any abelian category with enough injectives,
`InjectiveResolution.of Z` constructs an injective resolution of the object `Z`.
-/
irreducible_def of : InjectiveResolution Z where
  cocomplex := ofCocomplex Z
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨Injective.ι Z,
    by rw [ofCocomplex_d_0_1, cokernel.condition_assoc, zero_comp]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨exact_f_d (Injective.ι Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
          (by simp [ofCocomplex])
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt]
      · apply ofCocomplex_exactAt_succ
      · apply CochainComplex.exactAt_succ_single_obj⟩

instance (priority := 100) (Z : C) : HasInjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) : HasInjectiveResolutions C where out _ := inferInstance

end InjectiveResolution

variable [Abelian C]

/--
Definition of `InjectivePresentation.shortComplex` / `InjectivePresentation.shortComplex` 的定义

English:
abbreviation InjectivePresentation.shortComplex
  body: ShortComplex.mk ip.f (Limits.cokernel.π ip.f) (Limits.cokernel.condition ip.f)

中文:
缩写 InjectivePresentation.shortComplex
  定义体: ShortComplex.mk ip.f (Limits.cokernel.π ip.f) (Limits.cokernel.condition ip.f)

Depends on / 依赖: Limits, Limits.cokernel, Limits.cokernel.condition, ShortComplex, ShortComplex.mk, cokernel, condition, ip.f
-/
noncomputable abbrev InjectivePresentation.shortComplex
    {X : C} (ip : InjectivePresentation X) : ShortComplex C :=
  ShortComplex.mk ip.f (Limits.cokernel.π ip.f) (Limits.cokernel.condition ip.f)

/--
theorem `InjectivePresentation.shortExact_shortComplex` / 定理 `InjectivePresentation.shortExact_shortComplex`

English:
theorem InjectivePresentation.shortExact_shortComplex
  statement: {X : C}
  proof: { exact := ShortComplex.exact_cokernel ip.f }

中文:
定理 InjectivePresentation.shortExact_shortComplex
  结论: {X : C}
  证明: { exact := ShortComplex.exact_cokernel ip.f }

Depends on / 依赖: ShortComplex, ShortComplex.exact_cokernel, exact_cokernel, ip.f
-/
theorem InjectivePresentation.shortExact_shortComplex {X : C}
    (ip : InjectivePresentation X) : ip.shortComplex.ShortExact :=
  { exact := ShortComplex.exact_cokernel ip.f }

end CategoryTheory
