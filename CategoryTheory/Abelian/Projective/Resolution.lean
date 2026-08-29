/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Tactic.SuppressCompilation

/-!
# Abelian categories with enough projectives have projective resolutions

## Main results
When the underlying category is abelian:
* `CategoryTheory.ProjectiveResolution.lift`: Given `P : ProjectiveResolution X` and
  `Q : ProjectiveResolution Y`, any morphism `X ⟶ Y` admits a lifting to a chain map
  `P.complex ⟶ Q.complex`. It is a lifting in the sense that `P.ι` intertwines the lift and
  the original morphism, see `CategoryTheory.ProjectiveResolution.lift_commutes`.
* `CategoryTheory.ProjectiveResolution.liftHomotopy`: Any two such lifts are homotopic.
* `CategoryTheory.ProjectiveResolution.homotopyEquiv`: Any two projective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.projectiveResolutions`: If every object admits a projective resolution, we can
  construct a functor `projectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`.

* `CategoryTheory.exact_d_f`: `Projective.d f` and `f` are exact.
* `CategoryTheory.ProjectiveResolution.of`: Hence, starting from an epimorphism `P ⟶ X`, where `P`
  is projective, we can apply `Projective.d` repeatedly to obtain a projective resolution of `X`.
-/

@[expose] public section

suppress_compilation

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Category Limits Projective


namespace ProjectiveResolution

section

variable [HasZeroObject C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftFZero` / `liftFZero` 的定义

English:
definition liftFZero
  signature: {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z)
  body: Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

中文:
定义 liftFZero
  签名: {Y Z : C} (f : Y ⟶ Z) (P : 投射消解 Y) (Q : 投射消解 Z)
  定义体: Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

Depends on / 依赖: Projective, Projective.factorThru, factorThru
-/
def liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

end

section Abelian

variable [Abelian C]

/--
lemma `exact₀` / 引理 `exact₀`

English:
lemma exact₀
  given: {Z : C} (P : ProjectiveResolution Z)
  proof: ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

中文:
引理 exact₀
  条件: {Z : C} (P : 投射消解 Z)
  证明: ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

Depends on / 依赖: P.isColimitCokernelCofork, ShortComplex, ShortComplex.exact_of_g_is_cokernel, exact_of_g_is_cokernel, isColimitCokernelCofork
-/
lemma exact₀ {Z : C} (P : ProjectiveResolution Z) :
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftFOne` / `liftFOne` 的定义

English:
definition liftFOne
  signature: {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z)
  body: Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q) (by simp [liftFZero])

@[simp]

中文:
定义 liftFOne
  签名: {Y Z : C} (f : Y ⟶ Z) (P : 投射消解 Y) (Q : 投射消解 Z)
  定义体: Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q) (by simp [liftFZero])

@[simp]

Depends on / 依赖: P.complex.d, Q.exact, complex, liftFZero, liftFromProjective
-/
def liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q) (by simp [liftFZero])

@[simp]
/--
theorem `liftFOne_zero_comm` / 定理 `liftFOne_zero_comm`

English:
theorem liftFOne_zero_comm
  statement: {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
  proof: by
  apply Q.exact₀.liftFromProjective_comp

中文:
定理 liftFOne_zero_comm
  结论: {Y Z : C} (f : Y ⟶ Z) (P : 投射消解 Y)
  证明: by
  apply Q.exact₀.liftFromProjective_comp

Depends on / 依赖: Functor, Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension, Q.exact, isDense_iff_nonempty_isPointwiseLeftKanExtension, isLeftKanExtension, liftFromProjective_comp, some.isLeftKanExtension
-/
theorem liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) :
    liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q := by
  apply Q.exact₀.liftFromProjective_comp

/--
Definition of `liftFSucc` / `liftFSucc` 的定义

English:
definition liftFSucc
  signature: {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : Nat)
  body: ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

中文:
定义 liftFSucc
  签名: {Y Z : C} (P : 投射消解 Y) (Q : 投射消解 Z) (n : 自然数)
  定义体: ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

Depends on / 依赖: Functor, Functor.IsDense.isDenseAt, IsDense, P.complex.d, Q.exact_succ, complex, exact_succ, hasPointwiseLeftKanExtensionAt, isDenseAt, liftFromProjective, liftFromProjective_comp, some.hasPointwiseLeftKanExtensionAt
-/
def liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : Nat)
    (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z)
  body: ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

中文:
定义 lift
  签名: {Y Z : C} (f : Y ⟶ Z) (P : 投射消解 Y) (Q : 投射消解 Z)
  定义体: ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

Depends on / 依赖: ChainComplex, ChainComplex.mkHom, liftFOne, liftFOne_zero_comm, liftFSucc, liftFZero
-/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[reassoc (attr := simp)]
/--
theorem `lift_commutes` / 定理 `lift_commutes`

English:
theorem lift_commutes
  statement: {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
  proof: by
  ext
  simp [lift, liftFZero, liftFOne]

@[reassoc (attr := simp)]

中文:
定理 lift_commutes
  结论: {Y Z : C} (f : Y ⟶ Z) (P : 投射消解 Y)
  证明: by
  ext
  simp [lift, liftFZero, liftFOne]

@[reassoc (attr := simp)]

Depends on / 依赖: liftFOne, liftFZero
-/
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) : lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext
  simp [lift, liftFZero, liftFOne]

@[reassoc (attr := simp)]
/--
lemma `lift_commutes_zero` / 引理 `lift_commutes_zero`

English:
lemma lift_commutes_zero
  statement: {Y Z : C} (f : Y ⟶ Z)
  proof: (HomologicalComplex.congr_hom (lift_commutes f P Q) 0).trans (by simp)

中文:
引理 lift_commutes_zero
  结论: {Y Z : C} (f : Y ⟶ Z)
  证明: (HomologicalComplex.congr_hom (lift_commutes f P Q) 0).trans (by simp)

Depends on / 依赖: F.denseAt, HomologicalComplex, HomologicalComplex.congr_hom, congr_hom, denseAt, lift_commutes, precompOfFinal
-/
lemma lift_commutes_zero {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    (lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
  (HomologicalComplex.congr_hom (lift_commutes f P Q) 0).trans (by simp)

/--
Definition of `liftHomotopyZeroZero` / `liftHomotopyZeroZero` 的定义

English:
definition liftHomotopyZeroZero
  signature: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  body: Q.exact₀.liftFromProjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]

中文:
定义 liftHomotopyZeroZero
  签名: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  定义体: Q.exact₀.liftFromProjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.f, Q.exact, congr_arg, congr_fun, liftFromProjective
-/
def liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
/--
lemma `liftHomotopyZeroZero_comp` / 引理 `liftHomotopyZeroZero_comp`

English:
lemma liftHomotopyZeroZero_comp
  statement: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  proof: Q.exact₀.liftFromProjective_comp _ _

中文:
引理 liftHomotopyZeroZero_comp
  结论: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  证明: Q.exact₀.liftFromProjective_comp _ _

Depends on / 依赖: DenseAt, DenseAt.ofIso, F.denseAt, G.asEquivalence.counitIso.symm.app, G.inv.obj, G.obj, Q.exact, asEquivalence, counitIso, denseAt, e.symm, liftFromProjective_comp, postcompEquivalence
-/
lemma liftHomotopyZeroZero_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

/--
Definition of `liftHomotopyZeroOne` / `liftHomotopyZeroOne` 的定义

English:
definition liftHomotopyZeroOne
  signature: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  body: (Q.exact_succ 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
              liftHomotopyZeroZero_comp, sub_self])

@[reassoc (attr := simp)]

中文:
定义 liftHomotopyZeroOne
  签名: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  定义体: (Q.exact_succ 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
              liftHomotopyZeroZero_comp, sub_self])

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.comm, P.complex.d, Preadditive, Preadditive.sub_comp, Q.exact_succ, complex, exact_succ, liftFromProjective, liftHomotopyZeroZero, liftHomotopyZeroZero_comp, sub_comp, sub_self
-/
def liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
              liftHomotopyZeroZero_comp, sub_self])

@[reassoc (attr := simp)]
/--
lemma `liftHomotopyZeroOne_comp` / 引理 `liftHomotopyZeroOne_comp`

English:
lemma liftHomotopyZeroOne_comp
  statement: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  proof: (Q.exact_succ 0).liftFromProjective_comp _ _

中文:
引理 liftHomotopyZeroOne_comp
  结论: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  证明: (Q.exact_succ 0).liftFromProjective_comp _ _

Depends on / 依赖: Q.exact_succ, exact_succ, liftFromProjective_comp
-/
lemma liftHomotopyZeroOne_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm :=
  (Q.exact_succ 0).liftFromProjective_comp _ _

/--
Definition of `liftHomotopyZeroSucc` / `liftHomotopyZeroSucc` 的定义

English:
definition liftHomotopyZeroSucc
  signature: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  body: (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]

中文:
定义 liftHomotopyZeroSucc
  签名: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  定义体: (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]

Depends on / 依赖: P.complex.d, Q.exact_succ, complex, exact_succ, liftFromProjective
-/
def liftHomotopyZeroSucc {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : Nat) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]
/--
lemma `liftHomotopyZeroSucc_comp` / 引理 `liftHomotopyZeroSucc_comp`

English:
lemma liftHomotopyZeroSucc_comp
  statement: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  proof: (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

中文:
引理 liftHomotopyZeroSucc_comp
  结论: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  证明: (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

Depends on / 依赖: Q.exact_succ, exact_succ, liftFromProjective_comp
-/
lemma liftHomotopyZeroSucc_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : Nat) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    liftHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - P.complex.d _ _ ≫ g' :=
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

/--
Definition of `liftHomotopyZero` / `liftHomotopyZero` 的定义

English:
definition liftHomotopyZero
  signature: {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  body: Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp)
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩

中文:
定义 liftHomotopyZero
  签名: {Y Z : C} {P : 投射消解 Y} {Q : 投射消解 Z}
  定义体: Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp)
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩

Depends on / 依赖: Homotopy, Homotopy.mkInductive, liftHomotopyZeroOne, liftHomotopyZeroSucc, liftHomotopyZeroZero, mkInductive
-/
def liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp)
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩

/--
Definition of `liftHomotopy` / `liftHomotopy` 的定义

English:
definition liftHomotopy
  signature: {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  body: Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))

中文:
定义 liftHomotopy
  签名: {Y Z : C} (f : Y ⟶ Z) {P : 投射消解 Y} {Q : 投射消解 Z}
  定义体: Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))

Depends on / 依赖: Homotopy, Homotopy.equivSubZero.invFun, equivSubZero, g_comm, h_comm, invFun, liftHomotopyZero
-/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))

/--
Definition of `liftIdHomotopy` / `liftIdHomotopy` 的定义

English:
definition liftIdHomotopy
  signature: (X : C) (P : ProjectiveResolution X)
  body: by
  apply liftHomotopy (𝟙 X) <;> simp

中文:
定义 liftIdHomotopy
  签名: (X : C) (P : 投射消解 X)
  定义体: by
  apply liftHomotopy (𝟙 X) <;> simp

Depends on / 依赖: liftHomotopy
-/
def liftIdHomotopy (X : C) (P : ProjectiveResolution X) :
    Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) := by
  apply liftHomotopy (𝟙 X) <;> simp

/--
Definition of `liftCompHomotopy` / `liftCompHomotopy` 的定义

English:
definition liftCompHomotopy
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X)
  body: by
  apply liftHomotopy (f ≫ g) <;> simp

中文:
定义 liftCompHomotopy
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : 投射消解 X)
  定义体: by
  apply liftHomotopy (f ≫ g) <;> simp

Depends on / 依赖: liftHomotopy
-/
def liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) :
    Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  apply liftHomotopy (f ≫ g) <;> simp

-- We don't care about the actual definitions of these homotopies.
/--
Definition of `homotopyEquiv` / `homotopyEquiv` 的定义

English:
definition homotopyEquiv
  signature: {X : C} (P Q : ProjectiveResolution X)
  body: lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
homotopyHomInvId := (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans by
    simpa [id_comp] using liftIdHomotopy _ _
homotopyInvHomId := (liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans by
    simpa [id_comp] using liftIdHomotopy _ _

@[reassoc (attr := simp)]

中文:
定义 homotopyEquiv
  签名: {X : C} (P Q : 投射消解 X)
  定义体: lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
homotopyHomInvId := (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans by
    simpa [id_comp] using liftIdHomotopy _ _
homotopyInvHomId := (liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans by
    simpa [id_comp] using liftIdHomotopy _ _

@[reassoc (attr := simp)]
-/
def homotopyEquiv {X : C} (P Q : ProjectiveResolution X) :
    HomotopyEquiv P.complex Q.complex where
  hom := lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
homotopyHomInvId := (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans by
    simpa [id_comp] using liftIdHomotopy _ _
homotopyInvHomId := (liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans by
    simpa [id_comp] using liftIdHomotopy _ _

@[reassoc (attr := simp)]
/--
theorem `homotopyEquiv_hom_π` / 定理 `homotopyEquiv_hom_π`

English:
theorem homotopyEquiv_hom_π
  given: {X : C} (P Q : ProjectiveResolution X)
  proof: by simp [homotopyEquiv]

@[reassoc (attr := simp)]

中文:
定理 homotopyEquiv_hom_π
  条件: {X : C} (P Q : 投射消解 X)
  证明: by simp [homotopyEquiv]

@[reassoc (attr := simp)]

Depends on / 依赖: homotopyEquiv
-/
theorem homotopyEquiv_hom_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).hom ≫ Q.π = P.π := by simp [homotopyEquiv]

@[reassoc (attr := simp)]
/--
theorem `homotopyEquiv_inv_π` / 定理 `homotopyEquiv_inv_π`

English:
theorem homotopyEquiv_inv_π
  given: {X : C} (P Q : ProjectiveResolution X)
  proof: by simp [homotopyEquiv]

中文:
定理 homotopyEquiv_inv_π
  条件: {X : C} (P Q : 投射消解 X)
  证明: by simp [homotopyEquiv]

Depends on / 依赖: homotopyEquiv
-/
theorem homotopyEquiv_inv_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).inv ≫ P.π = Q.π := by simp [homotopyEquiv]

end Abelian

end ProjectiveResolution

/--
Definition of `projectiveResolution` / `projectiveResolution` 的定义

English:
abbreviation projectiveResolution
  signature: (Z : C) [HasZeroObject C]
  body: (HasProjectiveResolution.out (Z := Z)).some

中文:
缩写 projectiveResolution
  签名: (Z : C) [有ZeroObject C]
  定义体: (HasProjectiveResolution.out (Z := Z)).some

Depends on / 依赖: HasProjectiveResolution, HasProjectiveResolution.out
-/
abbrev projectiveResolution (Z : C) [HasZeroObject C]
    [HasZeroMorphisms C] [HasProjectiveResolution Z] :
    ProjectiveResolution Z :=
  (HasProjectiveResolution.out (Z := Z)).some

variable (C)
variable [Abelian C]

section
variable [HasProjectiveResolutions C]

/--
Definition of `projectiveResolutions` / `projectiveResolutions` 的定义

English:
definition projectiveResolutions
  signature: : C ⥤ HomotopyCategory C (ComplexShape.down Nat) where
  body: (HomotopyCategory.quotient _ _).obj (projectiveResolution X).complex
  map f := (HomotopyCategory.quotient _ _).map (ProjectiveResolution.lift f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomo

中文:
定义 projectiveResolutions
  签名: : C ⥤ HomotopyCategory C (余mplexShape.down 自然数) where
  定义体: (HomotopyCategory.quotient _ _).obj (projectiveResolution X).complex
  map f := (HomotopyCategory.quotient _ _).map (ProjectiveResolution.lift f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomo

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, complex, projectiveResolution, quotient
-/
def projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down Nat) where
  obj X := (HomotopyCategory.quotient _ _).obj (projectiveResolution X).complex
  map f := (HomotopyCategory.quotient _ _).map (ProjectiveResolution.lift f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftCompHomotopy

variable {C}

/--
Definition of `ProjectiveResolution.iso` / `ProjectiveResolution.iso` 的定义

English:
definition ProjectiveResolution.iso
  signature: {X : C} (P : ProjectiveResolution X)
  body: HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

中文:
定义 投射消解.iso
  签名: {X : C} (P : 投射消解 X)
  定义体: HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.isoOfHomotopyEquiv, homotopyEquiv, isoOfHomotopyEquiv
-/
def ProjectiveResolution.iso {X : C} (P : ProjectiveResolution X) :
    (projectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj P.complex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ProjectiveResolution.iso_inv_naturality` / 引理 `ProjectiveResolution.iso_inv_naturality`

English:
lemma ProjectiveResolution.iso_inv_naturality
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  apply HomotopyCategory.eq_of_homotopy
  apply liftHomotopy f
  all_goals
    cat_disch

@[reassoc]

中文:
引理 投射消解.iso_inv_naturality
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  apply HomotopyCategory.eq_of_homotopy
  apply liftHomotopy f
  all_goals
    cat_disch

@[reassoc]

Depends on / 依赖: HomotopyCategory, HomotopyCategory.eq_of_homotopy, all_goals, cat_disch, eq_of_homotopy, liftHomotopy
-/
lemma ProjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    P.iso.inv ≫ (projectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ Q.iso.inv := by
  apply HomotopyCategory.eq_of_homotopy
  apply liftHomotopy f
  all_goals
    cat_disch

@[reassoc]
/--
lemma `ProjectiveResolution.iso_hom_naturality` / 引理 `ProjectiveResolution.iso_hom_naturality`

English:
lemma ProjectiveResolution.iso_hom_naturality
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← cancel_epi (P.iso).inv]; rw [iso_inv_naturality_assoc f P Q φ comm]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 投射消解.iso_hom_naturality
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← cancel_epi (P.iso).inv]; rw [iso_inv_naturality_assoc f P Q φ comm]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, P.iso, cancel_epi, comp_id, inv_hom_id, inv_hom_id_assoc, iso_inv_naturality_assoc
-/
lemma ProjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    (projectiveResolutions C).map f ≫ Q.iso.hom =
      P.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  rw [← cancel_epi (P.iso).inv]; rw [iso_inv_naturality_assoc f P Q φ comm]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

end

variable [EnoughProjectives C]

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/--
theorem `exact_d_f` / 定理 `exact_d_f`

English:
theorem exact_d_f
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  let α : ShortComplex.mk (d f) f (by simp) ⟶ ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := Projective.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

中文:
定理 exact_d_f
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  let α : ShortComplex.mk (d f) f (by simp) ⟶ ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := Projective.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

Depends on / 依赖: Projective, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, ShortComplex.exact_of_f_is_kernel, ShortComplex.mk, exact_iff_of_epi_of_isIso_of_mono, exact_of_f_is_kernel, kernel, kernelIsKernel
-/
theorem exact_d_f {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (d f) f (by simp)).Exact := by
  let α : ShortComplex.mk (d f) f (by simp) ⟶ ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := Projective.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `Projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `Projective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `Projective.d`.
-/

variable {C}
variable (Z : C)

-- The construction of the projective resolution `of` would be very, very slow
-- if it were not broken into separate definitions and lemmas

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofComplex` / `ofComplex` 的定义

English:
definition ofComplex
  signature: : ChainComplex C Nat
  body: ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) (fun f => ⟨_, Projective.d f, by simp⟩)

中文:
定义 ofComplex
  签名: : 链复形 C 自然数
  定义体: ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) (fun f => ⟨_, Projective.d f, by simp⟩)

Depends on / 依赖: ChainComplex, ChainComplex.mk, Projective, Projective.d, Projective.over, Projective.syzygies, syzygies
-/
def ofComplex : ChainComplex C Nat :=
  ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) (fun f => ⟨_, Projective.d f, by simp⟩)

/--
lemma `ofComplex_d_1_0` / 引理 `ofComplex_d_1_0`

English:
lemma ofComplex_d_1_0
  proof: by
  simp [ofComplex]

中文:
引理 ofComplex_d_1_0
  证明: by
  simp [ofComplex]

Depends on / 依赖: ofComplex
-/
lemma ofComplex_d_1_0 :
    (ofComplex Z).d 1 0 = d (Projective.π Z) := by
  simp [ofComplex]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofComplex_exactAt_succ` / 引理 `ofComplex_exactAt_succ`

English:
lemma ofComplex_exactAt_succ
  given: (n : Nat)
  proof: by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  -- TODO: this should just be apply exact_d_f so something is miss

中文:
引理 ofComplex_exactAt_succ
  条件: (n : 自然数)
  证明: by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  -- TODO: this should just be apply exact_d_f so something is miss

Depends on / 依赖: ChainComplex, ChainComplex.mk, ChainComplex.of_d, HomologicalComplex, HomologicalComplex.exactAt_iff, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, exactAt_iff, ofComplex, of_d, shortComplexFunctor
-/
lemma ofComplex_exactAt_succ (n : Nat) :
    (ofComplex Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  -- TODO: this should just be apply exact_d_f so something is missing
  match n with
  | 0 => apply exact_d_f
  | n + 1 => apply exact_d_f

set_option backward.isDefEq.respectTransparency.types false in
instance (n : Nat) : Projective ((ofComplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Projective.projective_over

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
irreducible_def of : ProjectiveResolution Z where
  complex := ofComplex Z
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨Projective.π Z, by
          rw [ofComplex_d_1_0]; rw [assoc]; rw [kernel.condition]; rw [comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_d_f (Projective.π Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [ofComplex]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply ofComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

instance (priority := 100) (Z : C) : HasProjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) : HasProjectiveResolutions C where out _ := inferInstance

end ProjectiveResolution

end CategoryTheory
