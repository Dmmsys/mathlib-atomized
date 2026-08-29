/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Galois objects in Galois categories

We define when a connected object of a Galois category `C` is Galois in a fiber-functor-independent
way and show equivalent characterisations.

## Main definitions

* `IsGalois` : Connected object `X` of `C` such that `X / Aut X` is terminal.

## Main results

* `galois_iff_pretransitive` : A connected object `X` is Galois if and only if `Aut X`
                               acts transitively on `F.obj X` for a fiber functor `F`.

-/

@[expose] public section
universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

noncomputable instance {G : Type v} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) FintypeCat.incl.{w} := by
  choose G' hg hf e using Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv (Classical.choice e).toSingleObjEquiv.symm _

/--
Definition of `IsGalois` / `IsGalois` 的定义

English:
class IsGalois
  parameters: {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C)
  extends: IsConnected X
  axioms and operations (1):
    - quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

中文:
类 是Galois
  参数: {C : 类型u₁} [范畴.{u₂, u₁} C] [Galois范畴 C] (X : C)
  继承: 是连通 X
  公理与运算 (1 个):
    - quotientByAutTerminal : 非空 (是终止 <| colimit <| SingleObj.functor <| Aut.toEnd X)
-/
class IsGalois {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C) : Prop
    extends IsConnected X where
  quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

variable {C : Type u₁} [Category.{u₂, u₁} C]

/--
Instance `autMulFiber` / 实例 `autMulFiber`

English:
instance autMulFiber
  signature: (F : C ⥤ FintypeCat.{w}) (X : C)
  body: F.map σ.hom a
  one_smul a := by
    change F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    change F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

中文:
实例 autMulFiber
  签名: (F : C ⥤ FintypeCat.{w}) (X : C)
  定义体: F.map σ.hom a
  one_smul a := by
    change F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    change F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

Depends on / 依赖: F.map
-/
instance autMulFiber (F : C ⥤ FintypeCat.{w}) (X : C) : MulAction (Aut X) (F.obj X) where
  smul σ a := F.map σ.hom a
  one_smul a := by
    change F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    change F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/--
Definition of `quotientByAutTerminalEquivUniqueQuotient` / `quotientByAutTerminalEquivUniqueQuotient` 的定义

English:
definition quotientByAutTerminalEquivUniqueQuotient
  body: by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  · apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
      (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

中文:
定义 quotientByAutTerminalEquivUniqueQuotient
  定义体: by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  · apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
      (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

Depends on / 依赖: Aut.toEnd, Equiv.toIso, Equiv.trans, FintypeCat, FintypeCat.incl, IsTerminal, IsTerminal.isTerminalIffObj, SingleObj, SingleObj.Types.colimitEquivQuotient, SingleObj.functor, Types.isTerminalEquivUnique, asEmptyCone, colimit, colimitEquivQuotient, functor, isLimitEmptyConeEquiv, isTerminalEquivUnique, isTerminalIffObj, preservesColimitIso
-/
noncomputable def quotientByAutTerminalEquivUniqueQuotient
    (X : C) [IsConnected X] :
    IsTerminal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃
    Unique (MulAction.orbitRel.Quotient (Aut X) (F.obj X)) := by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  · apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
      (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

/--
lemma `isGalois_iff_aux` / 引理 `isGalois_iff_aux`

English:
lemma isGalois_iff_aux
  given: (X : C) [IsConnected X]
  proof: ⟨fun h => h.quotientByAutTerminal, fun h => ⟨h⟩⟩

中文:
引理 isGalois_iff_aux
  条件: (X : C) [是连通 X]
  证明: ⟨fun h => h.quotientByAutTerminal, fun h => ⟨h⟩⟩

Depends on / 依赖: Nonempty, Nonempty.intro, h.quotientByAutTerminal, quotientByAutTerminal
-/
lemma isGalois_iff_aux (X : C) [IsConnected X] :
    IsGalois X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X) :=
  ⟨fun h => h.quotientByAutTerminal, fun h => ⟨h⟩⟩

/--
theorem `isGalois_iff_pretransitive` / 定理 `isGalois_iff_pretransitive`

English:
theorem isGalois_iff_pretransitive
  given: (X : C) [IsConnected X]
  proof: by
  rw [isGalois_iff_aux]; rw [Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

中文:
定理 isGalois_iff_pretransitive
  条件: (X : C) [是连通 X]
  证明: by
  rw [isGalois_iff_aux]; rw [Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

Depends on / 依赖: Equiv.nonempty_congr, F.obj, MulAction, MulAction.pretransitive_iff_unique_quotient_of_nonempty, isGalois_iff_aux, nonempty_congr, pretransitive_iff_unique_quotient_of_nonempty, quotientByAutTerminalEquivUniqueQuotient
-/
theorem isGalois_iff_pretransitive (X : C) [IsConnected X] :
    IsGalois X ↔ MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [isGalois_iff_aux]; rw [Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

/--
Definition of `isTerminalQuotientOfIsGalois` / `isTerminalQuotientOfIsGalois` 的定义

English:
definition isTerminalQuotientOfIsGalois
  signature: (X : C) [IsGalois X]
  body: Nonempty.some IsGalois.quotientByAutTerminal

中文:
定义 isTerminalQuotientOfIsGalois
  签名: (X : C) [是Galois X]
  定义体: Nonempty.some IsGalois.quotientByAutTerminal

Depends on / 依赖: IsGalois, IsGalois.quotientByAutTerminal, Nonempty, Nonempty.intro, Nonempty.some, quotientByAutTerminal
-/
noncomputable def isTerminalQuotientOfIsGalois (X : C) [IsGalois X] :
IsTerminal colimit SingleObj.functor Aut.toEnd X :=
  Nonempty.some IsGalois.quotientByAutTerminal

/--
Instance `isPretransitive_of_isGalois` / 实例 `isPretransitive_of_isGalois`

English:
instance isPretransitive_of_isGalois
  signature: (X : C) [IsGalois X]
  body: by
  rw [← isGalois_iff_pretransitive]
  infer_instance

中文:
实例 isPretransitive_of_isGalois
  签名: (X : C) [是Galois X]
  定义体: by
  rw [← isGalois_iff_pretransitive]
  infer_instance

Depends on / 依赖: infer_instance, isGalois_iff_pretransitive
-/
instance isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [← isGalois_iff_pretransitive]
  infer_instance

/--
lemma `stabilizer_normal_of_isGalois` / 引理 `stabilizer_normal_of_isGalois`

English:
lemma stabilizer_normal_of_isGalois
  given: (X : C) [IsGalois X] (x : F.obj X)
  proof: by
    rw [MulAction.mem_stabilizer_iff]
    change g • n • (g⁻¹ • x) = x
    have : exists (φ : Aut X), F.map φ.hom x = g⁻¹ • x :=
      MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
    obtain ⟨φ, h⟩ := this
    rw [← h]; rw [mulAction_naturality]; rw [ninstab]; rw [h]
    simp

中文:
引理 stabilizer_normal_of_isGalois
  条件: (X : C) [是Galois X] (x : F.obj X)
  证明: by
    rw [MulAction.mem_stabilizer_iff]
    change g • n • (g⁻¹ • x) = x
    have : exists (φ : Aut X), F.map φ.hom x = g⁻¹ • x :=
      MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
    obtain ⟨φ, h⟩ := this
    rw [← h]; rw [mulAction_naturality]; rw [ninstab]; rw [h]
    simp

Depends on / 依赖: F.map, IsPretransitive, MulAction, MulAction.IsPretransitive.exists_smul_eq, MulAction.mem_stabilizer_iff, exists_smul_eq, mem_stabilizer_iff, mulAction_naturality, ninstab
-/
lemma stabilizer_normal_of_isGalois (X : C) [IsGalois X] (x : F.obj X) :
    Subgroup.Normal (MulAction.stabilizer (Aut F) x) where
  conj_mem n ninstab g := by
    rw [MulAction.mem_stabilizer_iff]
    change g • n • (g⁻¹ • x) = x
    have : exists (φ : Aut X), F.map φ.hom x = g⁻¹ • x :=
      MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
    obtain ⟨φ, h⟩ := this
    rw [← h]; rw [mulAction_naturality]; rw [ninstab]; rw [h]
    simp

/--
theorem `evaluation_aut_surjective_of_isGalois` / 定理 `evaluation_aut_surjective_of_isGalois`

English:
theorem evaluation_aut_surjective_of_isGalois
  given: (A : C) [IsGalois A] (a : F.obj A)
  proof: MulAction.IsPretransitive.exists_smul_eq a

中文:
定理 evaluation_aut_surjective_of_isGalois
  条件: (A : C) [是Galois A] (a : F.obj A)
  证明: MulAction.IsPretransitive.exists_smul_eq a

Depends on / 依赖: IsPretransitive, MulAction, MulAction.IsPretransitive.exists_smul_eq, exists_smul_eq
-/
theorem evaluation_aut_surjective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Surjective (fun f : Aut A => F.map f.hom a) :=
  MulAction.IsPretransitive.exists_smul_eq a

/--
theorem `evaluation_aut_bijective_of_isGalois` / 定理 `evaluation_aut_bijective_of_isGalois`

English:
theorem evaluation_aut_bijective_of_isGalois
  given: (A : C) [IsGalois A] (a : F.obj A)
  proof: ⟨evaluation_aut_injective_of_isConnected F A a, evaluation_aut_surjective_of_isGalois F A a⟩

中文:
定理 evaluation_aut_bijective_of_isGalois
  条件: (A : C) [是Galois A] (a : F.obj A)
  证明: ⟨evaluation_aut_injective_of_isConnected F A a, evaluation_aut_surjective_of_isGalois F A a⟩

Depends on / 依赖: evaluation_aut_injective_of_isConnected, evaluation_aut_surjective_of_isGalois
-/
theorem evaluation_aut_bijective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Bijective (fun f : Aut A => F.map f.hom a) :=
  ⟨evaluation_aut_injective_of_isConnected F A a, evaluation_aut_surjective_of_isGalois F A a⟩

/--
Definition of `evaluationEquivOfIsGalois` / `evaluationEquivOfIsGalois` 的定义

English:
definition evaluationEquivOfIsGalois
  signature: (A : C) [IsGalois A] (a : F.obj A)
  body: Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois F A a)

@[simp]

中文:
定义 evaluationEquivOfIsGalois
  签名: (A : C) [是Galois A] (a : F.obj A)
  定义体: Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois F A a)

@[simp]

Depends on / 依赖: Equiv.ofBijective, evaluation_aut_bijective_of_isGalois, ofBijective
-/
noncomputable def evaluationEquivOfIsGalois (A : C) [IsGalois A] (a : F.obj A) : Aut A ≃ F.obj A :=
  Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois F A a)

@[simp]
/--
lemma `evaluationEquivOfIsGalois_apply` / 引理 `evaluationEquivOfIsGalois_apply`

English:
lemma evaluationEquivOfIsGalois_apply
  given: (A : C) [IsGalois A] (a : F.obj A) (φ : Aut A)
  proof: rfl

@[simp]

中文:
引理 evaluationEquivOfIsGalois_apply
  条件: (A : C) [是Galois A] (a : F.obj A) (φ : Aut A)
  证明: rfl

@[simp]
-/
lemma evaluationEquivOfIsGalois_apply (A : C) [IsGalois A] (a : F.obj A) (φ : Aut A) :
    evaluationEquivOfIsGalois F A a φ = F.map φ.hom a :=
  rfl

@[simp]
/--
lemma `evaluationEquivOfIsGalois_symm_fiber` / 引理 `evaluationEquivOfIsGalois_symm_fiber`

English:
lemma evaluationEquivOfIsGalois_symm_fiber
  given: (A : C) [IsGalois A] (a b : F.obj A)
  proof: by
  change (evaluationEquivOfIsGalois F A a) _ = _
  simp

中文:
引理 evaluationEquivOfIsGalois_symm_fiber
  条件: (A : C) [是Galois A] (a b : F.obj A)
  证明: by
  change (evaluationEquivOfIsGalois F A a) _ = _
  simp

Depends on / 依赖: evaluationEquivOfIsGalois
-/
lemma evaluationEquivOfIsGalois_symm_fiber (A : C) [IsGalois A] (a b : F.obj A) :
    F.map ((evaluationEquivOfIsGalois F A a).symm b).hom a = b := by
  change (evaluationEquivOfIsGalois F A a) _ = _
  simp

section AutMap

/--
lemma `exists_autMap` / 引理 `exists_autMap`

English:
lemma exists_autMap
  given: {A B : C} (f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A)
  proof: by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  refine ⟨?_, ?_, ?_⟩
  · exact (evaluationEquivOfIsGalois F B (F.map f a)).symm (F.map (σ.hom ≫ f) a)
  · apply evaluation_injective_of_isConnected F A B a
    simp
  · intro τ hτ
    apply evaluation_aut_injective_of_isConnected F B (F.map f a)
    simpa using ConcreteCategory.congr_hom (F.congr_map hτ) a

中文:
引理 存在_autMap
  条件: {A B : C} (f : A ⟶ B) [是连通 A] [是Galois B] (σ : Aut A)
  证明: by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  refine ⟨?_, ?_, ?_⟩
  · exact (evaluationEquivOfIsGalois F B (F.map f a)).symm (F.map (σ.hom ≫ f) a)
  · apply evaluation_injective_of_isConnected F A B a
    simp
  · intro τ hτ
    apply evaluation_aut_injective_of_isConnected F B (F.map f a)
    simpa using ConcreteCategory.congr_hom (F.congr_map hτ) a

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.congr_map, F.map, GaloisCategory, GaloisCategory.getFiberFunctor, congr_hom, congr_map, evaluationEquivOfIsGalois, evaluation_aut_injective_of_isConnected, evaluation_injective_of_isConnected, getFiberFunctor, nonempty_fiber_of_isConnected
-/
lemma exists_autMap {A B : C} (f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A) :
    exists! (τ : Aut B), f ≫ τ.hom = σ.hom ≫ f := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  refine ⟨?_, ?_, ?_⟩
  · exact (evaluationEquivOfIsGalois F B (F.map f a)).symm (F.map (σ.hom ≫ f) a)
  · apply evaluation_injective_of_isConnected F A B a
    simp
  · intro τ hτ
    apply evaluation_aut_injective_of_isConnected F B (F.map f a)
    simpa using ConcreteCategory.congr_hom (F.congr_map hτ) a

/--
Definition of `autMap` / `autMap` 的定义

English:
definition autMap
  signature: {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
  body: (exists_autMap f σ).choose

@[simp]

中文:
定义 autMap
  签名: {A B : C} [是连通 A] [是Galois B] (f : A ⟶ B) (σ : Aut A)
  定义体: (exists_autMap f σ).choose

@[simp]

Depends on / 依赖: exists_autMap
-/
noncomputable def autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) :
    Aut B :=
  (exists_autMap f σ).choose

@[simp]
/--
lemma `comp_autMap` / 引理 `comp_autMap`

English:
lemma comp_autMap
  given: {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
  proof: (exists_autMap f σ).choose_spec.left

@[simp]

中文:
引理 comp_autMap
  条件: {A B : C} [是连通 A] [是Galois B] (f : A ⟶ B) (σ : Aut A)
  证明: (exists_autMap f σ).choose_spec.left

@[simp]

Depends on / 依赖: choose_spec, choose_spec.left, exists_autMap
-/
lemma comp_autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) :
    f ≫ (autMap f σ).hom = σ.hom ≫ f :=
  (exists_autMap f σ).choose_spec.left

@[simp]
/--
lemma `comp_autMap_apply` / 引理 `comp_autMap_apply`

English:
lemma comp_autMap_apply
  statement: (F : C ⥤ FintypeCat.{w}) {A B : C} [IsConnected A] [IsGalois B]
  proof: by
  simpa [-comp_autMap] using ConcreteCategory.congr_hom (F.congr_map (comp_autMap f σ)) a

中文:
引理 comp_autMap_apply
  结论: (F : C ⥤ FintypeCat.{w}) {A B : C} [是连通 A] [是Galois B]
  证明: by
  simpa [-comp_autMap] using ConcreteCategory.congr_hom (F.congr_map (comp_autMap f σ)) a

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.congr_map, comp_autMap, congr_hom, congr_map
-/
lemma comp_autMap_apply (F : C ⥤ FintypeCat.{w}) {A B : C} [IsConnected A] [IsGalois B]
    (f : A ⟶ B) (σ : Aut A) (a : F.obj A) :
    F.map (autMap f σ).hom (F.map f a) = F.map f (F.map σ.hom a) := by
  simpa [-comp_autMap] using ConcreteCategory.congr_hom (F.congr_map (comp_autMap f σ)) a

/--
lemma `autMap_unique` / 引理 `autMap_unique`

English:
lemma autMap_unique
  statement: {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
  proof: ((exists_autMap f σ).choose_spec.right τ h).symm

@[simp]

中文:
引理 autMap_unique
  结论: {A B : C} [是连通 A] [是Galois B] (f : A ⟶ B) (σ : Aut A)
  证明: ((exists_autMap f σ).choose_spec.right τ h).symm

@[simp]

Depends on / 依赖: choose_spec, choose_spec.right, exists_autMap
-/
lemma autMap_unique {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
    (τ : Aut B) (h : f ≫ τ.hom = σ.hom ≫ f) :
    autMap f σ = τ :=
  ((exists_autMap f σ).choose_spec.right τ h).symm

@[simp]
/--
lemma `autMap_id` / 引理 `autMap_id`

English:
lemma autMap_id
  given: {A : C} [IsGalois A]
  statement: autMap (𝟙 A) = id
  proof: funext fun σ => autMap_unique (𝟙 A) σ _ (by simp)

@[simp]

中文:
引理 autMap_id
  条件: {A : C} [是Galois A]
  结论: autMap (𝟙 A) = id
  证明: funext fun σ => autMap_unique (𝟙 A) σ _ (by simp)

@[simp]

Depends on / 依赖: autMap_unique
-/
lemma autMap_id {A : C} [IsGalois A] : autMap (𝟙 A) = id :=
  funext fun σ => autMap_unique (𝟙 A) σ _ (by simp)

@[simp]
/--
lemma `autMap_comp` / 引理 `autMap_comp`

English:
lemma autMap_comp
  statement: {X Y Z : C} [IsConnected X] [IsGalois Y] [IsGalois Z] (f : X ⟶ Y)
  proof: by
  refine funext fun σ => autMap_unique _ σ _ ?_
  rw [Function.comp_apply]; rw [Category.assoc]; rw [comp_autMap]; rw [← Category.assoc]
  simp

中文:
引理 autMap_comp
  结论: {X Y Z : C} [是连通 X] [是Galois Y] [是Galois Z] (f : X ⟶ Y)
  证明: by
  refine funext fun σ => autMap_unique _ σ _ ?_
  rw [Function.comp_apply]; rw [Category.assoc]; rw [comp_autMap]; rw [← Category.assoc]
  simp

Depends on / 依赖: Category, Category.assoc, Function, Function.comp_apply, autMap_unique, comp_apply, comp_autMap
-/
lemma autMap_comp {X Y Z : C} [IsConnected X] [IsGalois Y] [IsGalois Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) : autMap (f ≫ g) = autMap g ∘ autMap f := by
  refine funext fun σ => autMap_unique _ σ _ ?_
  rw [Function.comp_apply]; rw [Category.assoc]; rw [comp_autMap]; rw [← Category.assoc]
  simp

/--
lemma `autMap_surjective_of_isGalois` / 引理 `autMap_surjective_of_isGalois`

English:
lemma autMap_surjective_of_isGalois
  given: {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶ B)
  proof: by
  intro σ
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom (F.map f a))
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B (F.map f a)
  simp [hτ, ha']

中文:
引理 autMap_surjective_of_isGalois
  条件: {A B : C} [是Galois A] [是Galois B] (f : A ⟶ B)
  证明: by
  intro σ
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom (F.map f a))
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B (F.map f a)
  simp [hτ, ha']

Depends on / 依赖: F.map, GaloisCategory, GaloisCategory.getFiberFunctor, MulAction, MulAction.exists_smul_eq, evaluation_aut_injective_of_isConnected, exists_smul_eq, getFiberFunctor, nonempty_fiber_of_isConnected, surjective_of_nonempty_fiber_of_isConnected
-/
lemma autMap_surjective_of_isGalois {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶ B) :
    Function.Surjective (autMap f) := by
  intro σ
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom (F.map f a))
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B (F.map f a)
  simp [hτ, ha']

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `autMap_apply_mul` / 引理 `autMap_apply_mul`

English:
lemma autMap_apply_mul
  given: {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ τ : Aut A)
  proof: by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply evaluation_aut_injective_of_isConnected F (B : C) (F.map f a)
  simp [Aut.Aut_mul_def]

中文:
引理 autMap_apply_mul
  条件: {A B : C} [是连通 A] [是Galois B] (f : A ⟶ B) (σ τ : Aut A)
  证明: by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply evaluation_aut_injective_of_isConnected F (B : C) (F.map f a)
  simp [Aut.Aut_mul_def]

Depends on / 依赖: Aut.Aut_mul_def, Aut_mul_def, F.map, GaloisCategory, GaloisCategory.getFiberFunctor, evaluation_aut_injective_of_isConnected, getFiberFunctor, nonempty_fiber_of_isConnected
-/
lemma autMap_apply_mul {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ τ : Aut A) :
    autMap f (σ * τ) = autMap f σ * autMap f τ := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply evaluation_aut_injective_of_isConnected F (B : C) (F.map f a)
  simp [Aut.Aut_mul_def]

/-- `MonoidHom` version of `autMap`. -/
@[simps!]
/--
Definition of `autMapHom` / `autMapHom` 的定义

English:
definition autMapHom
  signature: {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B)
  body: MonoidHom.mk' (autMap f) (autMap_apply_mul f)

中文:
定义 autMapHom
  签名: {A B : C} [是连通 A] [是Galois B] (f : A ⟶ B)
  定义体: MonoidHom.mk' (autMap f) (autMap_apply_mul f)

Depends on / 依赖: MonoidHom, MonoidHom.mk, autMap, autMap_apply_mul
-/
noncomputable def autMapHom {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) :
     Aut A ->* Aut B :=
  MonoidHom.mk' (autMap f) (autMap_apply_mul f)

end AutMap

end PreGaloisCategory

end CategoryTheory
