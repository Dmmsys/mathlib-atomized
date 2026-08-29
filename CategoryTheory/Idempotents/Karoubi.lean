/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `Karoubi C` of a category `C`.

## Main constructions and definitions

- `Karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
  complete category. It is also preadditive when `C` is preadditive.
- `toKaroubi C : C ⥤ Karoubi C` is a fully faithful functor, which is an equivalence
  (`toKaroubiIsEquivalence`) when `C` is idempotent complete.

-/

@[expose] public section

noncomputable section

open CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type*) [Category* C]

namespace Idempotents

/--
Definition of `Karoubi` / `Karoubi` 的定义

English:
structure Karoubi
  parameters: where
  axioms and operations (3):
    - X : C
    - p : X ⟶ X
    - idem : p ≫ p = p  [default: by cat_disch]

中文:
结构 Karoubi
  参数: where
  公理与运算 (3 个):
    - X : C
    - p : X ⟶ X
    - idem : p ≫ p = p  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Karoubi where
  /-- an object of the underlying category -/
  X : C
  /-- an endomorphism of the object -/
  p : X ⟶ X
  /-- the condition that the given endomorphism is an idempotent -/
  idem : p ≫ p = p := by cat_disch

namespace Karoubi

variable {C}

attribute [reassoc (attr := simp)] idem

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p)
  proof: by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [mk.injEq, heq_eq_eq, true_and, eqToHom_refl, comp_id, id_comp] using h_p

中文:
定理 ext
  条件: {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p)
  证明: by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [mk.injEq, heq_eq_eq, true_and, eqToHom_refl, comp_id, id_comp] using h_p

Depends on / 依赖: comp_id, eqToHom_refl, heq_eq_eq, id_comp, mk.injEq, true_and
-/
theorem ext {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) :
    P = Q := by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [mk.injEq, heq_eq_eq, true_and, eqToHom_refl, comp_id, id_comp] using h_p

/-- A morphism `P ⟶ Q` in the category `Karoubi C` is a morphism in the underlying category
`C` which satisfies a relation, which in the preadditive case, expresses that it induces a
map between the corresponding "formal direct factors" and that it vanishes on the complement
formal direct factor. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (P Q : Karoubi C)
  axioms and operations (2):
    - f : P.X ⟶ Q.X
    - comm : P.p ≫ f ≫ Q.p = f  [default: by cat_disch]

中文:
结构 态射
  参数: (P Q : Karoubi C)
  公理与运算 (2 个):
    - f : P.X ⟶ Q.X
    - comm : P.p ≫ f ≫ Q.p = f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (P Q : Karoubi C) where
  /-- a morphism between the underlying objects -/
  f : P.X ⟶ Q.X
  /-- compatibility of the given morphism with the given idempotents -/
  comm : P.p ≫ f ≫ Q.p = f := by cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] (P Q
  body: ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[reassoc (attr := simp)]

中文:
实例 [预加性
  签名: C] (P Q
  定义体: ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[reassoc (attr := simp)]

Depends on / 依赖: comp_zero, zero_comp
-/
instance [Preadditive C] (P Q : Karoubi C) : Inhabited (Hom P Q) :=
  ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[reassoc (attr := simp)]
/--
theorem `p_comp` / 定理 `p_comp`

English:
theorem p_comp
  given: {P Q : Karoubi C} (f : Hom P Q)
  statement: P.p ≫ f.f = f.f
  proof: by
  rw [← f.comm]; rw [← assoc]; rw [P.idem]

@[reassoc (attr := simp)]

中文:
定理 p_comp
  条件: {P Q : Karoubi C} (f : 态射 P Q)
  结论: P.p ≫ f.f = f.f
  证明: by
  rw [← f.comm]; rw [← assoc]; rw [P.idem]

@[reassoc (attr := simp)]

Depends on / 依赖: P.idem, f.comm
-/
theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := by
  rw [← f.comm]; rw [← assoc]; rw [P.idem]

@[reassoc (attr := simp)]
/--
theorem `comp_p` / 定理 `comp_p`

English:
theorem comp_p
  given: {P Q : Karoubi C} (f : Hom P Q)
  statement: f.f ≫ Q.p = f.f
  proof: by
  rw [← f.comm]; rw [assoc]; rw [assoc]; rw [Q.idem]

@[reassoc]

中文:
定理 comp_p
  条件: {P Q : Karoubi C} (f : 态射 P Q)
  结论: f.f ≫ Q.p = f.f
  证明: by
  rw [← f.comm]; rw [assoc]; rw [assoc]; rw [Q.idem]

@[reassoc]

Depends on / 依赖: Q.idem, f.comm
-/
theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := by
  rw [← f.comm]; rw [assoc]; rw [assoc]; rw [Q.idem]

@[reassoc]
/--
theorem `p_comm` / 定理 `p_comm`

English:
theorem p_comm
  given: {P Q : Karoubi C} (f : Hom P Q)
  statement: P.p ≫ f.f = f.f ≫ Q.p
  proof: by rw [p_comp, comp_p]

中文:
定理 p_comm
  条件: {P Q : Karoubi C} (f : 态射 P Q)
  结论: P.p ≫ f.f = f.f ≫ Q.p
  证明: by rw [p_comp, comp_p]

Depends on / 依赖: comp_p, p_comp
-/
theorem p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p := by rw [p_comp, comp_p]

/--
theorem `comp_proof` / 定理 `comp_proof`

English:
theorem comp_proof
  given: {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q)
  proof: by simp

中文:
定理 comp_proof
  条件: {P Q R : Karoubi C} (g : 态射 Q R) (f : 态射 P Q)
  证明: by simp
-/
theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) :
    P.p ≫ (f.f ≫ g.f) ≫ R.p = f.f ≫ g.f := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Karoubi C)
  body: Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]

中文:
实例 :
  签名: 范畴 (Karoubi C)
  定义体: Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]

Depends on / 依赖: Karoubi, Karoubi.Hom
-/
instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]
/--
theorem `hom_ext_iff` / 定理 `hom_ext_iff`

English:
theorem hom_ext_iff
  given: {P Q : Karoubi C} {f g : P ⟶ Q}
  statement: f = g ↔ f.f = g.f
  proof: by
  constructor
  · intro h
    rw [h]
  · apply Hom.ext

@[ext]

中文:
定理 hom_ext_iff
  条件: {P Q : Karoubi C} {f g : P ⟶ Q}
  结论: f = g ↔ f.f = g.f
  证明: by
  constructor
  · intro h
    rw [h]
  · apply Hom.ext

@[ext]

Depends on / 依赖: Hom.ext
-/
theorem hom_ext_iff {P Q : Karoubi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f := by
  constructor
  · intro h
    rw [h]
  · apply Hom.ext

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f)
  statement: f = g
  proof: by
  simpa [hom_ext_iff] using h

@[simp]

中文:
定理 hom_ext
  条件: {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f)
  结论: f = g
  证明: by
  simpa [hom_ext_iff] using h

@[simp]

Depends on / 依赖: hom_ext_iff
-/
theorem hom_ext {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f) : f = g := by
  simpa [hom_ext_iff] using h

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R)
  statement: (f ≫ g).f = f.f ≫ g.f
  proof: rfl

@[simp]

中文:
定理 comp_f
  条件: {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R)
  结论: (f ≫ g).f = f.f ≫ g.f
  证明: rfl

@[simp]
-/
theorem comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f := rfl

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: {P : Karoubi C}
  statement: Hom.f (𝟙 P) = P.p
  proof: rfl

中文:
定理 id_f
  条件: {P : Karoubi C}
  结论: 态射.f (𝟙 P) = P.p
  证明: rfl
-/
theorem id_f {P : Karoubi C} : Hom.f (𝟙 P) = P.p := rfl

/--
Instance `coe` / 实例 `coe`

English:
instance coe
  signature: : CoeTC C (Karoubi C)
  body: ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩

中文:
实例 coe
  签名: : CoeTC C (Karoubi C)
  定义体: ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩

Depends on / 依赖: comp_id
-/
instance coe : CoeTC C (Karoubi C) :=
  ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩

/--
theorem `coe_X` / 定理 `coe_X`

English:
theorem coe_X
  given: (X : C)
  statement: (X : Karoubi C).X = X
  proof: by simp

@[simp]

中文:
定理 coe_X
  条件: (X : C)
  结论: (X : Karoubi C).X = X
  证明: by simp

@[simp]
-/
theorem coe_X (X : C) : (X : Karoubi C).X = X := by simp

@[simp]
/--
theorem `coe_p` / 定理 `coe_p`

English:
theorem coe_p
  given: (X : C)
  statement: (X : Karoubi C).p = 𝟙 X
  proof: rfl

@[simp]

中文:
定理 coe_p
  条件: (X : C)
  结论: (X : Karoubi C).p = 𝟙 X
  证明: rfl

@[simp]
-/
theorem coe_p (X : C) : (X : Karoubi C).p = 𝟙 X := rfl

@[simp]
/--
theorem `eqToHom_f` / 定理 `eqToHom_f`

English:
theorem eqToHom_f
  given: {P Q : Karoubi C} (h : P = Q)
  proof: by
  subst h
  simp only [eqToHom_refl, Karoubi.id_f, comp_id]

中文:
定理 eqToHom_f
  条件: {P Q : Karoubi C} (h : P = Q)
  证明: by
  subst h
  simp only [eqToHom_refl, Karoubi.id_f, comp_id]

Depends on / 依赖: Karoubi, Karoubi.id_f, comp_id, eqToHom_refl, id_f
-/
theorem eqToHom_f {P Q : Karoubi C} (h : P = Q) :
    Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.X h) := by
  subst h
  simp only [eqToHom_refl, Karoubi.id_f, comp_id]

end Karoubi

/-- The obvious fully faithful functor `toKaroubi` sends an object `X : C` to the obvious
formal direct factor of `X` given by `𝟙 X`. -/
@[simps, implicit_reducible]
/--
Definition of `toKaroubi` / `toKaroubi` 的定义

English:
definition toKaroubi
  signature: : C ⥤ Karoubi C where
  body: ⟨X, 𝟙 X, by rw [comp_id]⟩
  map f := ⟨f, by simp only [comp_id, id_comp]⟩

中文:
定义 toKaroubi
  签名: : C ⥤ Karoubi C where
  定义体: ⟨X, 𝟙 X, by rw [comp_id]⟩
  map f := ⟨f, by simp only [comp_id, id_comp]⟩

Depends on / 依赖: comp_id
-/
def toKaroubi : C ⥤ Karoubi C where
  obj X := ⟨X, 𝟙 X, by rw [comp_id]⟩
  map f := ⟨f, by simp only [comp_id, id_comp]⟩

/--
Definition of `fullyFaithfulToKaroubi` / `fullyFaithfulToKaroubi` 的定义

English:
definition fullyFaithfulToKaroubi
  signature: : (toKaroubi C).FullyFaithful where
  body: f.f

中文:
定义 fullyFaithfulToKaroubi
  签名: : (toKaroubi C).满忠实 where
  定义体: f.f
-/
def fullyFaithfulToKaroubi : (toKaroubi C).FullyFaithful where
  preimage f := f.f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toKaroubi C).Full
  body: (fullyFaithfulToKaroubi C).full

中文:
实例 :
  签名: (toKaroubi C).满
  定义体: (fullyFaithfulToKaroubi C).full

Depends on / 依赖: fullyFaithfulToKaroubi
-/
instance : (toKaroubi C).Full := (fullyFaithfulToKaroubi C).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toKaroubi C).Faithful
  body: (fullyFaithfulToKaroubi C).faithful

中文:
实例 :
  签名: (toKaroubi C).忠实
  定义体: (fullyFaithfulToKaroubi C).faithful

Depends on / 依赖: faithful, fullyFaithfulToKaroubi
-/
instance : (toKaroubi C).Faithful := (fullyFaithfulToKaroubi C).faithful

variable {C}

@[simps add]
/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [Preadditive C] {P Q : Karoubi C}
  body: ⟨f.f + g.f, by rw [add_comp, comp_add, f.comm, g.comm]⟩

@[simps neg]

中文:
实例 instAdd
  签名: [预加性 C] {P Q : Karoubi C}
  定义体: ⟨f.f + g.f, by rw [add_comp, comp_add, f.comm, g.comm]⟩

@[simps neg]

Depends on / 依赖: add_comp, comp_add, f.comm, g.comm
-/
instance instAdd [Preadditive C] {P Q : Karoubi C} : Add (P ⟶ Q) where
  add f g := ⟨f.f + g.f, by rw [add_comp, comp_add, f.comm, g.comm]⟩

@[simps neg]
/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [Preadditive C] {P Q : Karoubi C}
  body: ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩

@[simps zero]

中文:
实例 instNeg
  签名: [预加性 C] {P Q : Karoubi C}
  定义体: ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩

@[simps zero]

Depends on / 依赖: comp_neg, f.comm, neg_comp, neg_inj
-/
instance instNeg [Preadditive C] {P Q : Karoubi C} : Neg (P ⟶ Q) where
  neg f := ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩

@[simps zero]
/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Preadditive C] {P Q : Karoubi C}
  body: ⟨0, by simp only [comp_zero, zero_comp]⟩

中文:
实例 instZero
  签名: [预加性 C] {P Q : Karoubi C}
  定义体: ⟨0, by simp only [comp_zero, zero_comp]⟩

Depends on / 依赖: comp_zero, zero_comp
-/
instance instZero [Preadditive C] {P Q : Karoubi C} : Zero (P ⟶ Q) where
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩

/--
Instance `instAddCommGroupHom` / 实例 `instAddCommGroupHom`

English:
instance instAddCommGroupHom
  signature: [Preadditive C] {P Q : Karoubi C}
  body: by
    ext
    apply zero_add
  add_zero f := by
    ext
    apply add_zero
  add_assoc f g h' := by
    ext
    apply add_assoc
  add_comm f g := by
    ext
    apply add_comm
  neg_add_cancel f := by
    ext
    apply neg_add_cancel
  zsmul := zsmulRec
  nsmul := nsmulRec

中文:
实例 instAddCommGroupHom
  签名: [预加性 C] {P Q : Karoubi C}
  定义体: by
    ext
    apply zero_add
  add_zero f := by
    ext
    apply add_zero
  add_assoc f g h' := by
    ext
    apply add_assoc
  add_comm f g := by
    ext
    apply add_comm
  neg_add_cancel f := by
    ext
    apply neg_add_cancel
  zsmul := zsmulRec
  nsmul := nsmulRec

Depends on / 依赖: add_assoc, add_comm, add_zero, neg_add_cancel, nsmulRec, zero_add, zsmulRec
-/
instance instAddCommGroupHom [Preadditive C] {P Q : Karoubi C} : AddCommGroup (P ⟶ Q) where
  zero_add f := by
    ext
    apply zero_add
  add_zero f := by
    ext
    apply add_zero
  add_assoc f g h' := by
    ext
    apply add_assoc
  add_comm f g := by
    ext
    apply add_comm
  neg_add_cancel f := by
    ext
    apply neg_add_cancel
  zsmul := zsmulRec
  nsmul := nsmulRec

namespace Karoubi

/--
theorem `hom_eq_zero_iff` / 定理 `hom_eq_zero_iff`

English:
theorem hom_eq_zero_iff
  given: [Preadditive C] {P Q : Karoubi C} {f : P ⟶ Q}
  statement: f = 0 ↔ f.f = 0
  proof: hom_ext_iff

中文:
定理 hom_eq_zero_iff
  条件: [预加性 C] {P Q : Karoubi C} {f : P ⟶ Q}
  结论: f = 0 ↔ f.f = 0
  证明: hom_ext_iff

Depends on / 依赖: hom_ext_iff
-/
theorem hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : P ⟶ Q} : f = 0 ↔ f.f = 0 :=
  hom_ext_iff

/-- The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive. -/
@[simps]
/--
Definition of `inclusionHom` / `inclusionHom` 的定义

English:
definition inclusionHom
  signature: [Preadditive C] (P Q : Karoubi C)
  body: f.f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]

中文:
定义 inclusionHom
  签名: [预加性 C] (P Q : Karoubi C)
  定义体: f.f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
-/
def inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.X ⟶ Q.X) where
  toFun f := f.f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
/--
theorem `sum_hom` / 定理 `sum_hom`

English:
theorem sum_hom
  given: [Preadditive C] {P Q : Karoubi C} {α : Type*} (s : Finset α) (f : α -> (P ⟶ Q))
  proof: map_sum (inclusionHom P Q) f s

中文:
定理 sum_hom
  条件: [预加性 C] {P Q : Karoubi C} {α : 类型} (s : 有限集 α) (f : α -> (P ⟶ Q))
  证明: map_sum (inclusionHom P Q) f s

Depends on / 依赖: inclusionHom, map_sum
-/
theorem sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type*} (s : Finset α) (f : α -> (P ⟶ Q)) :
    (∑ x in s, f x).f = ∑ x in s, (f x).f :=
  map_sum (inclusionHom P Q) f s

end Karoubi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : Preadditive (Karoubi C) where
  body: by infer_instance

中文:
实例 [预加性
  签名: C] : 预加性 (Karoubi C) where
  定义体: by infer_instance

Depends on / 依赖: WidePullbackShape, WidePullbackShape.Hom.id, infer_instance
-/
instance [Preadditive C] : Preadditive (Karoubi C) where
  homGroup P Q := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : Functor.Additive (toKaroubi C) where

中文:
实例 [预加性
  签名: C] : 函子.加性 (toKaroubi C) where

Depends on / 依赖: eq_iff_true_of_subsingleton, intros
-/
instance [Preadditive C] : Functor.Additive (toKaroubi C) where

open Karoubi

variable (C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIdempotentComplete (Karoubi C)
  body: by
  refine ⟨?_⟩
  intro P p hp
  simp only [hom_ext_iff, comp_f] at hp
  use ⟨P.X, p.f, hp⟩
  use ⟨p.f, by rw [comp_p p, hp]⟩
  use ⟨p.f, by rw [hp, p_comp p]⟩
  simp [hp]

中文:
实例 :
  签名: 是IdempotentComplete (Karoubi C)
  定义体: by
  refine ⟨?_⟩
  intro P p hp
  simp only [hom_ext_iff, comp_f] at hp
  use ⟨P.X, p.f, hp⟩
  use ⟨p.f, by rw [comp_p p, hp]⟩
  use ⟨p.f, by rw [hp, p_comp p]⟩
  simp [hp]

Depends on / 依赖: comp_f, comp_p, hom_ext_iff, p_comp
-/
instance : IsIdempotentComplete (Karoubi C) := by
  refine ⟨?_⟩
  intro P p hp
  simp only [hom_ext_iff, comp_f] at hp
  use ⟨P.X, p.f, hp⟩
  use ⟨p.f, by rw [comp_p p, hp]⟩
  use ⟨p.f, by rw [hp, p_comp p]⟩
  simp [hp]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIdempotentComplete
  signature: C] : (toKaroubi C).EssSurj
  body: ⟨fun P => by
    rcases IsIdempotentComplete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { hom := ⟨i, by simp [← Category.assoc, h₁, ← h₂]⟩
          inv := ⟨e, by simp [Category.assoc, h₁, ← h₂]⟩ }⟩

中文:
实例 [是IdempotentComplete
  签名: C] : (toKaroubi C).本质满射
  定义体: ⟨fun P => by
    rcases IsIdempotentComplete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { hom := ⟨i, by simp [← Category.assoc, h₁, ← h₂]⟩
          inv := ⟨e, by simp [Category.assoc, h₁, ← h₂]⟩ }⟩

Depends on / 依赖: Category, Category.assoc, IsIdempotentComplete, IsIdempotentComplete.idempotents_split, Nonempty, Nonempty.intro, P.idem, idempotents_split
-/
instance [IsIdempotentComplete C] : (toKaroubi C).EssSurj :=
  ⟨fun P => by
    rcases IsIdempotentComplete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { hom := ⟨i, by simp [← Category.assoc, h₁, ← h₂]⟩
          inv := ⟨e, by simp [Category.assoc, h₁, ← h₂]⟩ }⟩

/--
Instance `toKaroubi_isEquivalence` / 实例 `toKaroubi_isEquivalence`

English:
instance toKaroubi_isEquivalence
  signature: [IsIdempotentComplete C]

中文:
实例 toKaroubi_isEquivalence
  签名: [是IdempotentComplete C]
-/
instance toKaroubi_isEquivalence [IsIdempotentComplete C] : (toKaroubi C).IsEquivalence where

/--
Definition of `toKaroubiEquivalence` / `toKaroubiEquivalence` 的定义

English:
definition toKaroubiEquivalence
  signature: [IsIdempotentComplete C]
  body: (toKaroubi C).asEquivalence

中文:
定义 toKaroubiEquivalence
  签名: [是IdempotentComplete C]
  定义体: (toKaroubi C).asEquivalence

Depends on / 依赖: WidePushoutShape, WidePushoutShape.Hom.id, asEquivalence, toKaroubi
-/
def toKaroubiEquivalence [IsIdempotentComplete C] : C ≌ Karoubi C :=
  (toKaroubi C).asEquivalence

/--
Instance `toKaroubiEquivalence_functor_additive` / 实例 `toKaroubiEquivalence_functor_additive`

English:
instance toKaroubiEquivalence_functor_additive
  signature: [Preadditive C] [IsIdempotentComplete C]
  body: inferInstanceAs (toKaroubi C).Additive

中文:
实例 toKaroubiEquivalence_functor_additive
  签名: [预加性 C] [是IdempotentComplete C]
  定义体: inferInstanceAs (toKaroubi C).Additive

Depends on / 依赖: Additive, eq_iff_true_of_subsingleton, toKaroubi
-/
instance toKaroubiEquivalence_functor_additive [Preadditive C] [IsIdempotentComplete C] :
    (toKaroubiEquivalence C).functor.Additive :=
inferInstanceAs (toKaroubi C).Additive

namespace Karoubi

variable {C}

/-- The split mono which appears in the factorisation `decompId P`. -/
@[simps]
/--
Definition of `decompId_i` / `decompId_i` 的定义

English:
definition decompId_i
  signature: (P : Karoubi C)
  body: ⟨P.p, by rw [coe_p, comp_id, P.idem]⟩

中文:
定义 decompId_i
  签名: (P : Karoubi C)
  定义体: ⟨P.p, by rw [coe_p, comp_id, P.idem]⟩

Depends on / 依赖: P.idem, coe_p, comp_id
-/
def decompId_i (P : Karoubi C) : P ⟶ P.X :=
  ⟨P.p, by rw [coe_p, comp_id, P.idem]⟩

/-- The split epi which appears in the factorisation `decompId P`. -/
@[simps]
/--
Definition of `decompId_p` / `decompId_p` 的定义

English:
definition decompId_p
  signature: (P : Karoubi C)
  body: ⟨P.p, by rw [coe_p, id_comp, P.idem]⟩

中文:
定义 decompId_p
  签名: (P : Karoubi C)
  定义体: ⟨P.p, by rw [coe_p, id_comp, P.idem]⟩

Depends on / 依赖: P.idem, coe_p, id_comp
-/
def decompId_p (P : Karoubi C) : (P.X : Karoubi C) ⟶ P :=
  ⟨P.p, by rw [coe_p, id_comp, P.idem]⟩

/-- The formal direct factor of `P.X` given by the idempotent `P.p` in the category `C`
is actually a direct factor in the category `Karoubi C`. -/
@[reassoc]
/--
theorem `decompId` / 定理 `decompId`

English:
theorem decompId
  given: (P : Karoubi C)
  statement: 𝟙 P = decompId_i P ≫ decompId_p P
  proof: by
  ext
  simp only [comp_f, id_f, P.idem, decompId_i, decompId_p]

中文:
定理 decompId
  条件: (P : Karoubi C)
  结论: 𝟙 P = decompId_i P ≫ decompId_p P
  证明: by
  ext
  simp only [comp_f, id_f, P.idem, decompId_i, decompId_p]

Depends on / 依赖: P.idem, comp_f, decompId_i, decompId_p, id_f
-/
theorem decompId (P : Karoubi C) : 𝟙 P = decompId_i P ≫ decompId_p P := by
  ext
  simp only [comp_f, id_f, P.idem, decompId_i, decompId_p]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `decomp_p` / 定理 `decomp_p`

English:
theorem decomp_p
  given: (P : Karoubi C)
  statement: (toKaroubi C).map P.p = decompId_p P ≫ decompId_i P
  proof: by
  ext
  simp only [comp_f, decompId_p_f, decompId_i_f, P.idem, toKaroubi_map_f]

中文:
定理 decomp_p
  条件: (P : Karoubi C)
  结论: (toKaroubi C).map P.p = decompId_p P ≫ decompId_i P
  证明: by
  ext
  simp only [comp_f, decompId_p_f, decompId_i_f, P.idem, toKaroubi_map_f]

Depends on / 依赖: P.idem, comp_f, decompId_i_f, decompId_p_f, toKaroubi_map_f
-/
theorem decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompId_p P ≫ decompId_i P := by
  ext
  simp only [comp_f, decompId_p_f, decompId_i_f, P.idem, toKaroubi_map_f]

/--
theorem `decompId_i_toKaroubi` / 定理 `decompId_i_toKaroubi`

English:
theorem decompId_i_toKaroubi
  given: (X : C)
  statement: decompId_i ((toKaroubi C).obj X) = 𝟙 _
  proof: rfl

中文:
定理 decompId_i_toKaroubi
  条件: (X : C)
  结论: decompId_i ((toKaroubi C).obj X) = 𝟙 _
  证明: rfl
-/
theorem decompId_i_toKaroubi (X : C) : decompId_i ((toKaroubi C).obj X) = 𝟙 _ :=
  rfl

/--
theorem `decompId_p_toKaroubi` / 定理 `decompId_p_toKaroubi`

English:
theorem decompId_p_toKaroubi
  given: (X : C)
  statement: decompId_p ((toKaroubi C).obj X) = 𝟙 _
  proof: rfl

中文:
定理 decompId_p_toKaroubi
  条件: (X : C)
  结论: decompId_p ((toKaroubi C).obj X) = 𝟙 _
  证明: rfl
-/
theorem decompId_p_toKaroubi (X : C) : decompId_p ((toKaroubi C).obj X) = 𝟙 _ :=
  rfl

/--
theorem `decompId_i_naturality` / 定理 `decompId_i_naturality`

English:
theorem decompId_i_naturality
  given: {P Q : Karoubi C} (f : P ⟶ Q)
  proof: by
  simp

中文:
定理 decompId_i_naturality
  条件: {P Q : Karoubi C} (f : P ⟶ Q)
  证明: by
  simp
-/
theorem decompId_i_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    f ≫ decompId_i Q = decompId_i P ≫ (by exact Hom.mk f.f (by simp)) := by
  simp

/--
theorem `decompId_p_naturality` / 定理 `decompId_p_naturality`

English:
theorem decompId_p_naturality
  given: {P Q : Karoubi C} (f : P ⟶ Q)
  proof: by
  simp

@[simp]

中文:
定理 decompId_p_naturality
  条件: {P Q : Karoubi C} (f : P ⟶ Q)
  证明: by
  simp

@[simp]
-/
theorem decompId_p_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    decompId_p P ≫ f = (by exact Hom.mk f.f (by simp)) ≫ decompId_p Q := by
  simp

@[simp]
/--
theorem `zsmul_hom` / 定理 `zsmul_hom`

English:
theorem zsmul_hom
  given: [Preadditive C] {P Q : Karoubi C} (n : Int) (f : P ⟶ Q)
  statement: (n • f).f = n • f.f
  proof: map_zsmul (inclusionHom P Q) n f

中文:
定理 zsmul_hom
  条件: [预加性 C] {P Q : Karoubi C} (n : 整数) (f : P ⟶ Q)
  结论: (n • f).f = n • f.f
  证明: map_zsmul (inclusionHom P Q) n f

Depends on / 依赖: inclusionHom, map_zsmul
-/
theorem zsmul_hom [Preadditive C] {P Q : Karoubi C} (n : Int) (f : P ⟶ Q) : (n • f).f = n • f.f :=
  map_zsmul (inclusionHom P Q) n f

set_option backward.defeqAttrib.useBackward true in
/-- If `X : Karoubi C`, then `X` is a retract of `((toKaroubi C).obj X.X)`. -/
@[simps]
/--
Definition of `retract` / `retract` 的定义

English:
definition retract
  signature: (X : Karoubi C)
  body: ⟨X.p, by simp⟩
  r := ⟨X.p, by simp⟩

中文:
定义 retract
  签名: (X : Karoubi C)
  定义体: ⟨X.p, by simp⟩
  r := ⟨X.p, by simp⟩
-/
def retract (X : Karoubi C) : Retract X ((toKaroubi C).obj X.X) where
  i := ⟨X.p, by simp⟩
  r := ⟨X.p, by simp⟩

end Karoubi

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toKaroubi C).PreservesEpimorphisms
  body: ⟨fun g h eq => by
    ext
    rw [← cancel_epi f]
    simpa using eq⟩

中文:
实例 :
  签名: (toKaroubi C).保持Epimorphisms
  定义体: ⟨fun g h eq => by
    ext
    rw [← cancel_epi f]
    simpa using eq⟩

Depends on / 依赖: cancel_epi
-/
instance : (toKaroubi C).PreservesEpimorphisms where
  preserves f _ := ⟨fun g h eq => by
    ext
    rw [← cancel_epi f]
    simpa using eq⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toKaroubi C).PreservesMonomorphisms
  body: ⟨fun g h eq => by
    ext
    rw [← cancel_mono f]
    simpa using eq⟩

中文:
实例 :
  签名: (toKaroubi C).保持Monomorphisms
  定义体: ⟨fun g h eq => by
    ext
    rw [← cancel_mono f]
    simpa using eq⟩

Depends on / 依赖: cancel_mono
-/
instance : (toKaroubi C).PreservesMonomorphisms where
  preserves f _ := ⟨fun g h eq => by
    ext
    rw [← cancel_mono f]
    simpa using eq⟩

end Idempotents

end CategoryTheory
