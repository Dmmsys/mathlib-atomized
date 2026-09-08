/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# The extension functor on the homotopy categories

Given an embedding of complex shapes `e : c.Embedding c'` and a preadditive
category `C`, we define a fully faithful functor
`e.extendHomotopyFunctor C : HomotopyCategory C c ⥤ HomotopyCategory C c'`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace Homotopy

open HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

namespace extend

variable (e : c.Embedding c') (φ : ∀ i j, K.X i ⟶ L.X j)

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `Homotopy.extend` -/
/-
**Homotopy.extend.homAux** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy.extend`。
形式化陈述：homAux (i' j' : Option ι) : extend.X K i' ⟶ extend.X L j'
参数：i' j' : Option ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Homotopy.extend`
-/
noncomputable def homAux (i' j' : Option ι) : extend.X K i' ⟶ extend.X L j' :=
  match i', j' with
  | none, _ => 0
  | _, none => 0
  | some i, some j => φ i j

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.extend.homAux_eq** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy.extend`。
形式化陈述：homAux_eq (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some 
j) : homAux φ i' j' = (extend.XIso K hi).hom ≫ φ i j ≫ (extend.XIso L hj).inv
参数：i' j' : Option ι；i j : ι；hi : i' = some i；hj : j' = some j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homAux_eq (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some j) :
    homAux φ i' j' = (extend.XIso K hi).hom ≫ φ i j ≫ (extend.XIso L hj).inv := by
  subst hi hj
  simp [homAux, extend.XIso, extend.X]

/-- Auxiliary definition for `Homotopy.extend`. -/
/-
**Homotopy.extend.hom** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy.extend`。
形式化陈述：hom (i' j' : ι') : (K.extend e).X i' ⟶ (L.extend e).X j'
参数：i' j' : ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Homotopy.extend`.
-/
noncomputable def hom (i' j' : ι') : (K.extend e).X i' ⟶ (L.extend e).X j' :=
  extend.homAux φ (e.r i') (e.r j')
/-
**Homotopy.extend.hom_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy.extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_eq_zero₁ (i' j' : ι') (hi' : ∀ i, e.f i ≠ i') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hi').eq_of_src _ _
/-
**Homotopy.extend.hom_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy.extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_eq_zero₂ (i' j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hj').eq_of_tgt _ _
/-
**Homotopy.extend.hom_eq** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy.extend`。
形式化陈述：hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') : hom e 
φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendXIso e hj).inv
参数：hi : e.f i = i'；hj : e.f j = j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homotopy.extend.homAux_eq`：homAux_eq (i' j' : Option ι) (i j : ι) (hi : 
i' = some i) (hj : j' = some j) : homAux φ i' j' = (extend.XIso K hi).hom ≫ φ i 
j ≫ (extend.XIs…
· 使用引理 `ComplexShape.Embedding.r_eq_some`：r_eq_some {i : ι} {i' : ι'} (hi : e.f 
i = i') : e.r i' = some i
-/
lemma hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    hom e φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendXIso e hj).inv :=
  homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

end extend

/-- If `e : c.Embedding c'` is an embedding of complex shapes and `h` is a
homotopy between morphisms of homological complexes of shape `c`, this is
the corresponding homotopy between the extension of these morphisms. -/
/-
**Homotopy.extend** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] : Homotopy (ex
tendMap f e) (extendMap g e) where hom
参数：h : Homotopy f g；e : c.Embedding c'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : c.Embedding c'` is an embedding of complex shapes and `h` is a
homotopy between morphisms of homological complexes of shape `c`, this is
the corresponding homotopy between the extension of these morphisms.
-/
noncomputable def extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    Homotopy (extendMap f e) (extendMap g e) where
  hom := extend.hom e h.hom
  comm i' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [extendMap_f _ _ rfl, extendMap_f _ _ rfl, h.comm i, Preadditive.add_comp,
        Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add, add_left_inj]
      congr 1
      · by_cases hi : c.Rel i (c.next i)
        · have hi' : c'.Rel (e.f i) (e.f (c.next i)) := by rwa [e.rel_iff]
          simp [dNext_eq _ hi, dNext_eq _ hi', extend.hom_eq _ _ rfl rfl,
            extend_d_eq _ _ rfl rfl]
        · rw [dNext_eq_zero _ _ hi]
          by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
          · simp [dNext_eq _ hi', K.extend_d_from_eq_zero _ _ _ _ rfl hi]
          · simp [dNext_eq_zero _ _ hi']
      · by_cases hi : c.Rel (c.prev i) i
        · have hi' : c'.Rel (e.f (c.prev i)) (e.f i) := by rwa [e.rel_iff]
          simp [prevD_eq _ hi, prevD_eq _ hi', extend.hom_eq _ _ rfl rfl,
            extend_d_eq _ _ rfl rfl]
        · rw [prevD_eq_zero _ _ hi]
          by_cases hi' : c'.Rel (c'.prev (e.f i)) (e.f i)
          · simp [prevD_eq _ hi', L.extend_d_to_eq_zero _ _ _ _ rfl hi]
          · simp [prevD_eq_zero _ _ hi']
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _
  zero i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [extend.hom_eq _ _ rfl rfl, h.zero _ _ (by rwa [← e.rel_iff]),
          zero_comp, comp_zero]
      · exact extend.hom_eq_zero₂ _ _ _ _ (by tauto)
    · exact extend.hom_eq_zero₁ _ _ _ _ (by tauto)
/-
**Homotopy.extend_hom_eq** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy`。
形式化陈述：extend_hom_eq (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] {i' j' 
: ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') : (h.extend e).hom i' j' = (
K.extendXIso e hi).hom ≫ h.hom i j ≫ (L.extendXIso e hj).inv
参数：h : Homotopy f g；e : c.Embedding c'；hi : e.f i = i'；hj : e.f j = j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homotopy.extend.hom_eq`：hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') 
(hj : e.f j = j') : hom e φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendX
Iso e hj).in…
-/
lemma extend_hom_eq (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
    {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (h.extend e).hom i' j' = (K.extendXIso e hi).hom ≫ h.hom i j ≫ (L.extendXIso e hj).inv :=
  extend.hom_eq _ _ _ _

/-- If `e : c.Embedding c'` is an embedding of complex shapes,
`f` and `g` are morphism between cochain complexes of shape `c`,
and `h` is an homotopy between the extensions `extendMap f e` and `extendMap g e`,
then this is the corresponding homotopy between `f` and `g`. -/
@[simps -isSimp]
/-
**Homotopy.ofExtend** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：ofExtend {e : c.Embedding c'} [e.IsRelIff] (h : Homotopy (extendMap f e) (
extendMap g e)) : Homotopy f g where hom i j
参数：h : Homotopy (extendMap f e) (extendMap g e)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : c.Embedding c'` is an embedding of complex shapes,
`f` and `g` are morphism between cochain complexes of shape `c`,
and `h` is an homotopy between the extensions `extendMap f e` and `extendMap g e
`,
then this is the corresponding homotopy between `f` and `g`.
-/
noncomputable def ofExtend {e : c.Embedding c'} [e.IsRelIff]
    (h : Homotopy (extendMap f e) (extendMap g e)) :
    Homotopy f g where
  hom i j := (K.extendXIso e rfl).inv ≫ h.hom (e.f i) (e.f j) ≫ (L.extendXIso e rfl).hom
  comm i := by
    have := h.comm (e.f i)
    simp only [extendMap_f _ _ rfl] at this
    simp only [← cancel_mono (L.extendXIso e rfl).inv,
      ← cancel_epi (K.extendXIso e rfl).hom, this, Preadditive.add_comp,
      Preadditive.comp_add, add_left_inj]
    congr 1
    · by_cases hi : c.Rel i (c.next i)
      · have hi' : c'.Rel (e.f i) (e.f (c.next i)) := by rwa [e.rel_iff]
        simp [dNext_eq _ hi, dNext_eq _ hi', K.extend_d_eq _ rfl rfl]
      · rw [dNext_eq_zero _ _ hi]
        by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
        · simp [dNext_eq _ hi', extend_d_from_eq_zero _ _ _ _ _ rfl hi]
        · simp [dNext_eq_zero _ _ hi']
    · by_cases hi : c.Rel (c.prev i) i
      · have hi' : c'.Rel (e.f (c.prev i)) (e.f i) := by rwa [e.rel_iff]
        simp [prevD_eq _ hi, prevD_eq _ hi', L.extend_d_eq _ rfl rfl]
      · rw [prevD_eq_zero _ _ hi]
        by_cases hi' : c'.Rel (c'.prev (e.f i)) (e.f i)
        · simp [prevD_eq _ hi', extend_d_to_eq_zero _ _ _ _ _ rfl hi]
        · simp [prevD_eq_zero _ _ hi']
  zero i j hij := by rw [h.zero _ _ (by rwa [e.rel_iff]), zero_comp, comp_zero]

@[simp]
/-
**Homotopy.extend_ofExtend** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy`。
形式化陈述：extend_ofExtend {e : c.Embedding c'} [e.IsRelIff] (h : Homotopy (extendMap
 f e) (extendMap g e)) : (ofExtend h).extend e = h
参数：h : Homotopy (extendMap f e) (extendMap g e)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homotopy.ext`：∀ {ι : Type u_1} {V : Type u} {inst : CategoryTheory.Categ
ory.{v, u} V} {inst_1 : CategoryTheory.Preadditive V}   {c : ComplexShape ι} {C 
D …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Homotopy.extend_hom_eq`：extend_hom_eq (h : Homotopy f g) (e : c.Embeddin
g c') [e.IsRelIff] {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') : 
(h.extend e)…
· 使用定理 `Homotopy.ofExtend_hom`：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShap
e ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_
1, u_3} C] …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma extend_ofExtend {e : c.Embedding c'} [e.IsRelIff]
    (h : Homotopy (extendMap f e) (extendMap g e)) :
    (ofExtend h).extend e = h := by
  ext i' j'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      simp [extend_hom_eq _ e rfl rfl, ofExtend_hom]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

@[simp]
/-
**Homotopy.ofExtend_extend** 是 Mathlib 中的一个引理，位于命名空间 `Homotopy`。
形式化陈述：ofExtend_extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] : (h.
extend e).ofExtend = h
参数：h : Homotopy f g；e : c.Embedding c'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homotopy.ext`：∀ {ι : Type u_1} {V : Type u} {inst : CategoryTheory.Categ
ory.{v, u} V} {inst_1 : CategoryTheory.Preadditive V}   {c : ComplexShape ι} {C 
D …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.ofExtend_hom`：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShap
e ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_
1, u_3} C] …
· 使用引理 `Homotopy.extend_hom_eq`：extend_hom_eq (h : Homotopy f g) (e : c.Embeddin
g c') [e.IsRelIff] {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') : 
(h.extend e)…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofExtend_extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).ofExtend = h := by
  ext i j
  simp [ofExtend_hom, h.extend_hom_eq e rfl rfl]


/-- If `e : c.Embedding c'` is an embedding of complex shapes,
`f` and `g` are morphism between cochain complexes of shape `c`,
this is the bijection between homotopies between `f` and `g`,
and homotopies between the extensions `extendMap f e` and `extendMap g e`. -/
/-
**Homotopy.extendEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：extendEquiv (e : c.Embedding c') [e.IsRelIff] : Homotopy f g ≃ Homotopy (e
xtendMap f e) (extendMap g e) where toFun h
参数：e : c.Embedding c'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : c.Embedding c'` is an embedding of complex shapes,
`f` and `g` are morphism between cochain complexes of shape `c`,
this is the bijection between homotopies between `f` and `g`,
and homotopies between the extensions `extendMap f e` and `extendMap g e`.
-/
noncomputable def extendEquiv (e : c.Embedding c') [e.IsRelIff] :
    Homotopy f g ≃ Homotopy (extendMap f e) (extendMap g e) where
  toFun h := h.extend e
  invFun h := h.ofExtend
  left_inv _ := by simp
  right_inv _ := by simp

end Homotopy

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsRelIff]
  (C : Type*) [Category* C] [HasZeroObject C] [Preadditive C]

/-- Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomotopyCategory C c ⥤ HomotopyCategory C c'` which
extend complexes along `e`. -/
/-
**ComplexShape.Embedding.extendHomotopyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Comple
xShape.Embedding`。
形式化陈述：extendHomotopyFunctor : HomotopyCategory C c ⥤ HomotopyCategory C c'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomotopyCategory C c ⥤ HomotopyCategory C c'` which
extend complexes along `e`.
-/
noncomputable def extendHomotopyFunctor :
    HomotopyCategory C c ⥤ HomotopyCategory C c' :=
  CategoryTheory.Quotient.lift _ (e.extendFunctor C ⋙ HomotopyCategory.quotient C c') (by
    rintro K L f₁ f₂ ⟨h⟩
    exact HomotopyCategory.eq_of_homotopy _ _ (h.extend e))

/-- Given an embedding `e : c.Embedding c'` of complex shapes, the
functor `e.extendHomotopyFunctor C` on homotopy categories is
induced by the functor `e.extendFunctor C` on homological complexes. -/
/-
**ComplexShape.Embedding.extendHomotopyFunctorFactors** 是 Mathlib 中的一个定义，位于命名空间 
`ComplexShape.Embedding`。
形式化陈述：extendHomotopyFunctorFactors : HomotopyCategory.quotient C c ⋙ e.extendHom
otopyFunctor C ≅ e.extendFunctor C ⋙ HomotopyCategory.quotient C c'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : c.Embedding c'` of complex shapes, the
functor `e.extendHomotopyFunctor C` on homotopy categories is
induced by the functor `e.extendFunctor C` on homological complexes.
-/
noncomputable def extendHomotopyFunctorFactors :
    HomotopyCategory.quotient C c ⋙ e.extendHomotopyFunctor C ≅
      e.extendFunctor C ⋙ HomotopyCategory.quotient C c' :=
  Iso.refl _
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (e.extendHomotopyFunctor C).Full where
  map_surjective {K L} φ := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ : K.extend e ⟶ L.extend e, rfl⟩ :=
      (HomotopyCategory.quotient C c').map_surjective φ
    obtain ⟨φ, rfl⟩ := (e.extendFunctor C).map_surjective φ
    exact ⟨(HomotopyCategory.quotient _ _).map φ, rfl⟩
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (e.extendHomotopyFunctor C).Faithful where
  map_injective {K L} φ₁ φ₂ hφ := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ₁, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₁
    obtain ⟨φ₂, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (.ofExtend (HomotopyCategory.homotopyOfEq _ _ hφ))

end ComplexShape.Embedding

@[simp]
/-
**HomologicalComplex.homotopyEquivalences_extendMap_iff** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：HomologicalComplex.homotopyEquivalences_extendMap_iff {C : Type*} [Categor
y* C] [HasZeroObject C] [Preadditive C] {K L : HomologicalComplex C c} (f : K ⟶ 
L) (e : ComplexShape.Embedding c c') [e.IsRelIff] : homotopyEquivalences C c' (e
xtendMap f e) ↔ homotopyEquivalences C c f
参数：f : K ⟶ L；e : ComplexShape.Embedding c c'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `ComplexShape.Embedding.instFullHomotopyCategoryExtendHomotopyFunctor`：∀ 
{ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : 
c.Embedding c') [inst : e.IsRelIff]   (C : Type u_3) [inst…
· 使用定理 `ComplexShape.Embedding.instFaithfulHomotopyCategoryExtendHomotopyFunctor
`：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (
e : c.Embedding c') [inst : e.IsRelIff]   (C : Type u_3) [inst…
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma HomologicalComplex.homotopyEquivalences_extendMap_iff
    {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : ComplexShape.Embedding c c') [e.IsRelIff] :
    homotopyEquivalences C c' (extendMap f e) ↔
      homotopyEquivalences C c f := by
  #adaptation_note /-- Prior to nightly-2026-05-07, `dsimp%` was used directly inline as the last
  argument to the original `simp`; it now reports `made no progress` so we apply
  `NatIso.isIso_map_iff` via a `change` + `rw` after the rest of the simp set has done its work. -/
  simp only [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (e.extendHomotopyFunctor C)]
  change _ ↔ IsIso ((HomotopyCategory.quotient C c ⋙ e.extendHomotopyFunctor C).map f)
  rw [NatIso.isIso_map_iff (e.extendHomotopyFunctorFactors C) f]
  rfl
