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

variable (e : c.Embedding c') (φ : forall i j, K.X i ⟶ L.X j)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `homAux` / `homAux` 的定义

English:
definition homAux
  signature: (i' j' : Option ι)
  body: match i', j' with
  | none, _ => 0
  | _, none => 0
  | some i, some j => φ i j

中文:
定义 homAux
  签名: (i' j' : 选项类型 ι)
  定义体: match i', j' with
  | none, _ => 0
  | _, none => 0
  | some i, some j => φ i j
-/
noncomputable def homAux (i' j' : Option ι) : extend.X K i' ⟶ extend.X L j' :=
  match i', j' with
  | none, _ => 0
  | _, none => 0
  | some i, some j => φ i j

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homAux_eq` / 引理 `homAux_eq`

English:
lemma homAux_eq
  given: (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some j)
  proof: by
  subst hi hj
  simp [homAux, extend.XIso, extend.X]

中文:
引理 homAux_eq
  条件: (i' j' : 选项类型 ι) (i j : ι) (hi : i' = some i) (hj : j' = some j)
  证明: by
  subst hi hj
  simp [homAux, extend.XIso, extend.X]

Depends on / 依赖: extend, extend.X, extend.XIso, homAux
-/
lemma homAux_eq (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some j) :
    homAux φ i' j' = (extend.XIso K hi).hom ≫ φ i j ≫ (extend.XIso L hj).inv := by
  subst hi hj
  simp [homAux, extend.XIso, extend.X]

/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: (i' j' : ι')
  body: extend.homAux φ (e.r i') (e.r j')

中文:
定义 hom
  签名: (i' j' : ι')
  定义体: extend.homAux φ (e.r i') (e.r j')

Depends on / 依赖: extend, extend.homAux, homAux
-/
noncomputable def hom (i' j' : ι') : (K.extend e).X i' ⟶ (L.extend e).X j' :=
  extend.homAux φ (e.r i') (e.r j')

/--
lemma `hom_eq_zero₁` / 引理 `hom_eq_zero₁`

English:
lemma hom_eq_zero₁
  given: (i' j' : ι') (hi' : forall i, e.f i != i')
  proof: (isZero_extend_X _ _ _ hi').eq_of_src _ _

中文:
引理 hom_eq_zero₁
  条件: (i' j' : ι') (hi' : 对任意 i, e.f i != i')
  证明: (isZero_extend_X _ _ _ hi').eq_of_src _ _

Depends on / 依赖: eq_of_src, isZero_extend_X
-/
lemma hom_eq_zero₁ (i' j' : ι') (hi' : forall i, e.f i != i') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hi').eq_of_src _ _

/--
lemma `hom_eq_zero₂` / 引理 `hom_eq_zero₂`

English:
lemma hom_eq_zero₂
  given: (i' j' : ι') (hj' : forall j, e.f j != j')
  proof: (isZero_extend_X _ _ _ hj').eq_of_tgt _ _

中文:
引理 hom_eq_zero₂
  条件: (i' j' : ι') (hj' : 对任意 j, e.f j != j')
  证明: (isZero_extend_X _ _ _ hj').eq_of_tgt _ _

Depends on / 依赖: eq_of_tgt, isZero_extend_X
-/
lemma hom_eq_zero₂ (i' j' : ι') (hj' : forall j, e.f j != j') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hj').eq_of_tgt _ _

/--
lemma `hom_eq` / 引理 `hom_eq`

English:
lemma hom_eq
  given: {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j')
  proof: homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

中文:
引理 hom_eq
  条件: {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j')
  证明: homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

Depends on / 依赖: e.r_eq_some, homAux_eq, r_eq_some
-/
lemma hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    hom e φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendXIso e hj).inv :=
  homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

end extend

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
  body: extend.hom e h.hom
  comm i' := by
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [extendMap_f _ _ rfl]; rw [extendMap_f _ _ rfl]; rw [h.comm i]; rw [Preadditive.add_comp]; rw [Preadditive.add_comp]; rw [Preadditive.comp_add]; rw [Preadditive.comp_add]; rw [add_left_inj]
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
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [extend.hom_eq _ _ rfl rfl]; rw [h.zero _ _ (by rwa [← e.rel_iff]),
          zero_comp, comp_zero]
      · exact extend.hom_eq_zero₂ _ _ _ _ (by tauto)
    · exact extend.hom_eq_zero₁ _ _ _ _ (by tauto)

中文:
定义 extend
  签名: (h : 同伦 f g) (e : c.嵌入 c') [e.是RelIff]
  定义体: extend.hom e h.hom
  comm i' := by
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [extendMap_f _ _ rfl]; rw [extendMap_f _ _ rfl]; rw [h.comm i]; rw [Preadditive.add_comp]; rw [Preadditive.add_comp]; rw [Preadditive.comp_add]; rw [Preadditive.comp_add]; rw [add_left_inj]
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
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [extend.hom_eq _ _ rfl rfl]; rw [h.zero _ _ (by rwa [← e.rel_iff]),
          zero_comp, comp_zero]
      · exact extend.hom_eq_zero₂ _ _ _ _ (by tauto)
    · exact extend.hom_eq_zero₁ _ _ _ _ (by tauto)

Depends on / 依赖: extend, extend.hom, h.hom
-/
noncomputable def extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    Homotopy (extendMap f e) (extendMap g e) where
  hom := extend.hom e h.hom
  comm i' := by
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [extendMap_f _ _ rfl]; rw [extendMap_f _ _ rfl]; rw [h.comm i]; rw [Preadditive.add_comp]; rw [Preadditive.add_comp]; rw [Preadditive.comp_add]; rw [Preadditive.comp_add]; rw [add_left_inj]
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
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [extend.hom_eq _ _ rfl rfl]; rw [h.zero _ _ (by rwa [← e.rel_iff]),
          zero_comp, comp_zero]
      · exact extend.hom_eq_zero₂ _ _ _ _ (by tauto)
    · exact extend.hom_eq_zero₁ _ _ _ _ (by tauto)

/--
lemma `extend_hom_eq` / 引理 `extend_hom_eq`

English:
lemma extend_hom_eq
  statement: (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
  proof: extend.hom_eq _ _ _ _

中文:
引理 extend_hom_eq
  结论: (h : 同伦 f g) (e : c.嵌入 c') [e.是RelIff]
  证明: extend.hom_eq _ _ _ _

Depends on / 依赖: extend, extend.hom_eq, hom_eq
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
/--
Definition of `ofExtend` / `ofExtend` 的定义

English:
definition ofExtend
  signature: {e : c.Embedding c'} [e.IsRelIff]
  body: (K.extendXIso e rfl).inv ≫ h.hom (e.f i) (e.f j) ≫ (L.extendXIso e rfl).hom
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

中文:
定义 ofExtend
  签名: {e : c.嵌入 c'} [e.是RelIff]
  定义体: (K.extendXIso e rfl).inv ≫ h.hom (e.f i) (e.f j) ≫ (L.extendXIso e rfl).hom
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

Depends on / 依赖: K.extendXIso, L.extendXIso, extendXIso, h.hom
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
/--
lemma `extend_ofExtend` / 引理 `extend_ofExtend`

English:
lemma extend_ofExtend
  statement: {e : c.Embedding c'} [e.IsRelIff]
  proof: by
  ext i' j'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : exists j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      simp [extend_hom_eq _ e rfl rfl, ofExtend_hom]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

@[simp]

中文:
引理 extend_ofExtend
  结论: {e : c.嵌入 c'} [e.是RelIff]
  证明: by
  ext i' j'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : exists j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      simp [extend_hom_eq _ e rfl rfl, ofExtend_hom]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

@[simp]

Depends on / 依赖: eq_of_src, eq_of_tgt, extend_hom_eq, isZero_extend_X, ofExtend_hom
-/
lemma extend_ofExtend {e : c.Embedding c'} [e.IsRelIff]
    (h : Homotopy (extendMap f e) (extendMap g e)) :
    (ofExtend h).extend e = h := by
  ext i' j'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : exists j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      simp [extend_hom_eq _ e rfl rfl, ofExtend_hom]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

@[simp]
/--
lemma `ofExtend_extend` / 引理 `ofExtend_extend`

English:
lemma ofExtend_extend
  given: (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
  proof: by
  ext i j
  simp [ofExtend_hom, h.extend_hom_eq e rfl rfl]

中文:
引理 ofExtend_extend
  条件: (h : 同伦 f g) (e : c.嵌入 c') [e.是RelIff]
  证明: by
  ext i j
  simp [ofExtend_hom, h.extend_hom_eq e rfl rfl]

Depends on / 依赖: extend_hom_eq, h.extend_hom_eq, ofExtend_hom
-/
lemma ofExtend_extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).ofExtend = h := by
  ext i j
  simp [ofExtend_hom, h.extend_hom_eq e rfl rfl]


/--
Definition of `extendEquiv` / `extendEquiv` 的定义

English:
definition extendEquiv
  signature: (e : c.Embedding c') [e.IsRelIff]
  body: h.extend e
  invFun h := h.ofExtend
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 extendEquiv
  签名: (e : c.嵌入 c') [e.是RelIff]
  定义体: h.extend e
  invFun h := h.ofExtend
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: extend, h.extend
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

/--
Definition of `extendHomotopyFunctor` / `extendHomotopyFunctor` 的定义

English:
definition extendHomotopyFunctor
  signature: :
  body: CategoryTheory.Quotient.lift _ (e.extendFunctor C ⋙ HomotopyCategory.quotient C c') (by
    rintro K L f₁ f₂ ⟨h⟩
    exact HomotopyCategory.eq_of_homotopy _ _ (h.extend e))

中文:
定义 extendHomotopyFunctor
  签名: :
  定义体: CategoryTheory.Quotient.lift _ (e.extendFunctor C ⋙ HomotopyCategory.quotient C c') (by
    rintro K L f₁ f₂ ⟨h⟩
    exact HomotopyCategory.eq_of_homotopy _ _ (h.extend e))

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, HomotopyCategory, HomotopyCategory.eq_of_homotopy, HomotopyCategory.quotient, Quotient, e.extendFunctor, eq_of_homotopy, extend, extendFunctor, h.extend, quotient
-/
noncomputable def extendHomotopyFunctor :
    HomotopyCategory C c ⥤ HomotopyCategory C c' :=
  CategoryTheory.Quotient.lift _ (e.extendFunctor C ⋙ HomotopyCategory.quotient C c') (by
    rintro K L f₁ f₂ ⟨h⟩
    exact HomotopyCategory.eq_of_homotopy _ _ (h.extend e))

/--
Definition of `extendHomotopyFunctorFactors` / `extendHomotopyFunctorFactors` 的定义

English:
definition extendHomotopyFunctorFactors
  signature: :
  body: Iso.refl _

中文:
定义 extendHomotopyFunctorFactors
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def extendHomotopyFunctorFactors :
    HomotopyCategory.quotient C c ⋙ e.extendHomotopyFunctor C ≅
      e.extendFunctor C ⋙ HomotopyCategory.quotient C c' :=
  Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (e.extendHomotopyFunctor C).Full
  body: by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ : K.extend e ⟶ L.extend e, rfl⟩ :=
      (HomotopyCategory.quotient C c').map_surjective φ
    obtain ⟨φ, rfl⟩ := (e.extendFunctor C).map_surjective φ
    exact ⟨(HomotopyCategory.quotient _ _).map φ, rfl⟩

中文:
实例 :
  签名: (e.extendHomotopyFunctor C).满
  定义体: by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ : K.extend e ⟶ L.extend e, rfl⟩ :=
      (HomotopyCategory.quotient C c').map_surjective φ
    obtain ⟨φ, rfl⟩ := (e.extendFunctor C).map_surjective φ
    exact ⟨(HomotopyCategory.quotient _ _).map φ, rfl⟩

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_surjective, K.extend, L.extend, e.extendFunctor, extend, extendFunctor, map_surjective, quotient, quotient_obj_surjective
-/
instance : (e.extendHomotopyFunctor C).Full where
  map_surjective {K L} φ := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ : K.extend e ⟶ L.extend e, rfl⟩ :=
      (HomotopyCategory.quotient C c').map_surjective φ
    obtain ⟨φ, rfl⟩ := (e.extendFunctor C).map_surjective φ
    exact ⟨(HomotopyCategory.quotient _ _).map φ, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (e.extendHomotopyFunctor C).Faithful
  body: by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ₁, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₁
    obtain ⟨φ₂, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (.ofExtend (HomotopyCategory.homotopyOfEq _ _ hφ))

中文:
实例 :
  签名: (e.extendHomotopyFunctor C).忠实
  定义体: by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ₁, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₁
    obtain ⟨φ₂, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (.ofExtend (HomotopyCategory.homotopyOfEq _ _ hφ))

Depends on / 依赖: HomotopyCategory, HomotopyCategory.eq_of_homotopy, HomotopyCategory.homotopyOfEq, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_surjective, eq_of_homotopy, homotopyOfEq, map_surjective, ofExtend, quotient, quotient_obj_surjective
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
/--
lemma `HomologicalComplex.homotopyEquivalences_extendMap_iff` / 引理 `HomologicalComplex.homotopyEquivalences_extendMap_iff`

English:
lemma HomologicalComplex.homotopyEquivalences_extendMap_iff
  proof: by
  #adaptation_note /-- Prior to nightly-2026-05-07, `dsimp%` was used directly inline as the last
  argument to the original `simp`; it now reports `made no progress` so we apply
  `NatIso.isIso_map_iff` via a `change` + `rw` after the rest of the simp set has done its work. -/
  simp only [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (e.extendHomotopyFunctor C)]
  change _ ↔ IsIso ((HomotopyCategory.quotient C c ⋙ e.extendHomotopyFunctor C).map f)
  rw [NatIso.isIso_map_iff (e.extendHomotopyFunctorFactors C) f]
  rfl

中文:
引理 同调复形.homotopyEquivalences_extendMap_iff
  证明: by
  #adaptation_note /-- Prior to nightly-2026-05-07, `dsimp%` was used directly inline as the last
  argument to the original `simp`; it now reports `made no progress` so we apply
  `NatIso.isIso_map_iff` via a `change` + `rw` after the rest of the simp set has done its work. -/
  simp only [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (e.extendHomotopyFunctor C)]
  change _ ↔ IsIso ((HomotopyCategory.quotient C c ⋙ e.extendHomotopyFunctor C).map f)
  rw [NatIso.isIso_map_iff (e.extendHomotopyFunctorFactors C) f]
  rfl

Depends on / 依赖: HomotopyCa, HomotopyCategory, HomotopyCategory.inverseImage_quotient_isomorphisms, MorphismProperty, MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff, NatIso, NatIso.isIso_map_iff, adaptation_note, argument, directly, e.extendHomotopyFunctor, extendHomotopyFunctor, infer_instance, inline, inverseImage_iff, inverseImage_quotient_isomorphisms, isIso_iff_of_reflects_iso, isIso_map_iff, isomorphisms
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
