/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Homological complexes supported in a single degree

We define `single V j c : V ⥤ HomologicalComplex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

In `ChainComplex.toSingle₀Equiv` we characterize chain maps to an
`ℕ`-indexed complex concentrated in degree 0; they are equivalent to
`{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

/-- The functor `V ⥤ HomologicalComplex V c` creating a chain complex supported in a single degree.
-/
/-
**HomologicalComplex.single** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：single (j : ι) : V ⥤ HomologicalComplex V c where obj A
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `V ⥤ HomologicalComplex V c` creating a chain complex supported in a
 single degree.
-/
noncomputable def single (j : ι) : V ⥤ HomologicalComplex V c where
  obj A :=
    { X := fun i => if i = j then A else 0
      d := fun _ _ => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
  map_id A := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · #adaptation_note /-- nightly-2024-03-07
      previously was `rw [if_neg h]; simp`, but that fails with "motive not type correct"
      This is because dsimp does not simplify numerals;
      this note should be removable once https://github.com/leanprover/lean4/pull/8433 lands. -/
      convert! (id_zero (C := V)).symm
      all_goals simp [if_neg h]
  map_comp f g := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · simp

variable {V}

@[simp]
/-
**HomologicalComplex.single_obj_X_self** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：single_obj_X_self (j : ι) (A : V) : ((single V c j).obj A).X j = A
参数：j : ι；A : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma single_obj_X_self (j : ι) (A : V) :
    ((single V c j).obj A).X j = A := if_pos rfl
/-
**HomologicalComplex.isZero_single_obj_X** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：isZero_single_obj_X (j : ι) (A : V) (i : ι) (hi : i != j) : IsZero (((sing
le V c j).obj A).X i)
参数：j : ι；A : V；i : ι；hi : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma isZero_single_obj_X (j : ι) (A : V) (i : ι) (hi : i ≠ j) :
    IsZero (((single V c j).obj A).X i) := by
  dsimp [single]
  rw [if_neg hi]
  exact Limits.isZero_zero V

/-- The object in degree `i` of `(single V c h).obj A` is just `A` when `i = j`. -/
/-
**HomologicalComplex.singleObjXIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex`。
形式化陈述：singleObjXIsoOfEq (j : ι) (A : V) (i : ι) (hi : i = j) : ((single V c j).o
bj A).X i ≅ A
参数：j : ι；A : V；i : ι；hi : i = j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in degree `i` of `(single V c h).obj A` is just `A` when `i = j`.
-/
noncomputable def singleObjXIsoOfEq (j : ι) (A : V) (i : ι) (hi : i = j) :
    ((single V c j).obj A).X i ≅ A :=
  eqToIso (by subst hi; simp [single])

/-- The object in degree `j` of `(single V c h).obj A` is just `A`. -/
/-
**HomologicalComplex.singleObjXSelf** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A
参数：j : ι；A : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in degree `j` of `(single V c h).obj A` is just `A`.
-/
noncomputable def singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A :=
  singleObjXIsoOfEq c j A j rfl

@[simp]
/-
**HomologicalComplex.single_obj_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：single_obj_d (j : ι) (A : V) (k l : ι) : ((single V c j).obj A).d k l = 0
参数：j : ι；A : V；k l : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single_obj_d (j : ι) (A : V) (k l : ι) :
    ((single V c j).obj A).d k l = 0 := rfl

@[reassoc]
/-
**HomologicalComplex.single_map_f_self** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) : ((single V c j).map f).f
 j = (singleObjXSelf c j A).hom ≫ f ≫ (singleObjXSelf c j B).inv
参数：j : ι；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫
      f ≫ (singleObjXSelf c j B).inv := by
  dsimp [single]
  rw [dif_pos rfl]
  rfl

variable (V)

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `single V c j ⋙ eval V c j ≅ 𝟭 V`. -/
@[simps!]
/-
**HomologicalComplex.singleCompEvalIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `Homologica
lComplex`。
形式化陈述：singleCompEvalIsoSelf (j : ι) : single V c j ⋙ eval V c j ≅ 𝟭 V
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `single V c j ⋙ eval V c j ≅ 𝟭 V`.
-/
noncomputable def singleCompEvalIsoSelf (j : ι) : single V c j ⋙ eval V c j ≅ 𝟭 V :=
  NatIso.ofComponents (singleObjXSelf c j) (fun {A B} f => by simp [single_map_f_self])
/-
**HomologicalComplex.isZero_single_comp_eval** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：isZero_single_comp_eval (j i : ι) (hi : i != j) : IsZero (single V c j ⋙ e
val V c i)
参数：j i : ι；hi : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isZero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (F
 : CategoryTheory.F…
· 使用引理 `HomologicalComplex.isZero_single_obj_X`：isZero_single_obj_X (j : ι) (A :
 V) (i : ι) (hi : i != j) : IsZero (((single V c j).obj A).X i)
-/
lemma isZero_single_comp_eval (j i : ι) (hi : i ≠ j) : IsZero (single V c j ⋙ eval V c i) :=
  Functor.isZero _ (fun _ ↦ isZero_single_obj_X c _ _ _ hi)

variable {V c}

@[ext]
/-
**HomologicalComplex.from_single_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：from_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V} {f g : (s
ingle V c j).obj A ⟶ K} (hfg : f.f j = g.f j) : f = g
参数：single V c j；hfg : f.f j = g.f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_single_obj_X`：isZero_single_obj_X (j : ι) (A :
 V) (i : ι) (hi : i != j) : IsZero (((single V c j).obj A).X i)
-/
lemma from_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : (single V c j).obj A ⟶ K} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_src

@[ext]
/-
**HomologicalComplex.to_single_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：to_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V} {f g : K ⟶ 
(single V c j).obj A} (hfg : f.f j = g.f j) : f = g
参数：single V c j；hfg : f.f j = g.f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `HomologicalComplex.isZero_single_obj_X`：isZero_single_obj_X (j : ι) (A :
 V) (i : ι) (hi : i != j) : IsZero (((single V c j).obj A).X i)
-/
lemma to_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : K ⟶ (single V c j).obj A} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_tgt
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : ι) : (single V c j).Faithful where
  map_injective {A B f g} w := by
    rw [← cancel_mono (singleObjXSelf c j B).inv,
      ← cancel_epi (singleObjXSelf c j A).hom, ← single_map_f_self,
      ← single_map_f_self, w]
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : ι) : (single V c j).Full where
  map_surjective {A B} f :=
    ⟨(singleObjXSelf c j A).inv ≫ f.f j ≫ (singleObjXSelf c j B).hom, by
      ext
      simp [single_map_f_self]⟩

/-- Constructor for morphisms to a single homological complex. -/
/-
**HomologicalComplex.mkHomToSingle** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：mkHomToSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
 (hφ : forall (i : ι), c.Rel i j -> K.d i j ≫ φ = 0) : K ⟶ (single V c j).obj A 
where f i
参数：φ : K.X j ⟶ A；hφ : forall (i : ι), c.Rel i j -> K.d i j ≫ φ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to a single homological complex.
-/
noncomputable def mkHomToSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : ∀ (i : ι), c.Rel i j → K.d i j ≫ φ = 0) :
    K ⟶ (single V c j).obj A where
  f i :=
    if hi : i = j
      then (K.XIsoOfEq hi).hom ≫ φ ≫ (singleObjXIsoOfEq c j A i hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [comp_zero]
    split_ifs with hk
    · subst hk
      simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, reassoc_of% hφ i hik, zero_comp]
    · apply (isZero_single_obj_X c j A k hk).eq_of_tgt

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**HomologicalComplex.mkHomToSingle_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：mkHomToSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ 
A) (hφ : forall (i : ι), c.Rel i j -> K.d i j ≫ φ = 0) : (mkHomToSingle φ hφ).f 
j = φ ≫ (singleObjXSelf c j A).inv
参数：φ : K.X j ⟶ A；hφ : forall (i : ι), c.Rel i j -> K.d i j ≫ φ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mkHomToSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : ∀ (i : ι), c.Rel i j → K.d i j ≫ φ = 0) :
    (mkHomToSingle φ hφ).f j = φ ≫ (singleObjXSelf c j A).inv := by
  dsimp [mkHomToSingle]
  rw [dif_pos rfl, id_comp]
  rfl

/-- Constructor for morphisms from a single homological complex. -/
/-
**HomologicalComplex.mkHomFromSingle** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：mkHomFromSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X 
j) (hφ : forall (k : ι), c.Rel j k -> φ ≫ K.d j k = 0) : (single V c j).obj A ⟶ 
K where f i
参数：φ : A ⟶ K.X j；hφ : forall (k : ι), c.Rel j k -> φ ≫ K.d j k = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from a single homological complex.
-/
noncomputable def mkHomFromSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : ∀ (k : ι), c.Rel j k → φ ≫ K.d j k = 0) :
    (single V c j).obj A ⟶ K where
  f i :=
    if hi : i = j
      then (singleObjXIsoOfEq c j A i hi).hom ≫ φ ≫ (K.XIsoOfEq hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [zero_comp]
    split_ifs with hi
    · subst hi
      simp only [XIsoOfEq_rfl, Iso.refl_inv, comp_id, assoc, hφ k hik, comp_zero]
    · apply (isZero_single_obj_X c j A i hi).eq_of_src

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**HomologicalComplex.mkHomFromSingle_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：mkHomFromSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.
X j) (hφ : forall (k : ι), c.Rel j k -> φ ≫ K.d j k = 0) : (mkHomFromSingle φ hφ
).f j = (singleObjXSelf c j A).hom ≫ φ
参数：φ : A ⟶ K.X j；hφ : forall (k : ι), c.Rel j k -> φ ≫ K.d j k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mkHomFromSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : ∀ (k : ι), c.Rel j k → φ ≫ K.d j k = 0) :
    (mkHomFromSingle φ hφ).f j = (singleObjXSelf c j A).hom ≫ φ := by
  dsimp [mkHomFromSingle]
  rw [dif_pos rfl, comp_id]
  rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : ι) : (single V c j).PreservesZeroMorphisms where

end HomologicalComplex

namespace ChainComplex

/-- The functor `V ⥤ ChainComplex V ℕ` creating a chain complex supported in degree zero. -/
/-
**ChainComplex.single** 是 Mathlib 中的一个缩写定义，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `V ⥤ ChainComplex V ℕ` creating a chain complex supported in degree 
zero.
-/
noncomputable abbrev single₀ : V ⥤ ChainComplex V ℕ :=
  HomologicalComplex.single V (ComplexShape.down ℕ) 0

variable {V}

@[simp]
/-
**ChainComplex.single** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**ChainComplex.single** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id, id_comp]


@[simp]
/-
**ChainComplex.single** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X = Iso.refl _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from an `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
@[simps apply_coe]
/-
**ChainComplex.toSingle** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms from an `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
noncomputable def toSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } where
  toFun φ := ⟨φ.f 0, by rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ChainComplex.toSingle** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSingle₀Equiv_symm_apply_f_zero {C : ChainComplex V ℕ} {X : V}
    (f : C.X 0 ⟶ X) (hf : C.d 1 0 ≫ f = 0) :
    ((toSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [toSingle₀Equiv]

set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms from a single object chain complex with `X` concentrated in degree 0
to an `ℕ`-indexed chain complex `C` are the same as morphisms `f : X → C.X 0`.
-/
@[simps apply]
/-
**ChainComplex.fromSingle** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms from a single object chain complex with `X` concentrated in degree 0
to an `ℕ`-indexed chain complex `C` are the same as morphisms `f : X → C.X 0`.
-/
noncomputable def fromSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ (X ⟶ C.X 0) where
  toFun f := f.f 0
  invFun f := HomologicalComplex.mkHomFromSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ChainComplex.fromSingle** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSingle₀Equiv_symm_apply_f_zero
    {C : ChainComplex V ℕ} {X : V} (f : X ⟶ C.X 0) :
    dsimp% ((fromSingle₀Equiv C X).symm f).f 0 = f := by
  simp [fromSingle₀Equiv]

@[simp]
/-
**ChainComplex.fromSingle** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSingle₀Equiv_symm_apply_f_succ
    {C : ChainComplex V ℕ} {X : V} (f : X ⟶ C.X 0) (n : ℕ) :
    ((fromSingle₀Equiv C X).symm f).f (n + 1) = 0 := rfl

end ChainComplex

namespace CochainComplex

/-- The functor `V ⥤ CochainComplex V ℕ` creating a cochain complex supported in degree zero. -/
/-
**CochainComplex.single** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `V ⥤ CochainComplex V ℕ` creating a cochain complex supported in deg
ree zero.
-/
noncomputable abbrev single₀ : V ⥤ CochainComplex V ℕ :=
  HomologicalComplex.single V (ComplexShape.up ℕ) 0

variable {V}

@[simp]
/-
**CochainComplex.single** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CochainComplex.single** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id, id_comp]

@[simp]
/-
**CochainComplex.single** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X = Iso.refl _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`. -/
@[simps apply_coe]
/-
**CochainComplex.fromSingle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms from a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`.
-/
noncomputable def fromSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.X 0 // f ≫ C.d 0 1 = 0 } where
  toFun φ := ⟨φ.f 0, by rw [φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CochainComplex.fromSingle** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSingle₀Equiv_symm_apply_f_zero {C : CochainComplex V ℕ} {X : V}
    (f : X ⟶ C.X 0) (hf : f ≫ C.d 0 1 = 0) :
    ((fromSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [fromSingle₀Equiv]

set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms to a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C` are the same as morphisms `f : C.X 0 ⟶ X`.
-/
@[simps apply]
/-
**CochainComplex.toSingle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms to a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C` are the same as morphisms `f : C.X 0 ⟶ X`.
-/
noncomputable def toSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ (C.X 0 ⟶ X) where
  toFun f := f.f 0
  invFun f := HomologicalComplex.mkHomToSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CochainComplex.toSingle** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSingle₀Equiv_symm_apply_f_zero
    {C : CochainComplex V ℕ} {X : V} (f : C.X 0 ⟶ X) :
    ((toSingle₀Equiv C X).symm f).f 0 = f := by
  simp [toSingle₀Equiv]

@[simp]
/-
**CochainComplex.toSingle** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSingle₀Equiv_symm_apply_f_succ
    {C : CochainComplex V ℕ} {X : V} (f : C.X 0 ⟶ X) (n : ℕ) :
    ((toSingle₀Equiv C X).symm f).f (n + 1) = 0 := by
  rfl

end CochainComplex

