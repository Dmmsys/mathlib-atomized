/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homology of the extension of a homological complex

Given an embedding `e : c.Embedding c'` and `K : HomologicalComplex C c`, we shall
compute the homology of `K.extend e`. In degrees that are not in the image of `e.f`,
the homology is obviously zero. When `e.f j = j`, we construct an isomorphism
`(K.extend e).homology j' ≅ K.homology j`.

-/

@[expose] public section

open CategoryTheory Limits Category

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

section HomologyData

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

include hk hk' in
/-
**HomologicalComplex.extend.comp_d_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.extend`。
形式化陈述：comp_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ K.X j) : φ ≫ K.d j k = 0 ↔ φ ≫ (K.exte
ndXIso e hj').inv ≫ (K.extend e).d j' k' = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `ComplexShape.Embedding.rel`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (self : c.Embedding c') {i₁ i₂ : ι},   c.Rel i₁
 i₂ → c'.Rel (se…
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用引理 `HomologicalComplex.extend_d_from_eq_zero`：extend_d_from_eq_zero (i' j' :
 ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) : (K.extend e).d i' 
j' = 0
-/
lemma comp_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ K.X j) :
    φ ≫ K.d j k = 0 ↔ φ ≫ (K.extendXIso e hj').inv ≫ (K.extend e).d j' k' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk', Iso.inv_hom_id_assoc,
      ← cancel_mono (K.extendXIso e hk').inv, zero_comp, assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K.extend_d_from_eq_zero e j' k' j hj', comp_zero, comp_zero]
    rw [hk]
    exact hjk

include hi hi' in
/-
**HomologicalComplex.extend.d_comp_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.extend`。
形式化陈述：d_comp_eq_zero_iff ⦃W : C⦄ (φ : K.X j ⟶ W) : K.d i j ≫ φ = 0 ↔ (K.extend e
).d i' j' ≫ (K.extendXIso e hj').hom ≫ φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `ComplexShape.Embedding.rel`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (self : c.Embedding c') {i₁ i₂ : ι},   c.Rel i₁
 i₂ → c'.Rel (se…
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用引理 `HomologicalComplex.extend_d_to_eq_zero`：extend_d_to_eq_zero (i' j' : ι')
 (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) : (K.extend e).d i' j' =
 0
-/
lemma d_comp_eq_zero_iff ⦃W : C⦄ (φ : K.X j ⟶ W) :
    K.d i j ≫ φ = 0 ↔ (K.extend e).d i' j' ≫ (K.extendXIso e hj').hom ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj', assoc, assoc, Iso.inv_hom_id_assoc,
      ← cancel_epi (K.extendXIso e hi').hom, comp_zero]
  · simp only [K.shape _ _ hij, zero_comp, true_iff]
    rw [K.extend_d_to_eq_zero e i' j' j hj', zero_comp]
    rw [hi]
    exact hij

namespace leftHomologyData

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)

/-- The kernel fork of `(K.extend e).d j' k'` that is deduced from a kernel
fork of `K.d j k `. -/
@[simp]
/-
**HomologicalComplex.extend.leftHomologyData.kernelFork** 是 Mathlib 中的一个定义，位于命名空
间 `HomologicalComplex.extend.leftHomologyData`。
形式化陈述：kernelFork : KernelFork ((K.extend e).d j' k')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel fork of `(K.extend e).d j' k'` that is deduced from a kernel
fork of `K.d j k `.
-/
noncomputable def kernelFork : KernelFork ((K.extend e).d j' k') :=
  KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

/-- The limit kernel fork of `(K.extend e).d j' k'` that is deduced from a limit
kernel fork of `K.d j k `. -/
/-
**HomologicalComplex.extend.leftHomologyData.isLimitKernelFork** 是 Mathlib 中的一个定
义，位于命名空间 `HomologicalComplex.extend.leftHomologyData`。
形式化陈述：isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend.comp_d_eq_zero_iff`：comp_d_eq_zero_iff ⦃W : C⦄
 (φ : W ⟶ K.X j) : φ ≫ K.d j k = 0 ↔ φ ≫ (K.extendXIso e hj').inv ≫ (K.extend e)
.d j' k' = 0

--- 原说明 ---
The limit kernel fork of `(K.extend e).d j' k'` that is deduced from a limit
kernel fork of `K.d j k `.
-/
noncomputable def isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone) :=
  KernelFork.isLimitOfIsLimitOfIff hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

include hi hi' hcone in
/-- Auxiliary lemma for `lift_d_comp_eq_zero_iff`. -/
/-
**HomologicalComplex.extend.leftHomologyData.lift_d_comp_eq_zero_iff'** 是 Mathli
b 中的一个引理，位于命名空间 `HomologicalComplex.extend.leftHomologyData`。
形式化陈述：lift_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt) (hf' : f' ≫ cone.ι
 = K.d i j) (f'' : (K.extend e).X i' ⟶ cone.pt) (hf'' : f'' ≫ cone.ι ≫ (extendXI
so K e hj').inv = (K.extend e).d i' j') (φ : cone.pt ⟶ W) : f' ≫ φ = 0 ↔ f'' ≫ φ
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `ComplexShape.Embedding.rel`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (self : c.Embedding c') {i₁ i₂ : ι},   c.Rel i₁
 i₂ → c'.Rel (se…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.extend_d_to_eq_zero`：extend_d_to_eq_zero (i' j' : ι')
 (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) : (K.extend e).d i' j' =
 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Auxiliary lemma for `lift_d_comp_eq_zero_iff`.
-/
lemma lift_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt)
    (hf' : f' ≫ cone.ι = K.d i j)
    (f'' : (K.extend e).X i' ⟶ cone.pt)
    (hf'' : f'' ≫ cone.ι ≫ (extendXIso K e hj').inv = (K.extend e).d i' j')
    (φ : cone.pt ⟶ W) :
    f' ≫ φ = 0 ↔ f'' ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc, hf', ← cancel_mono (extendXIso K e hj').inv, assoc, assoc, hf'',
        K.extend_d_eq e hi'' hj']
    rw [← cancel_epi (K.extendXIso e hi'').hom, comp_zero, ← this, assoc]
  · have h₁ : f' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      simp only [zero_comp, hf', K.shape _ _ hij]
    have h₂ : f'' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      rw [← cancel_mono (extendXIso K e hj').inv, assoc, hf'', zero_comp, zero_comp,
        K.extend_d_to_eq_zero e i' j' j hj']
      rw [hi]
      exact hij
    simp [h₁, h₂]

include hi hi' in
/-
**HomologicalComplex.extend.leftHomologyData.lift_d_comp_eq_zero_iff** 是 Mathlib
 中的一个引理，位于命名空间 `HomologicalComplex.extend.leftHomologyData`。
形式化陈述：lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) : hcone.lift (KernelFork
.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔ ((isLimitKernelFork K e hj' hk hk' 
cone hcone).lift (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend.leftHomologyData.lift_d_comp_eq_zero_iff'`：lif
t_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt) (hf' : f' ≫ cone.ι = K.d i 
j) (f'' : (K.extend e).X i' ⟶ cone.pt) (hf'' : f'' ≫ cone…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 :=
  lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

/-- Auxiliary definition for `extend.leftHomologyData`. -/
/-
**HomologicalComplex.extend.leftHomologyData.cokernelCofork** 是 Mathlib 中的一个定义，位
于命名空间 `HomologicalComplex.extend.leftHomologyData`。
形式化陈述：cokernelCofork : CokernelCofork ((isLimitKernelFork K e hj' hk hk' cone hc
one).lift (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _)))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0

--- 原说明 ---
Auxiliary definition for `extend.leftHomologyData`.
-/
noncomputable def cokernelCofork :
    CokernelCofork ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) :=
  CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)

/-- Auxiliary definition for `extend.leftHomologyData`. -/
/-
**HomologicalComplex.extend.leftHomologyData.isColimitCokernelCofork** 是 Mathlib
 中的一个定义，位于命名空间 `HomologicalComplex.extend.leftHomologyData`。
形式化陈述：isColimitCokernelCofork : IsColimit (cokernelCofork K e hj' hi hi' hk hk' 
cone hcone cocone)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `HomologicalComplex.extend.leftHomologyData.lift_d_comp_eq_zero_iff`：lift
_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) : hcone.lift (KernelFork.ofι (K.d 
i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔ ((isLimitKernelFork K…

--- 原说明 ---
Auxiliary definition for `extend.leftHomologyData`.
-/
noncomputable def isColimitCokernelCofork :
    IsColimit (cokernelCofork K e hj' hi hi' hk hk' cone hcone cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff' hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)

end leftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open leftHomologyData in
/-- The left homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a left homology data of `K.sc' i j k`. -/
@[simps]
/-
**HomologicalComplex.extend.leftHomologyData** 是 Mathlib 中的一个定义，位于命名空间 `Homologi
calComplex.extend`。
形式化陈述：leftHomologyData (h : (K.sc' i j k).LeftHomologyData) : ((K.extend e).sc' 
i' j' k').LeftHomologyData where K
参数：h : (K.sc' i j k).LeftHomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a left homology data of `K.sc' i j k`.
-/
noncomputable def leftHomologyData (h : (K.sc' i j k).LeftHomologyData) :
    ((K.extend e).sc' i' j' k').LeftHomologyData where
  K := h.K
  H := h.H
  i := h.i ≫ (extendXIso K e hj').inv
  π := h.π
  wi := by
    dsimp
    rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk']
    exact h.wi
  hi := isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    dsimp
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact h.wπ
  hπ := isColimitCokernelCofork K e hj' hi hi' hk hk' _ h.hi _ h.hπ

namespace rightHomologyData

variable (cocone : CokernelCofork (K.d i j)) (hcocone : IsColimit cocone)

/-- The cokernel cofork of `(K.extend e).d i' j'` that is deduced from a cokernel
cofork of `K.d i j`. -/
@[simp]
/-
**HomologicalComplex.extend.rightHomologyData.cokernelCofork** 是 Mathlib 中的一个定义，
位于命名空间 `HomologicalComplex.extend.rightHomologyData`。
形式化陈述：cokernelCofork : CokernelCofork ((K.extend e).d i' j')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel cofork of `(K.extend e).d i' j'` that is deduced from a cokernel
cofork of `K.d i j`.
-/
noncomputable def cokernelCofork : CokernelCofork ((K.extend e).d i' j') :=
  CokernelCofork.ofπ ((extendXIso K e hj').hom ≫ cocone.π) (by
    rw [← d_comp_eq_zero_iff K e hj' hi hi' cocone.π, cocone.condition])

/-- The colimit cokernel cofork of `(K.extend e).d i' j'` that is deduced from a
colimit cokernel cofork of `K.d i j`. -/
/-
**HomologicalComplex.extend.rightHomologyData.isColimitCokernelCofork** 是 Mathli
b 中的一个定义，位于命名空间 `HomologicalComplex.extend.rightHomologyData`。
形式化陈述：isColimitCokernelCofork : IsColimit (cokernelCofork K e hj' hi hi' cocone)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend.d_comp_eq_zero_iff`：d_comp_eq_zero_iff ⦃W : C⦄
 (φ : K.X j ⟶ W) : K.d i j ≫ φ = 0 ↔ (K.extend e).d i' j' ≫ (K.extendXIso e hj')
.hom ≫ φ = 0

--- 原说明 ---
The colimit cokernel cofork of `(K.extend e).d i' j'` that is deduced from a
colimit cokernel cofork of `K.d i j`.
-/
noncomputable def isColimitCokernelCofork : IsColimit (cokernelCofork K e hj' hi hi' cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff hcocone ((K.extend e).d i' j')
    (extendXIso K e hj') (d_comp_eq_zero_iff K e hj' hi hi')

variable (cone : KernelFork (hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k))))
  (hcone : IsLimit cone)

include hk hk' hcocone in
/-
**HomologicalComplex.extend.rightHomologyData.d_comp_desc_eq_zero_iff'** 是 Mathl
ib 中的一个引理，位于命名空间 `HomologicalComplex.extend.rightHomologyData`。
形式化陈述：d_comp_desc_eq_zero_iff' ⦃W : C⦄ (f' : cocone.pt ⟶ K.X k) (hf' : cocone.π 
≫ f' = K.d j k) (f'' : cocone.pt ⟶ (K.extend e).X k') (hf'' : (extendXIso K e hj
').hom ≫ cocone.π ≫ f'' = (K.extend e).d j' k') (φ : W ⟶ cocone.pt) : φ ≫ f' = 0
 ↔ φ ≫ f'' = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `ComplexShape.Embedding.rel`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (self : c.Embedding c') {i₁ i₂ : ι},   c.Rel i₁
 i₂ → c'.Rel (se…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.extend_d_from_eq_zero`：extend_d_from_eq_zero (i' j' :
 ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) : (K.extend e).d i' 
j' = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma d_comp_desc_eq_zero_iff' ⦃W : C⦄ (f' : cocone.pt ⟶ K.X k)
    (hf' : cocone.π ≫ f' = K.d j k)
    (f'' : cocone.pt ⟶ (K.extend e).X k')
    (hf'' : (extendXIso K e hj').hom ≫ cocone.π ≫ f'' = (K.extend e).d j' k')
    (φ : W ⟶ cocone.pt) :
    φ ≫ f' = 0 ↔ φ ≫ f'' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : f' ≫ (K.extendXIso e hk'').inv = f'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hf', ← cancel_epi (extendXIso K e hj').hom, hf'',
        K.extend_d_eq e hj' hk'']
    rw [← cancel_mono (K.extendXIso e hk'').inv, zero_comp, assoc, this]
  · have h₁ : f' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      simp only [hf', comp_zero, K.shape _ _ hjk]
    have h₂ : f'' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [← cancel_epi (extendXIso K e hj').hom, hf'', comp_zero, comp_zero,
        K.extend_d_from_eq_zero e j' k' j hj']
      rw [hk]
      exact hjk
    simp [h₁, h₂]

set_option backward.defeqAttrib.useBackward true in
include hk hk' in
/-
**HomologicalComplex.extend.rightHomologyData.d_comp_desc_eq_zero_iff** 是 Mathli
b 中的一个引理，位于命名空间 `HomologicalComplex.extend.rightHomologyData`。
形式化陈述：d_comp_desc_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ cocone.pt) : φ ≫ hcocone.desc (Co
kernelCofork.ofπ (K.d j k) (K.d_comp_d i j k)) = 0 ↔ φ ≫ ((isColimitCokernelCofo
rk K e hj' hi hi' cocone hcocone).desc (CokernelCofork.ofπ ((K.extend e).d j' k'
) (d_comp_d _ _ _ _))) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend.rightHomologyData.d_comp_desc_eq_zero_iff'`：d_
comp_desc_eq_zero_iff' ⦃W : C⦄ (f' : cocone.pt ⟶ K.X k) (hf' : cocone.π ≫ f' = K
.d j k) (f'' : cocone.pt ⟶ (K.extend e).X k') (hf'' : (ext…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma d_comp_desc_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ cocone.pt) :
    φ ≫ hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k)) = 0 ↔
      φ ≫ ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) = 0 :=
  d_comp_desc_eq_zero_iff' K e hj' hk hk' cocone hcocone _ (hcocone.fac _ _) _ (by
    simpa using! (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).fac _
      WalkingParallelPair.one) _

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `extend.rightHomologyData`. -/
/-
**HomologicalComplex.extend.rightHomologyData.kernelFork** 是 Mathlib 中的一个定义，位于命名
空间 `HomologicalComplex.extend.rightHomologyData`。
形式化陈述：kernelFork : KernelFork ((isColimitCokernelCofork K e hj' hi hi' cocone hc
ocone).desc (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _)))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0

--- 原说明 ---
Auxiliary definition for `extend.rightHomologyData`.
-/
noncomputable def kernelFork :
    KernelFork ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) :=
  KernelFork.ofι cone.ι (by
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone]
    exact cone.condition)

/-- Auxiliary definition for `extend.rightHomologyData`. -/
/-
**HomologicalComplex.extend.rightHomologyData.isLimitKernelFork** 是 Mathlib 中的一个
定义，位于命名空间 `HomologicalComplex.extend.rightHomologyData`。
形式化陈述：isLimitKernelFork : IsLimit (kernelFork K e hj' hi hi' hk hk' cocone hcoco
ne cone)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `HomologicalComplex.extend.rightHomologyData.d_comp_desc_eq_zero_iff`：d_c
omp_desc_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ cocone.pt) : φ ≫ hcocone.desc (CokernelCof
ork.ofπ (K.d j k) (K.d_comp_d i j k)) = 0 ↔ φ ≫ ((isColim…

--- 原说明 ---
Auxiliary definition for `extend.rightHomologyData`.
-/
noncomputable def isLimitKernelFork :
    IsLimit (kernelFork K e hj' hi hi' hk hk' cocone hcocone cone) :=
  KernelFork.isLimitOfIsLimitOfIff' hcone _
    (d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone)

end rightHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open rightHomologyData in
/-- The right homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a right homology data of `K.sc' i j k`. -/
@[simps]
/-
**HomologicalComplex.extend.rightHomologyData** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex.extend`。
形式化陈述：rightHomologyData (h : (K.sc' i j k).RightHomologyData) : ((K.extend e).sc
' i' j' k').RightHomologyData where Q
参数：h : (K.sc' i j k).RightHomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a right homology data of `K.sc' i j k`.
-/
noncomputable def rightHomologyData (h : (K.sc' i j k).RightHomologyData) :
    ((K.extend e).sc' i' j' k').RightHomologyData where
  Q := h.Q
  H := h.H
  p := (extendXIso K e hj').hom ≫ h.p
  ι := h.ι
  wp := by
    dsimp
    rw [← d_comp_eq_zero_iff K e hj' hi hi']
    exact h.wp
  hp := isColimitCokernelCofork K e hj' hi hi' _ h.hp
  wι := by
    dsimp
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' _ h.hp]
    exact h.wι
  hι := isLimitKernelFork K e hj' hi hi' hk hk' _ h.hp _ h.hι

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Computation of the `g'` field of `extend.rightHomologyData`. -/
/-
**HomologicalComplex.extend.rightHomologyData_g'** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex.extend`。
形式化陈述：rightHomologyData_g' (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k =
 k') : (rightHomologyData K e hj' hi hi' hk hk' h).g' = h.g' ≫ (K.extendXIso e h
k'').inv
参数：h : (K.sc' i j k).RightHomologyData；hk'' : e.f k = k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instEpiP`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'_assoc`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits
.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `HomologicalComplex.shortComplexFunctor'_obj_g`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} (c : Com…

--- 原说明 ---
Computation of the `g'` field of `extend.rightHomologyData`.
-/
lemma rightHomologyData_g' (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k') :
    (rightHomologyData K e hj' hi hi' hk hk' h).g' = h.g' ≫ (K.extendXIso e hk'').inv := by
  rw [← cancel_epi h.p, ← cancel_epi (extendXIso K e hj').hom]
  have := (rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this, K.extend_d_eq e hj' hk'', h.p_g'_assoc, shortComplexFunctor'_obj_g]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a homology data of `K.sc' i j k`. -/
@[simps]
/-
**HomologicalComplex.extend.homologyData** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex.extend`。
形式化陈述：homologyData (h : (K.sc' i j k).HomologyData) : ((K.extend e).sc' i' j' k'
).HomologyData where left
参数：h : (K.sc' i j k).HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a homology data of `K.sc' i j k`.
-/
noncomputable def homologyData (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc' i' j' k').HomologyData where
  left := leftHomologyData K e hj' hi hi' hk hk' h.left
  right := rightHomologyData K e hj' hi hi' hk hk' h.right
  iso := h.iso

set_option backward.isDefEq.respectTransparency.types false in
/-- The homology data of `(K.extend e).sc j'` that is deduced
from a homology data of `K.sc' i j k`. -/
@[simps!]
/-
**HomologicalComplex.extend.homologyData'** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.extend`。
形式化陈述：homologyData' (h : (K.sc' i j k).HomologyData) : ((K.extend e).sc j').Homo
logyData
参数：h : (K.sc' i j k).HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology data of `(K.extend e).sc j'` that is deduced
from a homology data of `K.sc' i j k`.
-/
noncomputable def homologyData' (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc j').HomologyData :=
  homologyData K e hj' hi rfl hk rfl h

end HomologyData

/-
**HomologicalComplex.extend.hasHomology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex.extend`。
形式化陈述：hasHomology {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] : (K.ex
tend e).HasHomology j'
参数：hj' : e.f j = j'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
-/
lemma hasHomology {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] :
    (K.extend e).HasHomology j' :=
  ShortComplex.HasHomology.mk'
    (homologyData' K e hj' rfl rfl ((K.sc j).homologyData))
/-
**HomologicalComplex.extend.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex.exten
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : ι) [K.HasHomology j] : (K.extend e).HasHomology (e.f j) :=
  hasHomology K e rfl
/-
**HomologicalComplex.extend.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex.exten
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ j, K.HasHomology j] (j' : ι') : (K.extend e).HasHomology j' := by
  by_cases h : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := h
    infer_instance
  · have hj := isZero_extend_X K e j' (by tauto)
    exact ShortComplex.HasHomology.mk'
      (ShortComplex.HomologyData.ofZeros _ (hj.eq_of_tgt _ _) (hj.eq_of_src _ _))

end extend

/-
**HomologicalComplex.extend_exactAt** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：extend_exactAt (j' : ι') (hj' : forall j, e.f j != j') : (K.extend e).Exac
tAt j'
参数：j' : ι'；hj' : forall j, e.f j != j'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.exactAt_of_isSupported`：exactAt_of_isSupported [K.IsS
upported e] (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instIsStrictlySupportedExtend`：∀ {ι : Type u_1} {ι' :
 Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : 
CategoryTheory.Category.{v_1, u_3} C] …
-/
lemma extend_exactAt (j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    (K.extend e).ExactAt j' :=
  exactAt_of_isSupported _ e j' hj'

section

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

/-- The isomorphism `(K.extend e).cycles j' ≅ K.cycles j` when `e.f j = j'`. -/
/-
**HomologicalComplex.extendCyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：extendCyclesIso : (K.extend e).cycles j' ≅ K.cycles j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.extend e).cycles j' ≅ K.cycles j` when `e.f j = j'`.
-/
noncomputable def extendCyclesIso :
    (K.extend e).cycles j' ≅ K.cycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.cyclesIso ≪≫
    (K.sc j).homologyData.left.cyclesIso.symm

/-- The isomorphism `(K.extend e).opcycles j' ≅ K.opcycles j` when `e.f j = j'`. -/
/-
**HomologicalComplex.extendOpcyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex`。
形式化陈述：extendOpcyclesIso : (K.extend e).opcycles j' ≅ K.opcycles j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.extend e).opcycles j' ≅ K.opcycles j` when `e.f j = j'`.
-/
noncomputable def extendOpcyclesIso :
    (K.extend e).opcycles j' ≅ K.opcycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).right.opcyclesIso ≪≫
    (K.sc j).homologyData.right.opcyclesIso.symm

/-- The isomorphism `(K.extend e).homology j' ≅ K.homology j` when `e.f j = j'`. -/
/-
**HomologicalComplex.extendHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex`。
形式化陈述：extendHomologyIso : (K.extend e).homology j' ≅ K.homology j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.extend e).homology j' ≅ K.homology j` when `e.f j = j'`.
-/
noncomputable def extendHomologyIso :
    (K.extend e).homology j' ≅ K.homology j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.homologyIso ≪≫
    (K.sc j).homologyData.left.homologyIso.symm

include hj' in
/-
**HomologicalComplex.extend_exactAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：extend_exactAt_iff : (K.extend e).ExactAt j' ↔ K.ExactAt j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
-/
lemma extend_exactAt_iff :
    (K.extend e).ExactAt j' ↔ K.ExactAt j := by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.extendCyclesIso_hom_iCycles** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：extendCyclesIso_hom_iCycles : (K.extendCyclesIso e hj').hom ≫ K.iCycles j 
= (K.extend e).iCycles j' ≫ (K.extendXIso e hj').hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_
assoc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i`：cycle
sIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
-/
lemma extendCyclesIso_hom_iCycles :
    (K.extendCyclesIso e hj').hom ≫ K.iCycles j =
      (K.extend e).iCycles j' ≫ (K.extendXIso e hj').hom := by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv, Iso.inv_hom_id_assoc]
  dsimp [extendCyclesIso, iCycles]
  rw [assoc, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.extendCyclesIso_inv_iCycles** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：extendCyclesIso_inv_iCycles : (K.extendCyclesIso e hj').inv ≫ (K.extend e)
.iCycles j' = K.iCycles j ≫ (K.extendXIso e hj').inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `HomologicalComplex.extendCyclesIso_hom_iCycles_assoc`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extendCyclesIso_inv_iCycles :
    (K.extendCyclesIso e hj').inv ≫ (K.extend e).iCycles j' =
      K.iCycles j ≫ (K.extendXIso e hj').inv := by
  simp only [← cancel_epi (K.extendCyclesIso e hj').hom, Iso.hom_inv_id_assoc,
    extendCyclesIso_hom_iCycles_assoc, Iso.hom_inv_id, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_extendHomologyIso_hom :
    (K.extend e).homologyπ j' ≫ (K.extendHomologyIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ K.homologyπ j := by
  dsimp [extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ← cancel_mono (K.sc j).homologyData.left.homologyIso.hom,
    assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  dsimp [extendCyclesIso]
  simp only [assoc, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_extendHomologyIso_inv :
    K.homologyπ j ≫ (K.extendHomologyIso e hj').inv =
      (K.extendCyclesIso e hj').inv ≫ (K.extend e).homologyπ j' := by
  simp only [← cancel_mono (K.extendHomologyIso e hj').hom,
    assoc, Iso.inv_hom_id, comp_id, homologyπ_extendHomologyIso_hom, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcycles_extendOpcyclesIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `
HomologicalComplex`。
形式化陈述：pOpcycles_extendOpcyclesIso_inv : K.pOpcycles j ≫ (K.extendOpcyclesIso e h
j').inv = (K.extendXIso e hj').inv ≫ (K.extend e).pOpcycles j'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso
_hom_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv`：p_
comp_opcyclesIso_inv : h.p ≫ h.opcyclesIso.inv = S.pOpcycles
-/
lemma pOpcycles_extendOpcyclesIso_inv :
    K.pOpcycles j ≫ (K.extendOpcyclesIso e hj').inv =
      (K.extendXIso e hj').inv ≫ (K.extend e).pOpcycles j' := by
  rw [← cancel_mono (K.extendOpcyclesIso e hj').hom, assoc, assoc, Iso.inv_hom_id, comp_id]
  dsimp [extendOpcyclesIso, pOpcycles]
  rw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id_assoc, ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv]
  rfl

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcycles_extendOpcyclesIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `
HomologicalComplex`。
形式化陈述：pOpcycles_extendOpcyclesIso_hom : (K.extend e).pOpcycles j' ≫ (K.extendOpc
yclesIso e hj').hom = (K.extendXIso e hj').hom ≫ K.pOpcycles j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.pOpcycles_extendOpcyclesIso_inv`：pOpcycles_extendOpcy
clesIso_inv : K.pOpcycles j ≫ (K.extendOpcyclesIso e hj').inv = (K.extendXIso e 
hj').inv ≫ (K.extend e).pOpcycles j'
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pOpcycles_extendOpcyclesIso_hom :
    (K.extend e).pOpcycles j' ≫ (K.extendOpcyclesIso e hj').hom =
      (K.extendXIso e hj').hom ≫ K.pOpcycles j := by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.extendHomologyIso_hom_homology** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendHomologyIso_hom_homologyι :
    (K.extendHomologyIso e hj').hom ≫ K.homologyι j =
      (K.extend e).homologyι j' ≫ (K.extendOpcyclesIso e hj').hom := by
  simp only [← cancel_epi ((K.extend e).homologyπ j'),
    homologyπ_extendHomologyIso_hom_assoc, homology_π_ι, extendCyclesIso_hom_iCycles_assoc,
    homology_π_ι_assoc, pOpcycles_extendOpcyclesIso_hom]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.extendHomologyIso_inv_homology** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendHomologyIso_inv_homologyι :
    (K.extendHomologyIso e hj').inv ≫ (K.extend e).homologyι j' =
      K.homologyι j ≫ (K.extendOpcyclesIso e hj').inv := by
  simp only [← cancel_epi (K.extendHomologyIso e hj').hom,
    Iso.hom_inv_id_assoc, extendHomologyIso_hom_homologyι_assoc, Iso.hom_inv_id, comp_id]

variable {K L}

@[reassoc (attr := simp)]
/-
**HomologicalComplex.extendCyclesIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：extendCyclesIso_hom_naturality : cyclesMap (extendMap φ e) j' ≫ (L.extendC
yclesIso e hj').hom = (K.extendCyclesIso e hj').hom ≫ cyclesMap φ j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.instMonoICycles`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.extendCyclesIso_hom_iCycles`：extendCyclesIso_hom_iCyc
les : (K.extendCyclesIso e hj').hom ≫ K.iCycles j = (K.extend e).iCycles j' ≫ (K
.extendXIso e hj').hom
· 使用定理 `HomologicalComplex.cyclesMap_i_assoc`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ i ≫ L.iCycles 
i = K.iCycles i ≫ φ.f i
· 使用定理 `HomologicalComplex.extendCyclesIso_hom_iCycles_assoc`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extendCyclesIso_hom_naturality :
    cyclesMap (extendMap φ e) j' ≫ (L.extendCyclesIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ cyclesMap φ j := by
  simp [← cancel_mono (L.iCycles j), extendMap_f φ e hj']

@[reassoc (attr := simp)]
/-
**HomologicalComplex.extendHomologyIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 
`HomologicalComplex`。
形式化陈述：extendHomologyIso_hom_naturality : homologyMap (extendMap φ e) j' ≫ (L.ext
endHomologyIso e hj').hom = (K.extendHomologyIso e hj').hom ≫ homologyMap φ j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiHomologyπ`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.homologyπ_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.homologyπ_extendHomologyIso_hom`：homologyπ_extendHomo
logyIso_hom : (K.extend e).homologyπ j' ≫ (K.extendHomologyIso e hj').hom = (K.e
xtendCyclesIso e hj').hom ≫ K.homologyπ …
· 使用定理 `HomologicalComplex.extendCyclesIso_hom_naturality_assoc`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc`：∀ {ι : Type u_
1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   
[inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用引理 `HomologicalComplex.homologyπ_naturality`：homologyπ_naturality : K.homolo
gyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extendHomologyIso_hom_naturality :
    homologyMap (extendMap φ e) j' ≫ (L.extendHomologyIso e hj').hom =
      (K.extendHomologyIso e hj').hom ≫ homologyMap φ j := by
  simp [← cancel_epi ((K.extend e).homologyπ _)]

set_option backward.defeqAttrib.useBackward true in
include hj' in
/-
**HomologicalComplex.quasiIsoAt_extendMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：quasiIsoAt_extendMap_iff : QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `HomologicalComplex.extendHomologyIso_hom_naturality`：extendHomologyIso_h
om_naturality : homologyMap (extendMap φ e) j' ≫ (L.extendHomologyIso e hj').hom
 = (K.extendHomologyIso e hj').hom ≫ homo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasiIsoAt_extendMap_iff :
    QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

end

variable {K L} in
/-
**HomologicalComplex.quasiIso_extendMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex`。
形式化陈述：quasiIso_extendMap_iff [forall j, K.HasHomology j] [forall j, L.HasHomolog
y j] : QuasiIso (extendMap φ e) ↔ QuasiIso φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.extend.instHasHomology`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.extend.instHasHomologyF`：∀ {ι : Type u_1} {ι' : Type 
u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Catego
ryTheory.Category.{v_1, u_3} C] …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.quasiIsoAt_extendMap_iff`：quasiIsoAt_extendMap_iff : 
QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j
· 使用引理 `quasiIsoAt_iff_exactAt`：quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.Ha
sHomology i] [L.HasHomology i] (hK : K.ExactAt i) : QuasiIsoAt f i ↔ L.ExactAt i
· 使用引理 `HomologicalComplex.extend_exactAt`：extend_exactAt (j' : ι') (hj' : foral
l j, e.f j != j') : (K.extend e).ExactAt j'
-/
lemma quasiIso_extendMap_iff [∀ j, K.HasHomology j] [∀ j, L.HasHomology j] :
    QuasiIso (extendMap φ e) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, ← fun j ↦ quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact extend_exactAt _ _ _ (by simpa using hj')
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ j, K.HasHomology j] [∀ j, L.HasHomology j] [QuasiIso φ] :
    QuasiIso (extendMap φ e) := by
  rwa [quasiIso_extendMap_iff]

end HomologicalComplex

