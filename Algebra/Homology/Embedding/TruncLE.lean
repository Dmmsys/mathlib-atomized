/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncGE

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncLE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncLE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

In order to achieve this, we dualize the constructions from the file
`Embedding.TruncGE`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncLE`. -/
/-
**HomologicalComplex.truncLE'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncLE' : HomologicalComplex C c
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncLE`.
-/
noncomputable def truncLE' : HomologicalComplex C c := (K.op.truncGE' e.op).unop

/-- The isomorphism `(K.truncLE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryLE i` does not hold. -/
/-
**HomologicalComplex.truncLE'XIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               (K : HomologicalComplex C c') →                 (e : c.E
mbedding c') →                   [inst_2 : e.IsTruncLE] →                     [i
nst_3 : ∀ (i' : ι'), K.HasHomology i'] →                       {i : ι} → {i' : ι
'} → e.f i = i' → ¬e.BoundaryLE i → ((K.truncLE' e).X i ≅ K.X i')
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；(K.truncLE' e).X i ≅ K
.X i'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The isomorphism `(K.truncLE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryLE i` does not hold.
-/
noncomputable def truncLE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.X i' :=
  (K.op.truncGE'XIso e.op hi' (by simpa)).symm.unop

/-- The isomorphism `(K.truncLE' e).X i ≅ K.cycles i'` when `e.f i = i'`
and `e.BoundaryLE i` holds. -/
/-
**HomologicalComplex.truncLE'XIsoCycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               (K : HomologicalComplex C c') →                 (e : c.E
mbedding c') →                   [inst_2 : e.IsTruncLE] →                     [i
nst_3 : ∀ (i' : ι'), K.HasHomology i'] →                       {i : ι} → {i' : ι
'} → e.f i = i' → e.BoundaryLE i → ((K.truncLE' e).X i ≅ K.cycles i')
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；(K.truncLE' e).X i ≅ K
.cycles i'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The isomorphism `(K.truncLE' e).X i ≅ K.cycles i'` when `e.f i = i'`
and `e.BoundaryLE i` holds.
-/
noncomputable def truncLE'XIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.cycles i' :=
  (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm
/-
**HomologicalComplex.truncLE'_d_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncLE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   {i 
j : ι} (hij : c.Rel i j) {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hj 
: ¬e.BoundaryLE j),   (K.truncLE' e).d i j =     CategoryTheory.CategoryStruct.c
omp (K.truncLE'XIso e hi' ⋯).hom       (CategoryTheory.CategoryStruct.comp (K.d 
i' j') (K.truncLE'XIso e hj' hj).inv)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；hij : c.Rel i j；hi' : 
e.f i = i'；hj' : e.f j = j'；hj : ¬e.BoundaryLE j；K.truncLE' e；K.truncLE'XIso e h
i' ⋯；CategoryTheory.CategoryStruct.comp (K.d i' j') (K.truncLE'XIso e hj' hj).in
v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用引理 `ComplexShape.Embedding.not_boundaryLE_prev`：not_boundaryLE_prev [e.IsRel
Iff] {i j : ι} (hi : c.Rel i j) : ¬ e.BoundaryLE i
· 使用定理 `ComplexShape.Embedding.IsTruncLE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncLE],   e.IsRelIff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用引理 `ComplexShape.Embedding.not_boundaryGE_next`：not_boundaryGE_next [e.IsRel
Iff] {j k : ι} (hk : c.Rel j k) : ¬ e.BoundaryGE k
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.op_d`：∀ {ι : Type u_1} {V : Type u_2} [inst : Categor
yTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.L
imits.HasZero…
· 使用定理 `HomologicalComplex.truncGE'_d_eq`：∀ {ι : Type u_1} {ι' : Type u_2} {c : 
ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheory.C
ategory.{v_1, u_3} C] …
-/
lemma truncLE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : ¬ e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫ K.d i' j' ≫
        (K.truncLE'XIso e hj' hj).inv :=
  Quiver.Hom.op_inj (by simpa using! K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.truncLE'_d_eq_toCycles** 是 Mathlib 中的一个定理，位于命名空间 `Homologic
alComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncLE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   {i 
j : ι} (hij : c.Rel i j) {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hj 
: e.BoundaryLE j),   (K.truncLE' e).d i j =     CategoryTheory.CategoryStruct.co
mp (K.truncLE'XIso e hi' ⋯).hom       (CategoryTheory.CategoryStruct.comp (K.toC
ycles i' j') (K.truncLE'XIsoCycles e hj' hj).inv)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；hij : c.Rel i j；hi' : 
e.f i = i'；hj' : e.f j = j'；hj : e.BoundaryLE j；K.truncLE' e；K.truncLE'XIso e hi
' ⋯；CategoryTheory.CategoryStruct.comp (K.toCycles i' j') (K.truncLE'XIsoCycles 
e hj' hj).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用引理 `ComplexShape.Embedding.not_boundaryLE_prev`：not_boundaryLE_prev [e.IsRel
Iff] {i j : ι} (hi : c.Rel i j) : ¬ e.BoundaryLE i
· 使用定理 `ComplexShape.Embedding.IsTruncLE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncLE],   e.IsRelIff
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.unop_d`：∀ {ι : Type u_1} {V : Type u_2} [inst : Categ
oryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTheory
.Limits.HasZero…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.unop_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : Cᵒᵖ} (f : X ≅ Y), f.unop.inv = f.inv.unop
· 使用定理 `CategoryTheory.Iso.unop_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : Cᵒᵖ} (f : X ≅ Y), f.unop.hom = f.hom.unop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.opcyclesOpIso_hom_toCycles_op`：opcyclesOpIso_hom_toCy
cles_op : (K.opcyclesOpIso i).hom ≫ (K.toCycles j i).op = K.op.fromOpcycles i j
· 使用定理 `HomologicalComplex.truncGE'_d_eq_fromOpcycles`：∀ {ι : Type u_1} {ι' : Ty
pe u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Cat
egoryTheory.Category.{v_1, u_3} C] …
-/
lemma truncLE'_d_eq_toCycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫
      K.toCycles i' j' ≫ (K.truncLE'XIsoCycles e hj' hj).inv :=
  Quiver.Hom.op_inj (by
    simpa [truncLE', truncLE'XIso, truncLE'XIsoCycles]
      using! K.op.truncGE'_d_eq_fromOpcycles e.op hij hj' hi' (by simpa))

section

variable [HasZeroObject C]

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncLE`. -/
/-
**HomologicalComplex.truncLE** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncLE : HomologicalComplex C c'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncLE`.
-/
noncomputable def truncLE : HomologicalComplex C c' := (K.op.truncGE e.op).unop

/-- The canonical isomorphism `K.truncLE e ≅ (K.truncLE' e).extend e`. -/
/-
**HomologicalComplex.truncLEIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncLEIso : K.truncLE e ≅ (K.truncLE' e).extend e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.truncLE e ≅ (K.truncLE' e).extend e`.
-/
noncomputable def truncLEIso : K.truncLE e ≅ (K.truncLE' e).extend e :=
  (unopFunctor C c'.symm).mapIso ((K.truncLE' e).extendOpIso e).symm.op

/-- The isomorphism `(K.truncLE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryLE i` does not hold. -/
/-
**HomologicalComplex.truncLEXIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncLEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
 (K.truncLE e).X i' ≅ K.X i'
参数：hi' : e.f i = i'；hi : ¬ e.BoundaryLE i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The isomorphism `(K.truncLE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryLE i` does not hold.
-/
noncomputable def truncLEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.X i' :=
  (K.op.truncGEXIso e.op hi' (by simpa)).unop.symm

/-- The isomorphism `(K.truncLE e).X i' ≅ K.cycles i'` when `e.f i = i'`
and `e.BoundaryLE i` holds. -/
/-
**HomologicalComplex.truncLEXIsoCycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex`。
形式化陈述：truncLEXIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE 
i) : (K.truncLE e).X i' ≅ K.cycles i'
参数：hi' : e.f i = i'；hi : e.BoundaryLE i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The isomorphism `(K.truncLE e).X i' ≅ K.cycles i'` when `e.f i = i'`
and `e.BoundaryLE i` holds.
-/
noncomputable def truncLEXIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.cycles i' :=
  (K.op.truncGEXIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

end

section

variable {K L M}

/-- The morphism `K.truncLE' e ⟶ L.truncLE' e` induced by a morphism `K ⟶ L`. -/
/-
**HomologicalComplex.truncLE'Map** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               {K L : HomologicalComplex C c'} →                 (K ⟶ L
) →                   (e : c.Embedding c') →                     [inst_2 : e.IsT
runcLE] →                       [inst_3 : ∀ (i' : ι'), K.HasHomology i'] →      
                   [inst_4 : ∀ (i' : ι'), L.HasHomology i'] → K.truncLE' e ⟶ L.t
runcLE' e
参数：K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The morphism `K.truncLE' e ⟶ L.truncLE' e` induced by a morphism `K ⟶ L`.
-/
noncomputable def truncLE'Map : K.truncLE' e ⟶ L.truncLE' e :=
  (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.truncLE'Map_f_eq_cyclesMap** 是 Mathlib 中的一个定理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L : HomologicalComplex C c'} (φ : K ⟶
 L) (e : c.Embedding c') [inst_2 : e.IsTruncLE]   [inst_3 : ∀ (i' : ι'), K.HasHo
mology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i'] {i : ι} (hi : e.BoundaryLE i
)   {i' : ι'} (h : e.f i = i'),   (HomologicalComplex.truncLE'Map φ e).f i =    
 CategoryTheory.CategoryStruct.comp (K.truncLE'XIsoCycles e h hi).hom       (Cat
egoryTheory.CategoryStruct.comp (HomologicalComplex.cyclesMap φ i') (L.truncLE'X
IsoCycles e h hi).inv)
参数：φ : K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'；hi : e.BoundaryLE i；h : e.f i = 
i'；HomologicalComplex.truncLE'Map φ e；K.truncLE'XIsoCycles e h hi；CategoryTheory
.CategoryStruct.comp (HomologicalComplex.cyclesMap φ i') (L.truncLE'XIsoCycles e
 h hi).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq_opcyclesMap`：∀ {ι : Type u_1} {ι' : 
Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : C
ategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `HomologicalComplex.opcyclesOpIso_inv_naturality_assoc`：∀ {ι : Type u_1} 
{V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι
}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma truncLE'Map_f_eq_cyclesMap {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIsoCycles e h hi).hom ≫ cyclesMap φ i' ≫
        (L.truncLE'XIsoCycles e h hi).inv := by
  apply Quiver.Hom.op_inj
  dsimp [truncLE'Map, truncLE'XIsoCycles]
  rw [assoc, assoc, truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h,
    opcyclesOpIso_inv_naturality_assoc, Iso.hom_inv_id_assoc]
/-
**HomologicalComplex.truncLE'Map_f_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L : HomologicalComplex C c'} (φ : K ⟶
 L) (e : c.Embedding c') [inst_2 : e.IsTruncLE]   [inst_3 : ∀ (i' : ι'), K.HasHo
mology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i'] {i : ι} (hi : ¬e.BoundaryLE 
i)   {i' : ι'} (h : e.f i = i'),   (HomologicalComplex.truncLE'Map φ e).f i =   
  CategoryTheory.CategoryStruct.comp (K.truncLE'XIso e h hi).hom       (Category
Theory.CategoryStruct.comp (φ.f i') (L.truncLE'XIso e h hi).inv)
参数：φ : K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'；hi : ¬e.BoundaryLE i；h : e.f i =
 i'；HomologicalComplex.truncLE'Map φ e；K.truncLE'XIso e h hi；CategoryTheory.Cate
goryStruct.comp (φ.f i') (L.truncLE'XIso e h hi).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.opFunctor_map_f`：∀ {ι : Type u_1} (V : Type u_2) [ins
t : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst_1 : Categ
oryTheory.Limits.HasZero…
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
-/
lemma truncLE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncLE'XIso e h hi).inv :=
  Quiver.Hom.op_inj
    (by simpa using! truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)

variable (K) in
@[simp]
/-
**HomologicalComplex.truncLE'Map_id** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncLE] [inst_3 : ∀ (i' : ι'), K.HasHomology i'],   Ho
mologicalComplex.truncLE'Map (CategoryTheory.CategoryStruct.id K) e =     Catego
ryTheory.CategoryStruct.id (K.truncLE' e)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；CategoryTheory.Categor
yStruct.id K；K.truncLE' e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HomologicalComplex.truncGE'Map_id`：∀ {ι : Type u_1} {ι' : Type u_2} {c :
 ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheory.
Category.{v_1, u_3} C] …
-/
lemma truncLE'Map_id : truncLE'Map (𝟙 K) e = 𝟙 _ :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGE'Map_id e.op))

@[reassoc, simp]
/-
**HomologicalComplex.truncLE'Map_comp** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L M : HomologicalComplex C c'} (φ : K
 ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c') [inst_2 : e.IsTruncLE]   [inst_3 : ∀ (i'
 : ι'), K.HasHomology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i']   [inst_5 : ∀
 (i' : ι'), M.HasHomology i'],   HomologicalComplex.truncLE'Map (CategoryTheory.
CategoryStruct.comp φ φ') e =     CategoryTheory.CategoryStruct.comp (Homologica
lComplex.truncLE'Map φ e) (HomologicalComplex.truncLE'Map φ' e)
参数：φ : K ⟶ L；φ' : L ⟶ M；e : c.Embedding c'；i' : ι'；i' : ι'；i' : ι'；CategoryTheor
y.CategoryStruct.comp φ φ'；HomologicalComplex.truncLE'Map φ e；HomologicalComplex
.truncLE'Map φ' e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HomologicalComplex.truncGE'Map_comp`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
-/
lemma truncLE'Map_comp : truncLE'Map (φ ≫ φ') e = truncLE'Map φ e ≫ truncLE'Map φ' e :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGE'Map_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

variable [HasZeroObject C]

/-- The morphism `K.truncLE e ⟶ L.truncLE e` induced by a morphism `K ⟶ L`. -/
/-
**HomologicalComplex.truncLEMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncLEMap : K.truncLE e ⟶ L.truncLE e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The morphism `K.truncLE e ⟶ L.truncLE e` induced by a morphism `K ⟶ L`.
-/
noncomputable def truncLEMap : K.truncLE e ⟶ L.truncLE e :=
  (unopFunctor C c'.symm).map (truncGEMap ((opFunctor C c').map φ.op) e.op).op

variable (K) in
@[simp]
/-
**HomologicalComplex.truncLEMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
形式化陈述：truncLEMap_id : truncLEMap (𝟙 K) e = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `HomologicalComplex.truncGEMap_id`：truncGEMap_id : truncGEMap (𝟙 K) e = 𝟙
 _
-/
lemma truncLEMap_id : truncLEMap (𝟙 K) e = 𝟙 _ :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGEMap_id e.op))

@[reassoc, simp]
/-
**HomologicalComplex.truncLEMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：truncLEMap_comp : truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `HomologicalComplex.truncGEMap_comp`：truncGEMap_comp : truncGEMap (φ ≫ φ'
) e = truncGEMap φ e ≫ truncGEMap φ' e
-/
lemma truncLEMap_comp : truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGEMap_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

end

/-- The canonical morphism `K.truncLE' e ⟶ K.restriction e`. -/
/-
**HomologicalComplex.truncLE'ToRestriction** 是 Mathlib 中的一个定义，位于命名空间 `Homologica
lComplex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               (K : HomologicalComplex C c') →                 (e : c.E
mbedding c') →                   [inst_2 : e.IsTruncLE] → [inst_3 : ∀ (i' : ι'),
 K.HasHomology i'] → K.truncLE' e ⟶ K.restriction e
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE

--- 原说明 ---
The canonical morphism `K.truncLE' e ⟶ K.restriction e`.
-/
noncomputable def truncLE'ToRestriction : K.truncLE' e ⟶ K.restriction e :=
  (unopFunctor C c.symm).map (K.op.restrictionToTruncGE' e.op).op

/-- `(K.truncLE'ToRestriction e).f i` is an isomorphism when `¬ e.BoundaryLE i`. -/
/-
**HomologicalComplex.isIso_truncLE'ToRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncLE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   (i 
: ι), ¬e.BoundaryLE i → CategoryTheory.IsIso ((K.truncLE'ToRestriction e).f i)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；i : ι；(K.truncLE'ToRes
triction e).f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncLE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncLE],   e.IsRelIff
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用引理 `HomologicalComplex.isIso_restrictionToTruncGE'`：isIso_restrictionToTrunc
GE' (i : ι) (hi : ¬ e.BoundaryGE i) : IsIso ((K.restrictionToTruncGE' e).f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
`(K.truncLE'ToRestriction e).f i` is an isomorphism when `¬ e.BoundaryLE i`.
-/
lemma isIso_truncLE'ToRestriction (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.truncLE'ToRestriction e).f i) := by
  change IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop
  have := K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  infer_instance

variable {K L} in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.truncLE'ToRestriction_naturality** 是 Mathlib 中的一个定理，位于命名空间 
`HomologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L : HomologicalComplex C c'} (φ : K ⟶
 L) (e : c.Embedding c') [inst_2 : e.IsTruncLE]   [inst_3 : ∀ (i' : ι'), K.HasHo
mology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i'],   CategoryTheory.CategorySt
ruct.comp (HomologicalComplex.truncLE'Map φ e) (L.truncLE'ToRestriction e) =    
 CategoryTheory.CategoryStruct.comp (K.truncLE'ToRestriction e) (HomologicalComp
lex.restrictionMap φ e)
参数：φ : K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'；HomologicalComplex.truncLE'Map φ
 e；L.truncLE'ToRestriction e；K.truncLE'ToRestriction e；HomologicalComplex.restri
ctionMap φ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HomologicalComplex.restrictionToTruncGE'_naturality`：∀ {ι : Type u_1} {ι
' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst
 : CategoryTheory.Category.{v_1, u_3} C] …
-/
lemma truncLE'ToRestriction_naturality :
    truncLE'Map φ e ≫ L.truncLE'ToRestriction e =
      K.truncLE'ToRestriction e ≫ restrictionMap φ e :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (restrictionToTruncGE'_naturality ((opFunctor C c').map φ.op) e.op))
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : Mono ((K.truncLE'ToRestriction e).f i) :=
  inferInstanceAs (Mono ((K.op.restrictionToTruncGE' e.op).f i).unop)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlySupported e] (i : ι) :
    IsIso ((K.truncLE'ToRestriction e).f i) :=
  inferInstanceAs (IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop)

section

variable [HasZeroObject C]

/-- The canonical morphism `K.truncLE e ⟶ K` when `e` is an embedding of complex
shapes which satisfy `e.IsTruncLE`. -/
/-
**HomologicalComplex.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `K.truncLE e ⟶ K` when `e` is an embedding of complex
shapes which satisfy `e.IsTruncLE`.
-/
noncomputable def ιTruncLE : K.truncLE e ⟶ K :=
  (unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i' : ι') : Mono ((K.ιTruncLE e).f i') :=
  inferInstanceAs (Mono ((K.op.πTruncGE e.op).f i').unop)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (K.ιTruncLE e) := mono_of_mono_f _ (fun _ => inferInstance)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (K.truncLE e).IsStrictlySupported e := by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs ((K.op.truncGE e.op).IsStrictlySupported e.op)

variable {K L} in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTruncLE_naturality :
    truncLEMap φ e ≫ L.ιTruncLE e = K.ιTruncLE e ≫ φ :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (πTruncGE_naturality ((opFunctor C c').map φ.op) e.op))
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] : (K.truncLE e).IsStrictlySupported e' := by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs ((K.op.truncGE e.op).IsStrictlySupported e'.op)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlySupported e] : IsIso (K.ιTruncLE e) :=
  inferInstanceAs (IsIso ((unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op))
/-
**HomologicalComplex.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_ιTruncLE_iff : IsIso (K.ιTruncLE e) ↔ K.IsStrictlySupported e :=
  ⟨fun _ ↦ isStrictlySupported_of_iso (asIso (K.ιTruncLE e)) e,
    fun _ ↦ inferInstance⟩

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncLE]
    (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
/-
**ComplexShape.Embedding.truncLE'Functor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape
.Embedding`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         (e : c.Embedding c') →           [e.IsTruncLE] →   
          (C : Type u_4) →               [inst : CategoryTheory.Category.{v_2, u
_4} C] →                 [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →  
                 [CategoryTheory.CategoryWithHomology C] →                     C
ategoryTheory.Functor (HomologicalComplex C c') (HomologicalComplex C c)
参数：e : c.Embedding c'；C : Type u_4；HomologicalComplex C c'；HomologicalComplex C 
c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTru
ncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`.
-/
noncomputable def truncLE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncLE' e
  map φ := HomologicalComplex.truncLE'Map φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.truncGE' e ⟶ K.restriction e` for all `K`. -/
@[simps]
/-
**ComplexShape.Embedding.truncLE'ToRestrictionNatTrans** 是 Mathlib 中的一个定义，位于命名空间
 `ComplexShape.Embedding`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         (e : c.Embedding c') →           [inst : e.IsTruncL
E] →             (C : Type u_4) →               [inst_1 : CategoryTheory.Categor
y.{v_2, u_4} C] →                 [inst_2 : CategoryTheory.Limits.HasZeroMorphis
ms C] →                   [inst_3 : CategoryTheory.CategoryWithHomology C] → e.t
runcLE'Functor C ⟶ e.restrictionFunctor C
参数：e : c.Embedding c'；C : Type u_4。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncLE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncLE],   e.IsRelIff

--- 原说明 ---
The natural transformation `K.truncGE' e ⟶ K.restriction e` for all `K`.
-/
noncomputable def truncLE'ToRestrictionNatTrans :
    e.truncLE'Functor C ⟶ e.restrictionFunctor C where
  app K := K.truncLE'ToRestriction e

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`. -/
@[simps]
/-
**ComplexShape.Embedding.truncLEFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.
Embedding`。
形式化陈述：truncLEFunctor : HomologicalComplex C c' ⥤ HomologicalComplex C c' where o
bj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTru
ncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`.
-/
noncomputable def truncLEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncLE e
  map φ := HomologicalComplex.truncLEMap φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.ιTruncLE e : K.truncLE e ⟶ K` for all `K`. -/
@[simps]
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `K.ιTruncLE e : K.truncLE e ⟶ K` for all `K`.
-/
noncomputable def ιTruncLENatTrans : e.truncLEFunctor C ⟶ 𝟭 _ where
  app K := K.ιTruncLE e

end ComplexShape.Embedding

