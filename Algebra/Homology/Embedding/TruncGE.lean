/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncGE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncGE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

For example, if `e` is the embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ`
in `ComplexShape.up ℤ` which sends `n : ℕ` to `p + n` and `K : CochainComplex C ℤ`,
then `K.truncGE' e : CochainComplex C ℕ` is the following complex:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). Then, the
cochain complex `K.truncGE e` is indexed by `ℤ`, and has the
following shape:

`... ⟶ 0 ⟶ 0 ⟶ 0 ⟶ Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where `Q` is in degree `p`.

We also construct the canonical epimorphism `K.πTruncGE e : K ⟶ K.truncGE e`.

## TODO
* show that `K.πTruncGE e : K ⟶ K.truncGE e` induces an isomorphism
  in homology in degrees in the image of `e.f`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

namespace truncGE'

open scoped Classical in
/-- The `X` field of `truncGE'`. -/
/-
**HomologicalComplex.truncGE.X** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.tru
ncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `X` field of `truncGE'`.
-/
noncomputable def X (i : ι) : C :=
  if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

/-- The isomorphism `truncGE'.X K e i ≅ K.opcycles (e.f i)` when `e.BoundaryGE i` holds. -/
/-
**HomologicalComplex.truncGE.XIsoOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.truncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `truncGE'.X K e i ≅ K.opcycles (e.f i)` when `e.BoundaryGE i` ho
lds.
-/
noncomputable def XIsoOpcycles {i : ι} (hi : e.BoundaryGE i) :
    X K e i ≅ K.opcycles (e.f i) :=
  eqToIso (if_pos hi)

/-- The isomorphism `truncGE'.X K e i ≅ K.X (e.f i)` when `e.BoundaryGE i` does not hold. -/
/-
**HomologicalComplex.truncGE.XIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.
truncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `truncGE'.X K e i ≅ K.X (e.f i)` when `e.BoundaryGE i` does not 
hold.
-/
noncomputable def XIso {i : ι} (hi : ¬ e.BoundaryGE i) :
    X K e i ≅ K.X (e.f i) :=
  eqToIso (if_neg hi)

open scoped Classical in
/-- The `d` field of `truncGE'`. -/
/-
**HomologicalComplex.truncGE.d** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.tru
ncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `d` field of `truncGE'`.
-/
noncomputable def d (i j : ι) : X K e i ⟶ X K e j :=
  if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
  else 0

@[reassoc (attr := simp)]
/-
**HomologicalComplex.truncGE.d_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex.truncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_comp_d (i j k : ι) : d K e i j ≫ d K e j k = 0 := by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

end truncGE'

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`. -/
/-
**HomologicalComplex.truncGE'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncGE' : HomologicalComplex C c where X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`.
-/
noncomputable def truncGE' : HomologicalComplex C c where
  X := truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

/-- The isomorphism `(K.truncGE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold. -/
/-
**HomologicalComplex.truncGE'XIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               (K : HomologicalComplex C c') →                 (e : c.E
mbedding c') →                   [inst_2 : e.IsTruncGE] →                     [i
nst_3 : ∀ (i' : ι'), K.HasHomology i'] →                       {i : ι} → {i' : ι
'} → e.f i = i' → ¬e.BoundaryGE i → ((K.truncGE' e).X i ≅ K.X i')
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；(K.truncGE' e).X i ≅ K
.X i'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.truncGE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold.
-/
noncomputable def truncGE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.X i' :=
  (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)

/-- The isomorphism `(K.truncGE' e).X i ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds. -/
/-
**HomologicalComplex.truncGE'XIsoOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               (K : HomologicalComplex C c') →                 (e : c.E
mbedding c') →                   [inst_2 : e.IsTruncGE] →                     [i
nst_3 : ∀ (i' : ι'), K.HasHomology i'] →                       {i : ι} → {i' : ι
'} → e.f i = i' → e.BoundaryGE i → ((K.truncGE' e).X i ≅ K.opcycles i')
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；(K.truncGE' e).X i ≅ K
.opcycles i'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.truncGE' e).X i ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds.
-/
noncomputable def truncGE'XIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.opcycles i' :=
  (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.truncGE'_d_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncGE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   {i 
j : ι} (hij : c.Rel i j) {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hi 
: ¬e.BoundaryGE i),   (K.truncGE' e).d i j =     CategoryTheory.CategoryStruct.c
omp (K.truncGE'XIso e hi' hi).hom       (CategoryTheory.CategoryStruct.comp (K.d
 i' j') (K.truncGE'XIso e hj' ⋯).inv)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；hij : c.Rel i j；hi' : 
e.f i = i'；hj' : e.f j = j'；hi : ¬e.BoundaryGE i；K.truncGE' e；K.truncGE'XIso e h
i' hi；CategoryTheory.CategoryStruct.comp (K.d i' j') (K.truncGE'XIso e hj' ⋯).in
v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.not_boundaryGE_next`：not_boundaryGE_next [e.IsRel
Iff] {j k : ι} (hk : c.Rel j k) : ¬ e.BoundaryGE k
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncGE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.truncGE'_d_eq_fromOpcycles** 是 Mathlib 中的一个定理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncGE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   {i 
j : ι} (hij : c.Rel i j) {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hi 
: e.BoundaryGE i),   (K.truncGE' e).d i j =     CategoryTheory.CategoryStruct.co
mp (K.truncGE'XIsoOpcycles e hi' hi).hom       (CategoryTheory.CategoryStruct.co
mp (K.fromOpcycles i' j') (K.truncGE'XIso e hj' ⋯).inv)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；hij : c.Rel i j；hi' : 
e.f i = i'；hj' : e.f j = j'；hi : e.BoundaryGE i；K.truncGE' e；K.truncGE'XIsoOpcyc
les e hi' hi；CategoryTheory.CategoryStruct.comp (K.fromOpcycles i' j') (K.truncG
E'XIso e hj' ⋯).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.not_boundaryGE_next`：not_boundaryGE_next [e.IsRel
Iff] {j k : ι} (hk : c.Rel j k) : ¬ e.BoundaryGE k
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncGE'_d_eq_fromOpcycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIsoOpcycles e hi' hi).hom ≫ K.fromOpcycles i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]

section

variable [HasZeroObject C]

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`. -/
/-
**HomologicalComplex.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncGE : HomologicalComplex C c'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`.
-/
noncomputable def truncGE : HomologicalComplex C c' := (K.truncGE' e).extend e

/-- The isomorphism `(K.truncGE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold. -/
/-
**HomologicalComplex.truncGEXIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncGEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
 (K.truncGE e).X i' ≅ K.X i'
参数：hi' : e.f i = i'；hi : ¬ e.BoundaryGE i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.truncGE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold.
-/
noncomputable def truncGEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.X i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIso e hi' hi

/-- The isomorphism `(K.truncGE e).X i' ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds. -/
/-
**HomologicalComplex.truncGEXIsoOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex`。
形式化陈述：truncGEXIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryG
E i) : (K.truncGE e).X i' ≅ K.opcycles i'
参数：hi' : e.f i = i'；hi : e.BoundaryGE i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.truncGE e).X i' ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds.
-/
noncomputable def truncGEXIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.opcycles i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIsoOpcycles e hi' hi

end

section

variable {K L M}

open scoped Classical in
/-- The morphism `K.truncGE' e ⟶ L.truncGE' e` induced by a morphism `K ⟶ L`. -/
/-
**HomologicalComplex.truncGE'Map** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] →               {K L : HomologicalComplex C c'} →                 (K ⟶ L
) →                   (e : c.Embedding c') →                     [inst_2 : e.IsT
runcGE] →                       [inst_3 : ∀ (i' : ι'), K.HasHomology i'] →      
                   [inst_4 : ∀ (i' : ι'), L.HasHomology i'] → K.truncGE' e ⟶ L.t
runcGE' e
参数：K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `K.truncGE' e ⟶ L.truncGE' e` induced by a morphism `K ⟶ L`.
-/
noncomputable def truncGE'Map : K.truncGE' e ⟶ L.truncGE' e where
  f i :=
    if hi : e.BoundaryGE i
    then
      (K.truncGE'XIsoOpcycles e rfl hi).hom ≫ opcyclesMap φ (e.f i) ≫
        (L.truncGE'XIsoOpcycles e rfl hi).inv
    else
      (K.truncGE'XIso e rfl hi).hom ≫ φ.f (e.f i) ≫ (L.truncGE'XIso e rfl hi).inv
  comm' i j hij := by
    rw [dif_neg (e.not_boundaryGE_next hij)]
    by_cases hi : e.BoundaryGE i
    · rw [dif_pos hi]
      simp [truncGE'_d_eq_fromOpcycles _ e hij rfl rfl hi,
        ← cancel_epi (K.pOpcycles (e.f i))]
    · rw [dif_neg hi]
      simp [truncGE'_d_eq _ e hij rfl rfl hi]
/-
**HomologicalComplex.truncGE'Map_f_eq_opcyclesMap** 是 Mathlib 中的一个定理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L : HomologicalComplex C c'} (φ : K ⟶
 L) (e : c.Embedding c') [inst_2 : e.IsTruncGE]   [inst_3 : ∀ (i' : ι'), K.HasHo
mology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i'] {i : ι} (hi : e.BoundaryGE i
)   {i' : ι'} (h : e.f i = i'),   (HomologicalComplex.truncGE'Map φ e).f i =    
 CategoryTheory.CategoryStruct.comp (K.truncGE'XIsoOpcycles e h hi).hom       (C
ategoryTheory.CategoryStruct.comp (HomologicalComplex.opcyclesMap φ i') (L.trunc
GE'XIsoOpcycles e h hi).inv)
参数：φ : K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'；hi : e.BoundaryGE i；h : e.f i = 
i'；HomologicalComplex.truncGE'Map φ e；K.truncGE'XIsoOpcycles e h hi；CategoryTheo
ry.CategoryStruct.comp (HomologicalComplex.opcyclesMap φ i') (L.truncGE'XIsoOpcy
cles e h hi).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma truncGE'Map_f_eq_opcyclesMap {i : ι} (hi : e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (truncGE'Map φ e).f i =
      (K.truncGE'XIsoOpcycles e h hi).hom ≫ opcyclesMap φ i' ≫
        (L.truncGE'XIsoOpcycles e h hi).inv := by
  subst h
  exact dif_pos hi
/-
**HomologicalComplex.truncGE'Map_f_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L : HomologicalComplex C c'} (φ : K ⟶
 L) (e : c.Embedding c') [inst_2 : e.IsTruncGE]   [inst_3 : ∀ (i' : ι'), K.HasHo
mology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i'] {i : ι} (hi : ¬e.BoundaryGE 
i)   {i' : ι'} (h : e.f i = i'),   (HomologicalComplex.truncGE'Map φ e).f i =   
  CategoryTheory.CategoryStruct.comp (K.truncGE'XIso e h hi).hom       (Category
Theory.CategoryStruct.comp (φ.f i') (L.truncGE'XIso e h hi).inv)
参数：φ : K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'；hi : ¬e.BoundaryGE i；h : e.f i =
 i'；HomologicalComplex.truncGE'Map φ e；K.truncGE'XIso e h hi；CategoryTheory.Cate
goryStruct.comp (φ.f i') (L.truncGE'XIso e h hi).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma truncGE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (truncGE'Map φ e).f i =
      (K.truncGE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncGE'XIso e h hi).inv := by
  subst h
  exact dif_neg hi

variable (K) in
@[simp]
/-
**HomologicalComplex.truncGE'Map_id** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncGE] [inst_3 : ∀ (i' : ι'), K.HasHomology i'],   Ho
mologicalComplex.truncGE'Map (CategoryTheory.CategoryStruct.id K) e =     Catego
ryTheory.CategoryStruct.id (K.truncGE' e)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；CategoryTheory.Categor
yStruct.id K；K.truncGE' e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq_opcyclesMap`：∀ {ι : Type u_1} {ι' : 
Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : C
ategoryTheory.Category.{v_1, u_3} C] …
· 使用引理 `HomologicalComplex.opcyclesMap_id`：opcyclesMap_id : opcyclesMap (𝟙 K) i 
= 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
-/
lemma truncGE'Map_id : truncGE'Map (𝟙 K) e = 𝟙 _ := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

@[reassoc, simp]
/-
**HomologicalComplex.truncGE'Map_comp** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L M : HomologicalComplex C c'} (φ : K
 ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c') [inst_2 : e.IsTruncGE]   [inst_3 : ∀ (i'
 : ι'), K.HasHomology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i']   [inst_5 : ∀
 (i' : ι'), M.HasHomology i'],   HomologicalComplex.truncGE'Map (CategoryTheory.
CategoryStruct.comp φ φ') e =     CategoryTheory.CategoryStruct.comp (Homologica
lComplex.truncGE'Map φ e) (HomologicalComplex.truncGE'Map φ' e)
参数：φ : K ⟶ L；φ' : L ⟶ M；e : c.Embedding c'；i' : ι'；i' : ι'；i' : ι'；CategoryTheor
y.CategoryStruct.comp φ φ'；HomologicalComplex.truncGE'Map φ e；HomologicalComplex
.truncGE'Map φ' e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq_opcyclesMap`：∀ {ι : Type u_1} {ι' : 
Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : C
ategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.opcyclesMap_comp`：opcyclesMap_comp : opcyclesMap (φ ≫
 ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
-/
lemma truncGE'Map_comp : truncGE'Map (φ ≫ φ') e = truncGE'Map φ e ≫ truncGE'Map φ' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl, opcyclesMap_comp]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

variable [HasZeroObject C]

/-- The morphism `K.truncGE e ⟶ L.truncGE e` induced by a morphism `K ⟶ L`. -/
/-
**HomologicalComplex.truncGEMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：truncGEMap : K.truncGE e ⟶ L.truncGE e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `K.truncGE e ⟶ L.truncGE e` induced by a morphism `K ⟶ L`.
-/
noncomputable def truncGEMap : K.truncGE e ⟶ L.truncGE e :=
  (e.extendFunctor C).map (truncGE'Map φ e)

variable (K) in
@[simp]
/-
**HomologicalComplex.truncGEMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
形式化陈述：truncGEMap_id : truncGEMap (𝟙 K) e = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.truncGE'Map_id`：∀ {ι : Type u_1} {ι' : Type u_2} {c :
 ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheory.
Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.Embedding.extendFunctor_map`：∀ {ι : Type u_1} {ι' : Type u_
2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') (C : Type u_
3)   [inst : CategoryTheory.Ca…
· 使用引理 `HomologicalComplex.extendMap_id`：extendMap_id : extendMap (𝟙 K) e = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncGEMap_id : truncGEMap (𝟙 K) e = 𝟙 _ := by
  simp [truncGEMap, truncGE]

@[reassoc, simp]
/-
**HomologicalComplex.truncGEMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：truncGEMap_comp : truncGEMap (φ ≫ φ') e = truncGEMap φ e ≫ truncGEMap φ' e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.truncGE'Map_comp`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.Embedding.extendFunctor_map`：∀ {ι : Type u_1} {ι' : Type u_
2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') (C : Type u_
3)   [inst : CategoryTheory.Ca…
· 使用引理 `HomologicalComplex.extendMap_comp`：extendMap_comp : extendMap (φ ≫ φ') e
 = extendMap φ e ≫ extendMap φ' e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncGEMap_comp : truncGEMap (φ ≫ φ') e = truncGEMap φ e ≫ truncGEMap φ' e := by
  simp [truncGEMap, truncGE]

end

namespace restrictionToTruncGE'

open scoped Classical in
/-- Auxiliary definition for `HomologicalComplex.restrictionToTruncGE'`. -/
/-
**HomologicalComplex.restrictionToTruncGE.f** 是 Mathlib 中的一个定义，位于命名空间 `Homologic
alComplex.restrictionToTruncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `HomologicalComplex.restrictionToTruncGE'`.
-/
noncomputable def f (i : ι) : (K.restriction e).X i ⟶ (K.truncGE' e).X i :=
  if hi : e.BoundaryGE i then
    K.pOpcycles _ ≫ (K.truncGE'XIsoOpcycles e rfl hi).inv
  else
    (K.truncGE'XIso e rfl hi).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.restrictionToTruncGE.f_eq_iso_hom_pOpcycles_iso_inv** 是 Mat
hlib 中的一个引理，位于命名空间 `HomologicalComplex.restrictionToTruncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma f_eq_iso_hom_pOpcycles_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    f K e i = (K.restrictionXIso e hi').hom ≫ K.pOpcycles i' ≫
      (K.truncGE'XIsoOpcycles e hi' hi).inv := by
  dsimp [f]
  rw [dif_pos hi]
  subst hi'
  simp [restrictionXIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.restrictionToTruncGE.f_eq_iso_hom_iso_inv** 是 Mathlib 中的一个引
理，位于命名空间 `HomologicalComplex.restrictionToTruncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma f_eq_iso_hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    f K e i = (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  dsimp [f]
  rw [dif_neg hi]
  subst hi'
  simp [restrictionXIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.restrictionToTruncGE.comm** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.restrictionToTruncGE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm (i j : ι) :
    f K e i ≫ (K.truncGE' e).d i j = (K.restriction e).d i j ≫ f K e j := by
  by_cases hij : c.Rel i j
  · by_cases hi : e.BoundaryGE i
    · rw [f_eq_iso_hom_pOpcycles_iso_inv K e rfl hi,
        f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq_fromOpcycles e hij rfl rfl hi]
      simp [restrictionXIso]
    · rw [f_eq_iso_hom_iso_inv K e rfl hi,
        f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq e hij rfl rfl hi]
      simp [restrictionXIso]
  · simp [HomologicalComplex.shape _ _ _ hij]

end restrictionToTruncGE'

/-- The canonical morphism `K.restriction e ⟶ K.truncGE' e`. -/
/-
**HomologicalComplex.restrictionToTruncGE'** 是 Mathlib 中的一个定义，位于命名空间 `Homologica
lComplex`。
形式化陈述：restrictionToTruncGE' : K.restriction e ⟶ K.truncGE' e where f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff

--- 原说明 ---
The canonical morphism `K.restriction e ⟶ K.truncGE' e`.
-/
noncomputable def restrictionToTruncGE' : K.restriction e ⟶ K.truncGE' e where
  f := restrictionToTruncGE'.f K e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.restrictionToTruncGE'_hasLift** 是 Mathlib 中的一个定理，位于命名空间 `Ho
mologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncGE] [inst_3 : ∀ (i' : ι'), K.HasHomology i'],   e.
HasLift (K.restrictionToTruncGE' e)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；K.restrictionToTruncGE
' e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv`
：f_eq_iso_hom_pOpcycles_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.Bou
ndaryGE i) : f K e i = (K.restrictionXIso e hi').hom ≫ K.pOpc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `HomologicalComplex.d_pOpcycles_assoc`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictionToTruncGE'_hasLift : e.HasLift (K.restrictionToTruncGE' e) := by
  intro j hj i' _
  dsimp [restrictionToTruncGE']
  rw [restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv K e rfl hj]
  simp [restrictionXIso]
/-
**HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv** 是 Ma
thlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncGE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   {i 
: ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i),   (K.restrictionToTrunc
GE' e).f i =     CategoryTheory.CategoryStruct.comp (K.restrictionXIso e hi').ho
m       (CategoryTheory.CategoryStruct.comp (K.pOpcycles i') (K.truncGE'XIsoOpcy
cles e hi' hi).inv)
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；hi' : e.f i = i'；hi : 
e.BoundaryGE i；K.restrictionToTruncGE' e；K.restrictionXIso e hi'；CategoryTheory.
CategoryStruct.comp (K.pOpcycles i') (K.truncGE'XIsoOpcycles e hi' hi).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv`
：f_eq_iso_hom_pOpcycles_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.Bou
ndaryGE i) : f K e i = (K.restrictionXIso e hi').hom ≫ K.pOpc…
-/
lemma restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.restrictionToTruncGE' e).f i = (K.restrictionXIso e hi').hom ≫ K.pOpcycles i' ≫
      (K.truncGE'XIsoOpcycles e hi' hi).inv := by
  apply restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv
/-
**HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv** 是 Mathlib 中的一个
定理，位于命名空间 `HomologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   (K : HomologicalComplex C c') (e : c.Emb
edding c') [inst_2 : e.IsTruncGE] [inst_3 : ∀ (i' : ι'), K.HasHomology i']   {i 
: ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬e.BoundaryGE i),   (K.restrictionToTrun
cGE' e).f i =     CategoryTheory.CategoryStruct.comp (K.restrictionXIso e hi').h
om (K.truncGE'XIso e hi' hi).inv
参数：K : HomologicalComplex C c'；e : c.Embedding c'；i' : ι'；hi' : e.f i = i'；hi : 
¬e.BoundaryGE i；K.restrictionToTruncGE' e；K.restrictionXIso e hi'；K.truncGE'XIso
 e hi' hi。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.restrictionToTruncGE'.f_eq_iso_hom_iso_inv`：f_eq_iso_
hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) : f K e
 i = (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIs…
-/
lemma restrictionToTruncGE'_f_eq_iso_hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i')
    (hi : ¬ e.BoundaryGE i) :
    (K.restrictionToTruncGE' e).f i =
      (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  apply restrictionToTruncGE'.f_eq_iso_hom_iso_inv

/-- `K.restrictionToTruncGE' e).f i` is an isomorphism when `¬ e.BoundaryGE i`. -/
/-
**HomologicalComplex.isIso_restrictionToTruncGE'** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：isIso_restrictionToTruncGE' (i : ι) (hi : ¬ e.BoundaryGE i) : IsIso ((K.re
strictionToTruncGE' e).f i)
参数：i : ι；hi : ¬ e.BoundaryGE i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv`：∀ {ι : Ty
pe u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_
3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv

--- 原说明 ---
`K.restrictionToTruncGE' e).f i` is an isomorphism when `¬ e.BoundaryGE i`.
-/
lemma isIso_restrictionToTruncGE' (i : ι) (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.restrictionToTruncGE' e).f i) := by
  rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {K L} in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.restrictionToTruncGE'_naturality** 是 Mathlib 中的一个定理，位于命名空间 
`HomologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K L : HomologicalComplex C c'} (φ : K ⟶
 L) (e : c.Embedding c') [inst_2 : e.IsTruncGE]   [inst_3 : ∀ (i' : ι'), K.HasHo
mology i'] [inst_4 : ∀ (i' : ι'), L.HasHomology i'],   CategoryTheory.CategorySt
ruct.comp (K.restrictionToTruncGE' e) (HomologicalComplex.truncGE'Map φ e) =    
 CategoryTheory.CategoryStruct.comp (HomologicalComplex.restrictionMap φ e) (L.r
estrictionToTruncGE' e)
参数：φ : K ⟶ L；e : c.Embedding c'；i' : ι'；i' : ι'；K.restrictionToTruncGE' e；Homolo
gicalComplex.truncGE'Map φ e；HomologicalComplex.restrictionMap φ e；L.restriction
ToTruncGE' e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv`
：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C
 : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq_opcyclesMap`：∀ {ι : Type u_1} {ι' : 
Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : C
ategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv`：∀ {ι : Ty
pe u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_
3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.truncGE'Map_f_eq`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
-/
lemma restrictionToTruncGE'_naturality :
    K.restrictionToTruncGE' e ≫ truncGE'Map φ e =
      restrictionMap φ e ≫ L.restrictionToTruncGE' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ e rfl hi,
      truncGE'Map_f_eq_opcyclesMap φ e hi rfl, restrictionXIso]
  · simp [restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ e rfl hi,
      truncGE'Map_f_eq φ e hi rfl, restrictionXIso]

attribute [local instance] epi_comp in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : Epi ((K.restrictionToTruncGE' e).f i) := by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e rfl hi]
    infer_instance
  · have := K.isIso_restrictionToTruncGE' e i hi
    infer_instance
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlySupported e] (i : ι) :
    IsIso ((K.restrictionToTruncGE' e).f i) := by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e rfl hi]
    have : IsIso (K.pOpcycles (e.f i)) := K.isIso_pOpcycles _ _ rfl (by
      obtain ⟨hi₁, hi₂⟩ := hi
      apply IsZero.eq_of_src (K.isZero_X_of_isStrictlySupported e _
        (fun j hj ↦ hi₂ j (by simpa only [hj] using hi₁))))
    infer_instance
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
    infer_instance

section

variable [HasZeroObject C]

/-- The canonical morphism `K ⟶ K.truncGE e` when `e` is an embedding of complex
shapes which satisfy `e.IsTruncGE`. -/
/-
**HomologicalComplex.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `K ⟶ K.truncGE e` when `e` is an embedding of complex
shapes which satisfy `e.IsTruncGE`.
-/
noncomputable def πTruncGE : K ⟶ K.truncGE e :=
  e.liftExtend (K.restrictionToTruncGE' e) (K.restrictionToTruncGE'_hasLift e)

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i' : ι') : Epi ((K.πTruncGE e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    dsimp [πTruncGE]
    rw [e.epi_liftExtend_f_iff _ _ hi]
    infer_instance
  · apply (isZero_extend_X _ _ _ (by simpa using hi')).epi
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (K.πTruncGE e) := epi_of_epi_f _ (fun _ => inferInstance)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (K.truncGE e).IsStrictlySupported e := by
  dsimp [truncGE]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {K L} in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πTruncGE_naturality :
    K.πTruncGE e ≫ truncGEMap φ e = φ ≫ L.πTruncGE e := by
  apply (e.homEquiv _ _).injective
  ext1
  dsimp [truncGEMap, πTruncGE]
  rw [e.homRestrict_comp_extendMap, e.homRestrict_liftExtend, e.homRestrict_precomp,
    e.homRestrict_liftExtend, restrictionToTruncGE'_naturality]

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] : (K.truncGE e).IsStrictlySupported e' where
  isZero := by
    intro i' hi'
    by_cases hi'' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi''
      by_cases hi''' : e.BoundaryGE i
      · rw [IsZero.iff_id_eq_zero, ← cancel_epi
          ((K.truncGE' e).extendXIso e hi ≪≫ K.truncGE'XIsoOpcycles e hi hi''').inv,
          ← cancel_epi (HomologicalComplex.pOpcycles _ _)]
        apply (K.isZero_X_of_isStrictlySupported e' i' hi').eq_of_src
      · exact (K.isZero_X_of_isStrictlySupported e' i' hi').of_iso
          ((K.truncGE' e).extendXIso e hi ≪≫ K.truncGE'XIso e hi hi''')
    · exact (K.truncGE e).isZero_X_of_isStrictlySupported e _ (by simpa using hi'')

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlySupported e] : IsIso (K.πTruncGE e) := by
  suffices ∀ (i' : ι'), IsIso ((K.πTruncGE e).f i') by
    apply Hom.isIso_of_components
  intro i'
  by_cases! hn : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hn
    dsimp [πTruncGE]
    rw [e.isIso_liftExtend_f_iff _ _ hi]
    infer_instance
  · refine ⟨0, ?_, ?_⟩
    all_goals
      apply (isZero_X_of_isStrictlySupported _ e i' hn).eq_of_src
/-
**HomologicalComplex.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_πTruncGE_iff : IsIso (K.πTruncGE e) ↔ K.IsStrictlySupported e :=
  ⟨fun _ ↦ isStrictlySupported_of_iso (asIso (K.πTruncGE e)).symm e,
    fun _ ↦ inferInstance⟩

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncGE]
    (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncGE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
/-
**ComplexShape.Embedding.truncGE'Functor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape
.Embedding`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         (e : c.Embedding c') →           [e.IsTruncGE] →   
          (C : Type u_4) →               [inst : CategoryTheory.Category.{v_2, u
_4} C] →                 [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →  
                 [CategoryTheory.CategoryWithHomology C] →                     C
ategoryTheory.Functor (HomologicalComplex C c') (HomologicalComplex C c)
参数：e : c.Embedding c'；C : Type u_4；HomologicalComplex C c'；HomologicalComplex C 
c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTru
ncGE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`.
-/
noncomputable def truncGE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncGE' e
  map φ := HomologicalComplex.truncGE'Map φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.restriction e ⟶ K.truncGE' e` for all `K`. -/
@[simps]
/-
**ComplexShape.Embedding.restrictionToTruncGE'NatTrans** 是 Mathlib 中的一个定义，位于命名空间
 `ComplexShape.Embedding`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         (e : c.Embedding c') →           [inst : e.IsTruncG
E] →             (C : Type u_4) →               [inst_1 : CategoryTheory.Categor
y.{v_2, u_4} C] →                 [inst_2 : CategoryTheory.Limits.HasZeroMorphis
ms C] →                   [inst_3 : CategoryTheory.CategoryWithHomology C] → e.r
estrictionFunctor C ⟶ e.truncGE'Functor C
参数：e : c.Embedding c'；C : Type u_4。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff

--- 原说明 ---
The natural transformation `K.restriction e ⟶ K.truncGE' e` for all `K`.
-/
noncomputable def restrictionToTruncGE'NatTrans :
    e.restrictionFunctor C ⟶ e.truncGE'Functor C where
  app K := K.restrictionToTruncGE' e

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncGE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`. -/
@[simps]
/-
**ComplexShape.Embedding.truncGEFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.
Embedding`。
形式化陈述：truncGEFunctor : HomologicalComplex C c' ⥤ HomologicalComplex C c' where o
bj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTru
ncGE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`.
-/
noncomputable def truncGEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncGE e
  map φ := HomologicalComplex.truncGEMap φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.πTruncGE e : K ⟶ K.truncGE e` for all `K`. -/
@[simps]
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `K.πTruncGE e : K ⟶ K.truncGE e` for all `K`.
-/
noncomputable def πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C where
  app K := K.πTruncGE e

end ComplexShape.Embedding

