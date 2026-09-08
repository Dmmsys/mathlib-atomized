/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncLE e : HomologicalComplex C c'`.

The main result is that `K.ιTruncLE e : K.truncLE e ⟶ K` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncLE e` is exact in degrees that are not in the image of `e.f`.)

All the results are obtained by dualising the results in the file `Embedding.TruncGEHomology`.

Moreover, if `C` is an abelian category, we introduce the cokernel
sequence `K.shortComplexTruncLE e` of the monomorphism `K.ιTruncLE e`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

section

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncLE'

set_option backward.isDefEq.respectTransparency false in
/-- `K.truncLE'ToRestriction e` is a quasi-isomorphism in degrees that are not at the boundary. -/
/-
**HomologicalComplex.truncLE.quasiIsoAt_truncLE'ToRestriction** 是 Mathlib 中的一个引理
，位于命名空间 `HomologicalComplex.truncLE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K.truncLE'ToRestriction e` is a quasi-isomorphism in degrees that are not at th
e boundary.
-/
lemma quasiIsoAt_truncLE'ToRestriction (j : ι) (hj : ¬ e.BoundaryLE j)
    [(K.restriction e).HasHomology j] [(K.truncLE' e).HasHomology j] :
    QuasiIsoAt (K.truncLE'ToRestriction e) j := by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)
/-
**HomologicalComplex.truncLE.truncLE'_hasHomology** 是 Mathlib 中的一个实例，位于命名空间 `Hom
ologicalComplex.truncLE`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance truncLE'_hasHomology (i : ι) : (K.truncLE' e).HasHomology i :=
  inferInstanceAs ((K.op.truncGE' e.op).unop.HasHomology i)

end truncLE'

variable [HasZeroObject C]

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i' : ι') : (K.truncLE e).HasHomology i' :=
  inferInstanceAs ((K.op.truncGE e.op).unop.HasHomology i')
/-
**HomologicalComplex.quasiIsoAt_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _).map (K.op.πTruncGE e.op).op) j')
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : QuasiIsoAt (K.ιTruncLE e) (e.f i) := K.quasiIsoAt_ιTruncLE e rfl
/-
**HomologicalComplex.quasiIso_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  rw [← quasiIso_opFunctor_map_iff, ← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op
/-
**HomologicalComplex.acyclic_truncLE_iff_isSupportedOutside** 是 Mathlib 中的一个引理，位
于命名空间 `HomologicalComplex`。
形式化陈述：acyclic_truncLE_iff_isSupportedOutside : (K.truncLE e).Acyclic ↔ K.IsSuppo
rtedOutside e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.acyclic_op_iff`：acyclic_op_iff (K : HomologicalComple
x V c) : K.op.Acyclic ↔ K.Acyclic
· 使用引理 `HomologicalComplex.isSupportedOutside_op_iff`：isSupportedOutside_op_iff 
: K.op.IsSupportedOutside e.op ↔ K.IsSupportedOutside e
· 使用引理 `HomologicalComplex.acyclic_truncGE_iff_isSupportedOutside`：acyclic_trunc
GE_iff_isSupportedOutside : (K.truncGE e).Acyclic ↔ K.IsSupportedOutside e
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
-/
lemma acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  rw [← acyclic_op_iff, ← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

variable {K L}
/-
**HomologicalComplex.Acyclic.truncLE** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCompl
ex.Acyclic`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K : HomologicalComplex C c'} [inst_2 : 
∀ (i' : ι'), K.HasHomology i']   [inst_3 : CategoryTheory.Limits.HasZeroObject C
],   K.Acyclic → ∀ (e : c.Embedding c') [inst_4 : e.IsTruncLE], (K.truncLE e).Ac
yclic
参数：i' : ι'；e : c.Embedding c'；K.truncLE e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.acyclic_truncLE_iff_isSupportedOutside`：acyclic_trunc
LE_iff_isSupportedOutside : (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e
-/
lemma Acyclic.truncLE (hK : K.Acyclic) (e : c.Embedding c') [e.IsTruncLE] :
    (K.truncLE e).Acyclic := by
  rw [acyclic_truncLE_iff_isSupportedOutside]
  exact ⟨fun _ ↦ hK _⟩
/-
**HomologicalComplex.quasiIso_truncLEMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：quasiIso_truncLEMap_iff : QuasiIso (truncLEMap φ e) ↔ forall (i : ι) (i' :
 ι') (_ : e.f i = i'), QuasiIsoAt φ i'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyTruncLE`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.quasiIso_opFunctor_map_iff`：quasiIso_opFunctor_map_if
f {K L : HomologicalComplex V c} (φ : K ⟶ L) [forall i, K.HasHomology i] [forall
 i, L.HasHomology i] : QuasiIso ((o…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `HomologicalComplex.quasiIsoAt_opFunctor_map_iff`：quasiIsoAt_opFunctor_ma
p_iff {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L.Ha
sHomology i] : QuasiIsoAt ((opFunctor…
· 使用引理 `HomologicalComplex.quasiIso_truncGEMap_iff`：quasiIso_truncGEMap_iff : Qu
asiIso (truncGEMap φ e) ↔ forall (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt 
φ i'
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
-/
lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

end

section

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

/-- The cokernel sequence of the monomorphism `K.ιTruncLE e`. -/
@[simps X₁ X₂ f]
/-
**HomologicalComplex.shortComplexTruncLE** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex`。
形式化陈述：shortComplexTruncLE : ShortComplex (HomologicalComplex C c')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The cokernel sequence of the monomorphism `K.ιTruncLE e`.
-/
noncomputable def shortComplexTruncLE : ShortComplex (HomologicalComplex C c') :=
  ShortComplex.mk (K.ιTruncLE e) _ (cokernel.condition _)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (K.shortComplexTruncLE e).f := by
  dsimp [shortComplexTruncLE]
  infer_instance
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (K.shortComplexTruncLE e).g := by
  dsimp [shortComplexTruncLE]
  infer_instance
/-
**HomologicalComplex.shortComplexTruncLE_shortExact** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：shortComplexTruncLE_shortExact : (K.shortComplexTruncLE e).ShortExact wher
e exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `HomologicalComplex.instMonoFShortComplexTruncLE`：∀ {ι : Type u_1} {ι' : 
Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : C
ategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instEpiGShortComplexTruncLE`：∀ {ι : Type u_1} {ι' : T
ype u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Ca
tegoryTheory.Category.{v_1, u_3} C] …
-/
lemma shortComplexTruncLE_shortExact :
    (K.shortComplexTruncLE e).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
/-
**HomologicalComplex.mono_homologyMap_shortComplexTruncLE_g** 是 Mathlib 中的一个引理，位
于命名空间 `HomologicalComplex`。
形式化陈述：mono_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i !=
 i') : Mono (homologyMap (K.shortComplexTruncLE e).g i')
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.homology_exact₂`：homology_exact₂ 
: (ShortComplex.mk (HomologicalComplex.homologyMap S.f i) (HomologicalComplex.ho
mologyMap S.g i) (by rw [← HomologicalComple…
· 使用引理 `HomologicalComplex.shortComplexTruncLE_shortExact`：shortComplexTruncLE_s
hortExact : (K.shortComplexTruncLE e).ShortExact where exact
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomologicalComplex.instHasHomologyTruncLE`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.ExactAt.isZero_homology`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.exactAt_of_isSupported`：exactAt_of_isSupported [K.IsS
upported e] (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
-/
lemma mono_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    Mono (homologyMap (K.shortComplexTruncLE e).g i') :=
  ((K.shortComplexTruncLE_shortExact e).homology_exact₂ i').mono_g
    (by apply ((K.truncLE e).exactAt_of_isSupported e i' hi').isZero_homology.eq_of_src)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HomologicalComplex.shortComplexTruncLE_shortExact_** 是 Mathlib 中的一个引理，位于命名空间 `
HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shortComplexTruncLE_shortExact_δ_eq_zero (i' j' : ι') (hij' : c'.Rel i' j') :
    (K.shortComplexTruncLE_shortExact e).δ i' j' hij' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j)), zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj)).isZero_homology.eq_of_tgt
/-
**HomologicalComplex.epi_homologyMap_shortComplexTruncLE_g** 是 Mathlib 中的一个实例，位于
命名空间 `HomologicalComplex`。
形式化陈述：epi_homologyMap_shortComplexTruncLE_g (i' : ι') : Epi (homologyMap (K.shor
tComplexTruncLE e).g i')
参数：i' : ι'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : C
ategoryTheory.ShortComplex C}…
· 使用引理 `HomologicalComplex.shortComplexTruncLE_shortExact`：shortComplexTruncLE_s
hortExact : (K.shortComplexTruncLE e).ShortExact where exact
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.comp_δ`：comp_δ : HomologicalCompl
ex.homologyMap S.g i ≫ hS.δ i j hij = 0
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.homology_exact₃`：homology_exact₃ 
: (ShortComplex.mk _ _ (comp_δ hS i j hij)).Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.shortComplexTruncLE_shortExact_δ_eq_zero`：shortComple
xTruncLE_shortExact_δ_eq_zero (i' j' : ι') (hij' : c'.Rel i' j') : (K.shortCompl
exTruncLE_shortExact e).δ i' j' hij' = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.epi_homologyMap_of_epi_of_not_rel`：epi_homologyMap_of
_epi_of_not_rel (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] [Epi (φ.
f i)] (hi : forall j, ¬ c.Rel i j) : Epi (…
· 使用定理 `HomologicalComplex.instEpiFOfHasFiniteColimits`：∀ {C : Type u_1} {ι : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}   [in
st_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `HomologicalComplex.instEpiGShortComplexTruncLE`：∀ {ι : Type u_1} {ι' : T
ype u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Ca
tegoryTheory.Category.{v_1, u_3} C] …
-/
instance epi_homologyMap_shortComplexTruncLE_g (i' : ι') :
    Epi (homologyMap (K.shortComplexTruncLE e).g i') := by
  by_cases hi' : ∃ j', c'.Rel i' j'
  · obtain ⟨j', hj'⟩ := hi'
    exact ((K.shortComplexTruncLE_shortExact e).homology_exact₃ i' j' hj').epi_f (by simp)
  · exact epi_homologyMap_of_epi_of_not_rel _ _ (by simpa using hi')
/-
**HomologicalComplex.isIso_homologyMap_shortComplexTruncLE_g** 是 Mathlib 中的一个引理，
位于命名空间 `HomologicalComplex`。
形式化陈述：isIso_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i !
= i') : IsIso (homologyMap (K.shortComplexTruncLE e).g i')
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `HomologicalComplex.mono_homologyMap_shortComplexTruncLE_g`：mono_homology
Map_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i != i') : Mono (homolo
gyMap (K.shortComplexTruncLE e).g i')
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
-/
lemma isIso_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsIso (homologyMap (K.shortComplexTruncLE e).g i') := by
  have := K.mono_homologyMap_shortComplexTruncLE_g e i' hi'
  apply isIso_of_mono_of_epi
/-
**HomologicalComplex.quasiIsoAt_shortComplexTruncLE_g** 是 Mathlib 中的一个引理，位于命名空间 
`HomologicalComplex`。
形式化陈述：quasiIsoAt_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i != i') :
 QuasiIsoAt (K.shortComplexTruncLE e).g i'
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff_isIso_homologyMap`：quasiIsoAt_iff_isIso_homologyMap (f : 
K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt f i ↔ IsIso (hom
ologyMap f i)
· 使用引理 `HomologicalComplex.isIso_homologyMap_shortComplexTruncLE_g`：isIso_homolo
gyMap_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i != i') : IsIso (hom
ologyMap (K.shortComplexTruncLE e).g i')
-/
lemma quasiIsoAt_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    QuasiIsoAt (K.shortComplexTruncLE e).g i' := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact K.isIso_homologyMap_shortComplexTruncLE_g e i' hi'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.shortComplexTruncLE_X** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shortComplexTruncLE_X₃_isSupportedOutside :
    (K.shortComplexTruncLE e).X₃.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff_isZero_homology]
    by_cases hi : ∃ j', c'.Rel (e.f i) j'
    · obtain ⟨j', hj'⟩ := hi
      apply ((K.shortComplexTruncLE_shortExact e).homology_exact₃ (e.f i) j' hj').isZero_X₂
      · rw [← cancel_epi (homologyMap (K.ιTruncLE e) (e.f i)), comp_zero]
        dsimp [shortComplexTruncLE]
        rw [← homologyMap_comp, cokernel.condition, homologyMap_zero]
      · simp
    · have : IsIso (homologyMap (K.shortComplexTruncLE e).f (e.f i)) := by dsimp; infer_instance
      rw [IsZero.iff_id_eq_zero, ← cancel_epi (homologyMap (K.shortComplexTruncLE e).g (e.f i)),
        comp_id, comp_zero, ← cancel_epi (homologyMap (K.shortComplexTruncLE e).f (e.f i)),
        comp_zero, ← homologyMap_comp, ShortComplex.zero, homologyMap_zero]

end

end HomologicalComplex

