/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# The homology sequence

If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence in a category of complexes
`HomologicalComplex C c` in an abelian category (i.e. `S` is a short complex in
that category and satisfies `hS : S.ShortExact`), then whenever `i` and `j` are degrees
such that `hij : c.Rel i j`, then there is a long exact sequence :
`... ⟶ S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j ⟶ ...`.
The connecting homomorphism `S.X₃.homology i ⟶ S.X₁.homology j` is `hS.δ i j hij`, and
the exactness is asserted as lemmas `hS.homology_exact₁`, `hS.homology_exact₂` and
`hS.homology_exact₃`.

The proof is based on the snake lemma, similarly as it was originally done in
the Liquid Tensor Experiment.

## References

* https://stacks.math.columbia.edu/tag/0111

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

section HasZeroMorphisms

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

/-- The morphism `K.opcycles i ⟶ K.cycles j` that is induced by `K.d i j`. -/
/-
**HomologicalComplex.opcyclesToCycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：opcyclesToCycles : K.opcycles i ⟶ K.cycles j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `K.opcycles i ⟶ K.cycles j` that is induced by `K.d i j`.
-/
noncomputable def opcyclesToCycles : K.opcycles i ⟶ K.cycles j :=
  K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.opcyclesToCycles_iCycles** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOp
cycles i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.liftCycles_i`：liftCycles_i {A : C} (k : A ⟶ K.X i) (j
 : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iC
ycles i = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j := by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc]
/-
**HomologicalComplex.pOpcycles_opcyclesToCycles_iCycles** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex`。
形式化陈述：pOpcycles_opcyclesToCycles_iCycles : K.pOpcycles i ≫ K.opcyclesToCycles i 
j ≫ K.iCycles j = K.d i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.liftCycles_i`：liftCycles_i {A : C} (k : A ⟶ K.X i) (j
 : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iC
ycles i = k
· 使用引理 `HomologicalComplex.p_fromOpcycles`：p_fromOpcycles : K.pOpcycles i ≫ K.fr
omOpcycles i j = K.d i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pOpcycles_opcyclesToCycles_iCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j ≫ K.iCycles j = K.d i j := by
  simp [opcyclesToCycles]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcycles_opcyclesToCycles** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：pOpcycles_opcyclesToCycles : K.pOpcycles i ≫ K.opcyclesToCycles i j = K.to
Cycles i j
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
· 使用引理 `HomologicalComplex.opcyclesToCycles_iCycles`：opcyclesToCycles_iCycles : 
K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j
· 使用引理 `HomologicalComplex.p_fromOpcycles`：p_fromOpcycles : K.pOpcycles i ≫ K.fr
omOpcycles i j = K.d i j
· 使用引理 `HomologicalComplex.toCycles_i`：toCycles_i [K.HasHomology j] : K.toCycles
 i j ≫ K.iCycles j = K.d i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pOpcycles_opcyclesToCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j = K.toCycles i j := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_opcyclesToCycles :
    K.homologyι i ≫ K.opcyclesToCycles i j = 0 := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.opcyclesToCycles_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opcyclesToCycles_homologyπ :
    K.opcyclesToCycles i j ≫ K.homologyπ j = 0 := by
  simp only [← cancel_epi (K.pOpcycles i),
    pOpcycles_opcyclesToCycles_assoc, toCycles_comp_homologyπ, comp_zero]

variable {K L}

@[reassoc (attr := simp)]
/-
**HomologicalComplex.opcyclesToCycles_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：opcyclesToCycles_naturality : opcyclesMap φ i ≫ opcyclesToCycles L i j = o
pcyclesToCycles K i j ≫ cyclesMap φ j
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
· 使用引理 `HomologicalComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ i ≫ L.iCycles 
i = K.iCycles i ≫ φ.f i
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.pOpcycles_opcyclesToCycles_iCycles`：pOpcycles_opcycle
sToCycles_iCycles : K.pOpcycles i ≫ K.opcyclesToCycles i j ≫ K.iCycles j = K.d i
 j
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `HomologicalComplex.pOpcycles_opcyclesToCycles_iCycles_assoc`：∀ {C : Type
 u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C] {c : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesToCycles_naturality :
    opcyclesMap φ i ≫ opcyclesToCycles L i j = opcyclesToCycles K i j ≫ cyclesMap φ j := by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

variable (C c)

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.opcyclesToCycles i j : K.opcycles i ⟶ K.cycles j` for all
`K : HomologicalComplex C c`. -/
@[simps]
/-
**HomologicalComplex.natTransOpCyclesToCycles** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex`。
形式化陈述：natTransOpCyclesToCycles [CategoryWithHomology C] : opcyclesFunctor C c i 
⟶ cyclesFunctor C c j where app K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `K.opcyclesToCycles i j : K.opcycles i ⟶ K.cycles j` 
for all
`K : HomologicalComplex C c`.
-/
noncomputable def natTransOpCyclesToCycles [CategoryWithHomology C] :
    opcyclesFunctor C c i ⟶ cyclesFunctor C c j where
  app K := K.opcyclesToCycles i j

end HasZeroMorphisms

section Preadditive

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simp]
/-
**HomologicalComplex.HomologySequence.composableArrows** 是 Mathlib 中的一个定义，位于命名空间
 `HomologicalComplex.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`.
-/
noncomputable def composableArrows₃ [K.HasHomology i] [K.HasHomology j] :
    ComposableArrows C 3 :=
  ComposableArrows.mk₃ (K.homologyι i) (K.opcyclesToCycles i j) (K.homologyπ j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.HomologySequence.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalCom
plex.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.HasHomology i] [K.HasHomology j] :
    Mono ((composableArrows₃ K i j).map' 0 1) := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.HomologySequence.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalCom
plex.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.HasHomology i] [K.HasHomology j] :
    Epi ((composableArrows₃ K i j).map' 2 3) := by
  -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
  dsimp [-Fin.reduceFinMk]
  infer_instance

include hij in
/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j` is exact
when `c.Rel i j`. -/
/-
**HomologicalComplex.HomologySequence.composableArrows** 是 Mathlib 中的一个引理，位于命名空间
 `HomologicalComplex.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j` is exact
when `c.Rel i j`.
-/
lemma composableArrows₃_exact [CategoryWithHomology C] :
    (composableArrows₃ K i j).Exact := by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

variable (C)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `HomologicalComplex C c ⥤ ComposableArrows C 3` that maps `K` to the
diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simps]
/-
**HomologicalComplex.HomologySequence.composableArrows** 是 Mathlib 中的一个定义，位于命名空间
 `HomologicalComplex.HomologySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HomologicalComplex C c ⥤ ComposableArrows C 3` that maps `K` to the
diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`.
-/
noncomputable def composableArrows₃Functor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ ComposableArrows C 3 where
  obj K := composableArrows₃ K i j
  map {K L} φ := ComposableArrows.homMk₃ (homologyMap φ i) (opcyclesMap φ i) (cyclesMap φ j)
    -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
    (homologyMap φ j) (by simp) (by simp [-Fin.reduceFinMk]) (by simp [-Fin.reduceFinMk])

end HomologySequence

end Preadditive

section Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is an exact sequence of homological complexes, then
`X₁.opcycles i ⟶ X₂.opcycles i ⟶ X₃.opcycles i ⟶ 0` is exact. This lemma states
the exactness at `X₂.opcycles i`, while the fact that `X₂.opcycles i ⟶ X₃.opcycles i`
is an epi is an instance. -/
/-
**HomologicalComplex.opcycles_right_exact** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex`。
形式化陈述：opcycles_right_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.E
xact) [Epi S.g] (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomol
ogy i] : (ShortComplex.mk (opcyclesMap S.f i) (opcyclesMap S.g i) (by rw [← opcy
clesMap_comp, S.zero, opcyclesMap_zero])).Exact
参数：S : ShortComplex (HomologicalComplex C c)；hS : S.Exact；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `HomologicalComplex.instEpiFOfHasFiniteColimits`：∀ {C : Type u_1} {ι : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}   [in
st_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
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
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsEvalOfHasFiniteLimits`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : Co
mplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsEvalOfHasFiniteColimits`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c 
: ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `HomologicalComplex.d_pOpcycles_assoc`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.opcyclesMap_comp_descOpcycles`：opcyclesMap_comp_descO
pcycles {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j) (hk : L.d j i ≫ k = 
0) (φ : K ⟶ L) : opcyclesMap φ i ≫ L.d…
· 使用引理 `HomologicalComplex.p_descOpcycles`：p_descOpcycles {A : C} (k : K.X i ⟶ A
) (j : ι) (hj : c.prev i = j) (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpc
ycles k j hj hk = k
· 使用定理 `HomologicalComplex.instEpiOpcyclesMapOfF`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is an exact sequence of homological complexes, then
`X₁.opcycles i ⟶ X₂.opcycles i ⟶ X₃.opcycles i ⟶ 0` is exact. This lemma states
the exactness at `X₂.opcycles i`, while the fact that `X₂.opcycles i ⟶ X₃.opcycl
es i`
is an epi is an instance.
-/
lemma opcycles_right_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Epi S.g]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (opcyclesMap S.f i) (opcyclesMap S.g i)
      (by rw [← opcyclesMap_comp, S.zero, opcyclesMap_zero])).Exact := by
  have : Epi (ShortComplex.map S (eval C c i)).g := by dsimp; infer_instance
  have hj := (hS.map (HomologicalComplex.eval C c i)).gIsCokernel
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := CokernelCofork.IsColimit.desc' hj (S.X₂.pOpcycles i ≫ k) (by
      dsimp
      rw [← p_opcyclesMap_assoc, hk, comp_zero])
    dsimp at H
    refine ⟨S.X₃.descOpcycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_epi (S.g.f (c.prev i)), comp_zero, Hom.comm_assoc, H.2,
        d_pOpcycles_assoc, zero_comp]
    · rw [← cancel_epi (S.X₂.pOpcycles i), opcyclesMap_comp_descOpcycles, p_descOpcycles, H.2])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃` is an exact sequence of homological complex, then
`0 ⟶ X₁.cycles i ⟶ X₂.cycles i ⟶ X₃.cycles i` is exact. This lemma states
the exactness at `X₂.cycles i`, while the fact that `X₁.cycles i ⟶ X₂.cycles i`
is a mono is an instance. -/
/-
**HomologicalComplex.cycles_left_exact** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：cycles_left_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exac
t) [Mono S.f] (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomolog
y i] : (ShortComplex.mk (cyclesMap S.f i) (cyclesMap S.g i) (by rw [← cyclesMap_
comp, S.zero, cyclesMap_zero])).Exact
参数：S : ShortComplex (HomologicalComplex C c)；hS : S.Exact；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `HomologicalComplex.instMonoFOfHasFiniteLimits`：∀ {C : Type u_1} {ι : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}   [ins
t_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
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
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsEvalOfHasFiniteLimits`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : Co
mplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsEvalOfHasFiniteColimits`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c 
: ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ i ≫ L.iCycles 
i = K.iCycles i ≫ φ.f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `HomologicalComplex.iCycles_d`：iCycles_d : K.iCycles i ≫ K.d i j = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃` is an exact sequence of homological complex, then
`0 ⟶ X₁.cycles i ⟶ X₂.cycles i ⟶ X₃.cycles i` is exact. This lemma states
the exactness at `X₂.cycles i`, while the fact that `X₁.cycles i ⟶ X₂.cycles i`
is a mono is an instance.
-/
lemma cycles_left_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Mono S.f]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (cyclesMap S.f i) (cyclesMap S.g i)
      (by rw [← cyclesMap_comp, S.zero, cyclesMap_zero])).Exact := by
  have : Mono (ShortComplex.map S (eval C c i)).f := by dsimp; infer_instance
  have hi := (hS.map (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc, ← cyclesMap_i, reassoc_of% hk, zero_comp])
    dsimp at H
    refine ⟨S.X₁.liftCycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

set_option backward.defeqAttrib.useBackward true in
/-- Given a short exact short complex `S : HomologicalComplex C c`, and degrees `i` and `j`
such that `c.Rel i j`, this is the snake diagram whose four lines are respectively
obtained by applying the functors `homologyFunctor C c i`, `opcyclesFunctor C c i`,
`cyclesFunctor C c j`, `homologyFunctor C c j` to `S`. Applying the snake lemma to this
gives the homology sequence of `S`. -/
@[simps]
/-
**HomologicalComplex.HomologySequence.snakeInput** 是 Mathlib 中的一个定义，位于命名空间 `Homo
logicalComplex.HomologySequence`。
形式化陈述：snakeInput (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) : ShortComplex.
SnakeInput C where L₀
参数：hS : S.ShortExact；i j : ι；hij : c.Rel i j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a short exact short complex `S : HomologicalComplex C c`, and degrees `i` 
and `j`
such that `c.Rel i j`, this is the snake diagram whose four lines are respective
ly
obtained by applying the functors `homologyFunctor C c i`, `opcyclesFunctor C c 
i`,
`cyclesFunctor C c j`, `homologyFunctor C c j` to `S`. Applying the snake lemma 
to this
gives the homology sequence of `S`.
-/
noncomputable def snakeInput (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    ShortComplex.SnakeInput C where
  L₀ := (homologyFunctor C c i).mapShortComplex.obj S
  L₁ := (opcyclesFunctor C c i).mapShortComplex.obj S
  L₂ := (cyclesFunctor C c j).mapShortComplex.obj S
  L₃ := (homologyFunctor C c j).mapShortComplex.obj S
  v₀₁ := S.mapNatTrans (natTransHomologyι C c i)
  v₁₂ := S.mapNatTrans (natTransOpCyclesToCycles C c i j)
  v₂₃ := S.mapNatTrans (natTransHomologyπ C c j)
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 0).fIsKernel
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 1).gIsCokernel
  L₁_exact := by
    have := hS.epi_g
    exact opcycles_right_exact S hS.exact i
  L₂_exact := by
    have := hS.mono_f
    exact cycles_left_exact S hS.exact j
  epi_L₁_g := by
    have := hS.epi_g
    dsimp
    infer_instance
  mono_L₂_f := by
    have := hS.mono_f
    dsimp
    infer_instance

end HomologySequence

end Abelian

end HomologicalComplex

namespace CategoryTheory

open HomologicalComplex HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace ShortComplex

namespace ShortExact

/-- The connecting homomorphism `S.X₃.homology i ⟶ S.X₁.homology j` for a short exact
short complex `S`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism `S.X₃.homology i ⟶ S.X₁.homology j` for a short exac
t
short complex `S`.
-/
noncomputable def δ : S.X₃.homology i ⟶ S.X₁.homology j := (snakeInput hS i j hij).δ

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp : hS.δ i j hij ≫ HomologicalComplex.homologyMap S.f j = 0 :=
  (snakeInput hS i j hij).δ_L₃_f

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.ShortExact.comp_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_δ : HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0 :=
  (snakeInput hS i j hij).L₀_g_δ

/-- Exactness of `S.X₃.homology i ⟶ S.X₁.homology j ⟶ S.X₂.homology j`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.homology_exact** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `S.X₃.homology i ⟶ S.X₁.homology j ⟶ S.X₂.homology j`.
-/
lemma homology_exact₁ : (ShortComplex.mk _ _ (δ_comp hS i j hij)).Exact :=
  (snakeInput hS i j hij).L₂'_exact

set_option backward.isDefEq.respectTransparency false in
include hS in
/-- Exactness of `S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.homology_exact** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i`.
-/
lemma homology_exact₂ : (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
    (HomologicalComplex.homologyMap S.g i) (by rw [← HomologicalComplex.homologyMap_comp,
      S.zero, HomologicalComplex.homologyMap_zero])).Exact := by
  by_cases h : c.Rel i (c.next i)
  · exact (snakeInput hS i _ h).L₀_exact
  · have := hS.epi_g
    have : ∀ (K : HomologicalComplex C c), IsIso (K.homologyι i) :=
      fun K => ShortComplex.isIso_homologyι (K.sc i) (K.shape _ _ h)
    have e : S.map (HomologicalComplex.homologyFunctor C c i) ≅
        S.map (HomologicalComplex.opcyclesFunctor C c i) :=
      ShortComplex.isoMk (asIso (S.X₁.homologyι i))
        (asIso (S.X₂.homologyι i)) (asIso (S.X₃.homologyι i)) (by simp) (by simp)
    exact ShortComplex.exact_of_iso e.symm (opcycles_right_exact S hS.exact i)

/-- Exactness of `S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.homology_exact** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j`.
-/
lemma homology_exact₃ : (ShortComplex.mk _ _ (comp_δ hS i j hij)).Exact :=
  (snakeInput hS i j hij).L₁'_exact
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq' {A : C} (x₃ : A ⟶ S.X₃.homology i) (x₂ : A ⟶ S.X₂.opcycles i)
    (x₁ : A ⟶ S.X₁.cycles j)
    (h₂ : x₂ ≫ HomologicalComplex.opcyclesMap S.g i = x₃ ≫ S.X₃.homologyι i)
    (h₁ : x₁ ≫ HomologicalComplex.cyclesMap S.f j = x₂ ≫ S.X₂.opcyclesToCycles i j) :
    x₃ ≫ hS.δ i j hij = x₁ ≫ S.X₁.homologyπ j :=
  (snakeInput hS i j hij).δ_eq x₃ x₂ x₁ h₂ h₁
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq {A : C} (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0)
    (x₂ : A ⟶ S.X₂.X i) (hx₂ : x₂ ≫ S.g.f i = x₃)
    (x₁ : A ⟶ S.X₁.X j) (hx₁ : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j)
    (k : ι) (hk : c.next j = k) :
    S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i ≫ hS.δ i j hij =
      S.X₁.liftCycles x₁ k hk (by
        have := hS.mono_f
        rw [← cancel_mono (S.f.f k), assoc, ← S.f.comm, reassoc_of% hx₁,
          d_comp_d, comp_zero, zero_comp]) ≫ S.X₁.homologyπ j := by
  simpa only [assoc] using hS.δ_eq' i j hij (S.X₃.liftCycles x₃ j
    (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles x₁ k hk _)
      (by simp only [assoc, HomologicalComplex.p_opcyclesMap,
        HomologicalComplex.homology_π_ι,
        HomologicalComplex.liftCycles_i_assoc, reassoc_of% hx₂])
      (by rw [← cancel_mono (S.X₂.iCycles j), HomologicalComplex.liftCycles_comp_cyclesMap,
        HomologicalComplex.liftCycles_i, assoc, assoc, opcyclesToCycles_iCycles,
        HomologicalComplex.p_fromOpcycles, hx₁])
/-
**CategoryTheory.ShortComplex.ShortExact.mono_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_δ (hi : IsZero (S.X₂.homology i)) : Mono (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).mono_δ hi
/-
**CategoryTheory.ShortComplex.ShortExact.epi_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem epi_δ (hj : IsZero (S.X₂.homology j)) : Epi (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).epi_δ hj
/-
**CategoryTheory.ShortComplex.ShortExact.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_δ (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    IsIso (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).isIso_δ hi hj

/-- If `c.Rel i j` and `Hᵢ(X₂), Hⱼ(X₂)` are trivial, `δ` defines an isomorphism
`Hᵢ(X₃) ≅ Hⱼ(X₁)`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c.Rel i j` and `Hᵢ(X₂), Hⱼ(X₂)` are trivial, `δ` defines an isomorphism
`Hᵢ(X₃) ≅ Hⱼ(X₁)`.
-/
noncomputable def δIso (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    S.X₃.homology i ≅ S.X₁.homology j :=
  @asIso _ _ _ _ (hS.δ i j hij) (hS.isIso_δ i j hij hi hj)

end ShortExact

end ShortComplex

end CategoryTheory

