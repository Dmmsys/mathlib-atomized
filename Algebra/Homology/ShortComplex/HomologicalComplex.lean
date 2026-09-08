/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Tactic.NormNum

/-!
# The short complexes attached to homological complexes

In this file, we define a functor
`shortComplexFunctor C c i : HomologicalComplex C c ⥤ ShortComplex C`.
By definition, the image of a homological complex `K` by this functor
is the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`.

The homology `K.homology i` of a homological complex `K` in degree `i` is defined as
the homology of the short complex `(shortComplexFunctor C c i).obj K`, which can be
abbreviated as `K.sc i`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
@[simps]
/-
**HomologicalComplex.shortComplexFunctor'** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex`。
形式化陈述：shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C
 where obj K
参数：i j k : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0

--- 原说明 ---
The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `
i`, `j` and `k`.
-/
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
@[simps!]
/-
**HomologicalComplex.shortComplexFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex`。
形式化陈述：shortComplexFunctor (i : ι)
参数：i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`.
-/
noncomputable def shortComplexFunctor (i : ι) :=
  shortComplexFunctor' C c (c.prev i) i (c.next i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k`
when `c.prev j = i` and `c.next j = k`. -/
@[simps!]
/-
**HomologicalComplex.natIsoSc'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) : shortCompl
exFunctor C c j ≅ shortComplexFunctor' C c i j k
参数：i j k : ι；hi : c.prev j = i；hk : c.next j = k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `shortComplexFunctor C c j ≅ shortComplexFunctor' C c i 
j k`
when `c.prev j = i` and `c.next j = k`.
-/
noncomputable def natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by simp) (by simp)) (by cat_disch)

variable {C c}

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

/-- The short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
/-
**HomologicalComplex.sc'** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：sc'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`
.
-/
abbrev sc' := (shortComplexFunctor' C c i j k).obj K

/-- The short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
/-
**HomologicalComplex.sc** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：sc
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`.
-/
noncomputable abbrev sc := (shortComplexFunctor C c i).obj K

/-- The canonical isomorphism `K.sc j ≅ K.sc' i j k` when `c.prev j = i` and `c.next j = k`. -/
/-
**HomologicalComplex.isoSc'** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：isoSc' (hi : c.prev j = i) (hk : c.next j = k) : K.sc j ≅ K.sc' i j k
参数：hi : c.prev j = i；hk : c.next j = k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.sc j ≅ K.sc' i j k` when `c.prev j = i` and `c.next
 j = k`.
-/
noncomputable abbrev isoSc' (hi : c.prev j = i) (hk : c.next j = k) :
    K.sc j ≅ K.sc' i j k := (natIsoSc' C c i j k hi hk).app K

/-- A homological complex `K` has homology in degree `i` if the associated
short complex `K.sc i` has. -/
/-
**HomologicalComplex.HasHomology** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：HasHomology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homological complex `K` has homology in degree `i` if the associated
short complex `K.sc i` has.
-/
abbrev HasHomology := (K.sc i).HasHomology

variable {K L} in
include iso in
/-
**HomologicalComplex.hasHomology_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：hasHomology_of_iso [K.HasHomology i] : L.HasHomology i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hasHomology_of_iso`：hasHomology_of_iso (e : 
S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂
-/
lemma hasHomology_of_iso [K.HasHomology i] : L.HasHomology i :=
  ShortComplex.hasHomology_of_iso
    ((shortComplexFunctor _ _ i).mapIso iso : K.sc i ≅ L.sc i)

section

variable [K.HasHomology i]

/-- The homology in degree `i` of a homological complex. -/
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology in degree `i` of a homological complex.
-/
noncomputable def homology := (K.sc i).homology

/-- The cycles in degree `i` of a homological complex. -/
/-
**HomologicalComplex.cycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：cycles
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cycles in degree `i` of a homological complex.
-/
noncomputable def cycles := (K.sc i).cycles

/-- The inclusion of the cycles of a homological complex. -/
/-
**HomologicalComplex.iCycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：iCycles : K.cycles i ⟶ K.X i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the cycles of a homological complex.
-/
noncomputable def iCycles : K.cycles i ⟶ K.X i := (K.sc i).iCycles

/-- The homology class map from cycles to the homology of a homological complex. -/
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology class map from cycles to the homology of a homological complex.
-/
noncomputable def homologyπ : K.cycles i ⟶ K.homology i := (K.sc i).homologyπ

variable {i}

/-- The morphism to `K.cycles i` that is induced by a "cycle", i.e. a morphism
to `K.X i` whose postcomposition with the differential is zero. -/
/-
**HomologicalComplex.liftCycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j) (hk : k ≫ K
.d i j = 0) : A ⟶ K.cycles i
参数：k : A ⟶ K.X i；j : ι；hj : c.next i = j；hk : k ≫ K.d i j = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism to `K.cycles i` that is induced by a "cycle", i.e. a morphism
to `K.X i` whose postcomposition with the differential is zero.
-/
noncomputable def liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  (K.sc i).liftCycles k (by subst hj; exact hk)

/-- The morphism to `K.cycles i` that is induced by a "cycle", i.e. a morphism
to `K.X i` whose postcomposition with the differential is zero. -/
/-
**HomologicalComplex.liftCycles'** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j) (hk : k ≫ K.d
 i j = 0) : A ⟶ K.cycles i
参数：k : A ⟶ K.X i；j : ι；hj : c.Rel i j；hk : k ≫ K.d i j = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j

--- 原说明 ---
The morphism to `K.cycles i` that is induced by a "cycle", i.e. a morphism
to `K.X i` whose postcomposition with the differential is zero.
-/
noncomputable abbrev liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  K.liftCycles k j (c.next_eq' hj) hk

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.liftCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j) (hk : k ≫
 K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k
参数：k : A ⟶ K.X i；j : ι；hj : c.next i = j；hk : k ≫ K.d i j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k := by
  dsimp [liftCycles, iCycles]
  simp

variable (i)

/-- The map `K.X i ⟶ K.cycles j` induced by the differential `K.d i j`. -/
/-
**HomologicalComplex.toCycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：toCycles [K.HasHomology j] : K.X i ⟶ K.cycles j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `K.X i ⟶ K.cycles j` induced by the differential `K.d i j`.
-/
noncomputable def toCycles [K.HasHomology j] :
    K.X i ⟶ K.cycles j :=
  K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.iCycles_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：iCycles_d : K.iCycles i ≫ K.d i j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma iCycles_d : K.iCycles i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  · rw [K.shape _ _ hij, comp_zero]

/-- `K.cycles i` is the kernel of `K.d i j` when `c.next i = j`. -/
/-
**HomologicalComplex.cyclesIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：cyclesIsKernel (hj : c.next i = j) : IsLimit (KernelFork.ofι (K.iCycles i)
 (K.iCycles_d i j))
参数：hj : c.next i = j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.iCycles_d`：iCycles_d : K.iCycles i ≫ K.d i j = 0

--- 原说明 ---
`K.cycles i` is the kernel of `K.d i j` when `c.next i = j`.
-/
noncomputable def cyclesIsKernel (hj : c.next i = j) :
    IsLimit (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) := by
  obtain rfl := hj
  exact (K.sc i).cyclesIsKernel

end

@[reassoc (attr := simp)]
/-
**HomologicalComplex.toCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：toCycles_i [K.HasHomology j] : K.toCycles i j ≫ K.iCycles j = K.d i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.liftCycles_i`：liftCycles_i {A : C} (k : A ⟶ K.X i) (j
 : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iC
ycles i = k
-/
lemma toCycles_i [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

section
variable [K.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

end

@[reassoc (attr := simp)]
/-
**HomologicalComplex.d_toCycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：d_toCycles [K.HasHomology k] : K.d i j ≫ K.toCycles j k = 0
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
· 使用引理 `HomologicalComplex.toCycles_i`：toCycles_i [K.HasHomology j] : K.toCycles
 i j ≫ K.iCycles j = K.d i j
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_toCycles [K.HasHomology k] :
    K.d i j ≫ K.toCycles j k = 0 := by
  simp only [← cancel_mono (K.iCycles k), assoc, toCycles_i, d_comp_d, zero_comp]

variable {i j} in
/-
**HomologicalComplex.toCycles_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：toCycles_eq_zero [K.HasHomology j] (hij : ¬ c.Rel i j) : K.toCycles i j = 
0
参数：hij : ¬ c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.instMonoICycles`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.toCycles_i`：toCycles_i [K.HasHomology j] : K.toCycles
 i j ≫ K.iCycles j = K.d i j
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
-/
lemma toCycles_eq_zero [K.HasHomology j] (hij : ¬ c.Rel i j) :
    K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), toCycles_i, zero_comp, K.shape _ _ hij]

variable {i}

section
variable [K.HasHomology i]

@[reassoc]
/-
**HomologicalComplex.comp_liftCycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j) (hk
 : k ≫ K.d i j = 0) (α : A' ⟶ A) : α ≫ K.liftCycles k j hj hk = K.liftCycles (α 
≫ k) j hj (by rw [assoc, hk, comp_zero])
参数：k : A ⟶ K.X i；j : ι；hj : c.next i = j；hk : k ≫ K.d i j = 0；α : A' ⟶ A。
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
· 使用引理 `HomologicalComplex.liftCycles_i`：liftCycles_i {A : C} (k : A ⟶ K.X i) (j
 : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iC
ycles i = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (α : A' ⟶ A) :
    α ≫ K.liftCycles k j hj hk = K.liftCycles (α ≫ k) j hj (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

@[reassoc]
/-
**HomologicalComplex.liftCycles_homology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftCycles_homologyπ_eq_zero_of_boundary {A : C} (k : A ⟶ K.X i) (j : ι)
    (hj : c.next i = j) {i' : ι} (x : A ⟶ K.X i') (hx : k = x ≫ K.d i' i) :
    K.liftCycles k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) ≫ K.homologyπ i = 0 := by
  by_cases h : c.Rel i' i
  · obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  · have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h, comp_zero] at hx
      rw [← cancel_mono (K.iCycles i), zero_comp, liftCycles_i, hx]
    rw [this, zero_comp]

end

variable (i)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.toCycles_comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCycles_comp_homologyπ [K.HasHomology j] :
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

/-- `K.homology j` is the cokernel of `K.toCycles i j : K.X i ⟶ K.cycles j`
when `c.prev j = i`. -/
/-
**HomologicalComplex.homologyIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：homologyIsCokernel (hi : c.prev j = i) [K.HasHomology j] : IsColimit (Coke
rnelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j))
参数：hi : c.prev j = i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.toCycles_comp_homologyπ`：toCycles_comp_homologyπ [K.H
asHomology j] : K.toCycles i j ≫ K.homologyπ j = 0

--- 原说明 ---
`K.homology j` is the cokernel of `K.toCycles i j : K.X i ⟶ K.cycles j`
when `c.prev j = i`.
-/
noncomputable def homologyIsCokernel (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j)) := by
  subst hi
  exact (K.sc j).homologyIsCokernel

section
variable [K.HasHomology i]

/-- The opcycles in degree `i` of a homological complex. -/
/-
**HomologicalComplex.opcycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：opcycles
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opcycles in degree `i` of a homological complex.
-/
noncomputable def opcycles := (K.sc i).opcycles

/-- The projection to the opcycles of a homological complex. -/
/-
**HomologicalComplex.pOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：pOpcycles : K.X i ⟶ K.opcycles i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection to the opcycles of a homological complex.
-/
noncomputable def pOpcycles : K.X i ⟶ K.opcycles i := (K.sc i).pOpcycles

/-- The inclusion map of the homology of a homological complex into its opcycles. -/
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map of the homology of a homological complex into its opcycles.
-/
noncomputable def homologyι : K.homology i ⟶ K.opcycles i := (K.sc i).homologyι

variable {i}

/-- The morphism from `K.opcycles i` that is induced by an "opcycle", i.e. a morphism
from `K.X i` whose precomposition with the differential is zero. -/
/-
**HomologicalComplex.descOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j) (hk : K.d
 j i ≫ k = 0) : K.opcycles i ⟶ A
参数：k : K.X i ⟶ A；j : ι；hj : c.prev i = j；hk : K.d j i ≫ k = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from `K.opcycles i` that is induced by an "opcycle", i.e. a morphis
m
from `K.X i` whose precomposition with the differential is zero.
-/
noncomputable def descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  (K.sc i).descOpcycles k (by subst hj; exact hk)

/-- The morphism from `K.opcycles i` that is induced by an "opcycle", i.e. a morphism
from `K.X i` whose precomposition with the differential is zero. -/
/-
**HomologicalComplex.descOpcycles'** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：descOpcycles' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i) (hk : K.d j
 i ≫ k = 0) : K.opcycles i ⟶ A
参数：k : K.X i ⟶ A；j : ι；hj : c.Rel j i；hk : K.d j i ≫ k = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j

--- 原说明 ---
The morphism from `K.opcycles i` that is induced by an "opcycle", i.e. a morphis
m
from `K.X i` whose precomposition with the differential is zero.
-/
noncomputable abbrev descOpcycles' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  K.descOpcycles k j (c.prev_eq' hj) hk

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.p_descOpcycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j) (hk : K
.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k
参数：k : K.X i ⟶ A；j : ι；hj : c.prev i = j；hk : K.d j i ≫ k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.p_descOpcycles`：p_descOpcycles : S.pOpcycles
 ≫ S.descOpcycles k hk = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k := by
  dsimp [descOpcycles, pOpcycles]
  simp

variable (i)

/-- The map `K.opcycles i ⟶ K.X j` induced by the differential `K.d i j`. -/
/-
**HomologicalComplex.fromOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：fromOpcycles : K.opcycles i ⟶ K.X j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `K.opcycles i ⟶ K.X j` induced by the differential `K.d i j`.
-/
noncomputable def fromOpcycles : K.opcycles i ⟶ K.X j :=
  K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

omit [K.HasHomology i] in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.d_pOpcycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：d_pOpcycles [K.HasHomology j] : K.d i j ≫ K.pOpcycles j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.f_pOpcycles`：f_pOpcycles : S.f ≫ S.pOpcycles
 = 0
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma d_pOpcycles [K.HasHomology j] : K.d i j ≫ K.pOpcycles j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (K.sc j).f_pOpcycles
  · rw [K.shape _ _ hij, zero_comp]

/-- `K.opcycles j` is the cokernel of `K.d i j` when `c.prev j = i`. -/
/-
**HomologicalComplex.opcyclesIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：opcyclesIsCokernel (hi : c.prev j = i) [K.HasHomology j] : IsColimit (Coke
rnelCofork.ofπ (K.pOpcycles j) (K.d_pOpcycles i j))
参数：hi : c.prev j = i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.d_pOpcycles`：d_pOpcycles [K.HasHomology j] : K.d i j 
≫ K.pOpcycles j = 0

--- 原说明 ---
`K.opcycles j` is the cokernel of `K.d i j` when `c.prev j = i`.
-/
noncomputable def opcyclesIsCokernel (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.pOpcycles j) (K.d_pOpcycles i j)) := by
  obtain rfl := hi
  exact (K.sc j).opcyclesIsCokernel

@[reassoc (attr := simp)]
/-
**HomologicalComplex.p_fromOpcycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：p_fromOpcycles : K.pOpcycles i ≫ K.fromOpcycles i j = K.d i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.p_descOpcycles`：p_descOpcycles {A : C} (k : K.X i ⟶ A
) (j : ι) (hj : c.prev i = j) (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpc
ycles k j hj hk = k
-/
lemma p_fromOpcycles :
    K.pOpcycles i ≫ K.fromOpcycles i j = K.d i j :=
  p_descOpcycles _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (K.pOpcycles i) := by
  dsimp only [pOpcycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (K.homologyι i) := by
  dsimp only [homologyι]
  infer_instance

@[reassoc (attr := simp)]
/-
**HomologicalComplex.fromOpcycles_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：fromOpcycles_d : K.fromOpcycles i j ≫ K.d j k = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.p_fromOpcycles_assoc`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromOpcycles_d :
    K.fromOpcycles i j ≫ K.d j k = 0 := by
  simp only [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_comp_d, comp_zero]

variable {i j} in
/-
**HomologicalComplex.fromOpcycles_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex`。
形式化陈述：fromOpcycles_eq_zero (hij : ¬ c.Rel i j) : K.fromOpcycles i j = 0
参数：hij : ¬ c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.p_fromOpcycles`：p_fromOpcycles : K.pOpcycles i ≫ K.fr
omOpcycles i j = K.d i j
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
-/
lemma fromOpcycles_eq_zero (hij : ¬ c.Rel i j) :
    K.fromOpcycles i j = 0 := by
  rw [← cancel_epi (K.pOpcycles i), p_fromOpcycles, comp_zero, K.shape _ _ hij]

variable {i}

@[reassoc]
/-
**HomologicalComplex.descOpcycles_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：descOpcycles_comp {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j) (
hk : K.d j i ≫ k = 0) (α : A ⟶ A') : K.descOpcycles k j hj hk ≫ α = K.descOpcycl
es (k ≫ α) j hj (by rw [reassoc_of% hk, zero_comp])
参数：k : K.X i ⟶ A；j : ι；hj : c.prev i = j；hk : K.d j i ≫ k = 0；α : A ⟶ A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.p_descOpcycles_assoc`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.p_descOpcycles`：p_descOpcycles {A : C} (k : K.X i ⟶ A
) (j : ι) (hj : c.prev i = j) (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpc
ycles k j hj hk = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma descOpcycles_comp {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) (α : A ⟶ A') :
    K.descOpcycles k j hj hk ≫ α = K.descOpcycles (k ≫ α) j hj
      (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, p_descOpcycles]

@[reassoc]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_descOpcycles_eq_zero_of_boundary {A : C} (k : K.X i ⟶ A) (j : ι)
    (hj : c.prev i = j) {i' : ι} (x : K.X i' ⟶ A) (hx : k = K.d i i' ≫ x) :
    K.homologyι i ≫ K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
  by_cases h : c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h, zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i), comp_zero, p_descOpcycles, hx]
    rw [this, comp_zero]

variable (i)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_comp_fromOpcycles :
    K.homologyι i ≫ K.fromOpcycles i j = 0 :=
  K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

/-- `K.homology i` is the kernel of `K.fromOpcycles i j : K.opcycles i ⟶ K.X j`
when `c.next i = j`. -/
/-
**HomologicalComplex.homologyIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：homologyIsKernel (hi : c.next i = j) : IsLimit (KernelFork.ofι (K.homology
ι i) (K.homologyι_comp_fromOpcycles i j))
参数：hi : c.next i = j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homologyι_comp_fromOpcycles`：homologyι_comp_fromOpcyc
les : K.homologyι i ≫ K.fromOpcycles i j = 0

--- 原说明 ---
`K.homology i` is the kernel of `K.fromOpcycles i j : K.opcycles i ⟶ K.X j`
when `c.next i = j`.
-/
noncomputable def homologyIsKernel (hi : c.next i = j) :
    IsLimit (KernelFork.ofι (K.homologyι i) (K.homologyι_comp_fromOpcycles i j)) := by
  subst hi
  exact (K.sc i).homologyIsKernel

variable {K L M}
variable [L.HasHomology i] [M.HasHomology i]

/-- The map `K.homology i ⟶ L.homology i` induced by a morphism in `HomologicalComplex`. -/
/-
**HomologicalComplex.homologyMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homologyMap : K.homology i ⟶ L.homology i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `K.homology i ⟶ L.homology i` induced by a morphism in `HomologicalCompl
ex`.
-/
noncomputable def homologyMap : K.homology i ⟶ L.homology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

/-- The map `K.cycles i ⟶ L.cycles i` induced by a morphism in `HomologicalComplex`. -/
/-
**HomologicalComplex.cyclesMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：cyclesMap : K.cycles i ⟶ L.cycles i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `K.cycles i ⟶ L.cycles i` induced by a morphism in `HomologicalComplex`.
-/
noncomputable def cyclesMap : K.cycles i ⟶ L.cycles i :=
  ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

/-- The map `K.opcycles i ⟶ L.opcycles i` induced by a morphism in `HomologicalComplex`. -/
/-
**HomologicalComplex.opcyclesMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：opcyclesMap : K.opcycles i ⟶ L.opcycles i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `K.opcycles i ⟶ L.opcycles i` induced by a morphism in `HomologicalCompl
ex`.
-/
noncomputable def opcyclesMap : K.opcycles i ⟶ L.opcycles i :=
  ShortComplex.opcyclesMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.cyclesMap_i** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：cyclesMap_i : cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ ≫ S₂.
iCycles = S₁.iCycles ≫ φ.τ₂
-/
lemma cyclesMap_i : cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i :=
  ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]
/-
**HomologicalComplex.p_opcyclesMap** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
形式化陈述：p_opcyclesMap : K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.p_opcyclesMap`：p_opcyclesMap : S₁.pOpcycles 
≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles
-/
lemma p_opcyclesMap : K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i :=
  ShortComplex.p_opcyclesMap _
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono (φ.f i)] : Mono (cyclesMap φ i) := mono_of_mono_fac (cyclesMap_i φ i)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Epi (φ.f i)] : Epi (opcyclesMap φ i) := epi_of_epi_fac (p_opcyclesMap φ i)

variable (K)

@[simp]
/-
**HomologicalComplex.homologyMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_id`：homologyMap_id [HasHomology 
S] : homologyMap (𝟙 S) = 𝟙 _
-/
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

@[simp]
/-
**HomologicalComplex.cyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_id`：cyclesMap_id [HasLeftHomology 
S] : cyclesMap (𝟙 S) = 𝟙 _
-/
lemma cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.cyclesMap_id _

@[simp]
/-
**HomologicalComplex.opcyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：opcyclesMap_id : opcyclesMap (𝟙 K) i = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap_id`：opcyclesMap_id [HasRightHomo
logy S] : opcyclesMap (𝟙 S) = 𝟙 _
-/
lemma opcyclesMap_id : opcyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.opcyclesMap_id _

variable {K}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.homologyMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ
 i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_comp`：homologyMap_comp [HasHomol
ogy S₁] [HasHomology S₂] [HasHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : homolo
gyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫…
-/
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.cyclesMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：cyclesMap_comp : cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_comp`：cyclesMap_comp [HasLeftHomol
ogy S₁] [HasLeftHomology S₂] [HasLeftHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) 
: cyclesMap (φ₁ ≫ φ₂) = cyclesMa…
-/
lemma cyclesMap_comp : cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i := by
  dsimp [cyclesMap]
  rw [Functor.map_comp, ShortComplex.cyclesMap_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.opcyclesMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：opcyclesMap_comp : opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ
 i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap_comp`：opcyclesMap_comp [HasRight
Homology S₁] [HasRightHomology S₂] [HasRightHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂
 ⟶ S₃) : opcyclesMap (φ₁ ≫ φ₂) = o…
-/
lemma opcyclesMap_comp : opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i := by
  dsimp [opcyclesMap]
  rw [Functor.map_comp, ShortComplex.opcyclesMap_comp]

variable (K L)

@[simp]
/-
**HomologicalComplex.homologyMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_zero`：homologyMap_zero [S₁.HasHo
mology] [S₂.HasHomology] : homologyMap (0 : S₁ ⟶ S₂) = 0
-/
lemma homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.homologyMap_zero _ _

@[simp]
/-
**HomologicalComplex.cyclesMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：cyclesMap_zero : cyclesMap (0 : K ⟶ L) i = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_zero`：cyclesMap_zero [HasLeftHomol
ogy S₁] [HasLeftHomology S₂] : cyclesMap (0 : S₁ ⟶ S₂) = 0
-/
lemma cyclesMap_zero : cyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.cyclesMap_zero _ _

@[simp]
/-
**HomologicalComplex.opcyclesMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：opcyclesMap_zero : opcyclesMap (0 : K ⟶ L) i = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap_zero`：opcyclesMap_zero [HasRight
Homology S₁] [HasRightHomology S₂] : opcyclesMap (0 : S₁ ⟶ S₂) = 0
-/
lemma opcyclesMap_zero : opcyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.opcyclesMap_zero _ _

variable {K L}

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_naturality :
    K.homologyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i :=
  ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_naturality :
    homologyMap φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i :=
  ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homology_π_ι :
    K.homologyπ i ≫ K.homologyι i = K.iCycles i ≫ K.pOpcycles i :=
  (K.sc i).homology_π_ι

/-- The isomorphism `K.homology i ≅ L.homology i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
/-
**HomologicalComplex.homologyMapIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：homologyMapIso : K.homology i ≅ L.homology i where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `K.homology i ≅ L.homology i` induced by an isomorphism
in `HomologicalComplex`.
-/
noncomputable def homologyMapIso : K.homology i ≅ L.homology i where
  hom := homologyMap iso.hom i
  inv := homologyMap iso.inv i
  hom_inv_id := by simp [← homologyMap_comp]
  inv_hom_id := by simp [← homologyMap_comp]

/-- The isomorphism `K.cycles i ≅ L.cycles i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
/-
**HomologicalComplex.cyclesMapIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：cyclesMapIso : K.cycles i ≅ L.cycles i where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `K.cycles i ≅ L.cycles i` induced by an isomorphism
in `HomologicalComplex`.
-/
noncomputable def cyclesMapIso : K.cycles i ≅ L.cycles i where
  hom := cyclesMap iso.hom i
  inv := cyclesMap iso.inv i
  hom_inv_id := by simp [← cyclesMap_comp]
  inv_hom_id := by simp [← cyclesMap_comp]

/-- The isomorphism `K.opcycles i ≅ L.opcycles i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
/-
**HomologicalComplex.opcyclesMapIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：opcyclesMapIso : K.opcycles i ≅ L.opcycles i where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `K.opcycles i ≅ L.opcycles i` induced by an isomorphism
in `HomologicalComplex`.
-/
noncomputable def opcyclesMapIso : K.opcycles i ≅ L.opcycles i where
  hom := opcyclesMap iso.hom i
  inv := opcyclesMap iso.inv i
  hom_inv_id := by simp [← opcyclesMap_comp]
  inv_hom_id := by simp [← opcyclesMap_comp]

variable {i}

@[reassoc (attr := simp)]
/-
**HomologicalComplex.opcyclesMap_comp_descOpcycles** 是 Mathlib 中的一个引理，位于命名空间 `Ho
mologicalComplex`。
形式化陈述：opcyclesMap_comp_descOpcycles {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev
 i = j) (hk : L.d j i ≫ k = 0) (φ : K ⟶ L) : opcyclesMap φ i ≫ L.descOpcycles k 
j hj hk = K.descOpcycles (φ.f i ≫ k) j hj (by rw [← φ.comm_assoc, hk, comp_zero]
)
参数：k : L.X i ⟶ A；j : ι；hj : c.prev i = j；hk : L.d j i ≫ k = 0；φ : K ⟶ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.p_descOpcycles`：p_descOpcycles {A : C} (k : K.X i ⟶ A
) (j : ι) (hj : c.prev i = j) (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpc
ycles k j hj hk = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesMap_comp_descOpcycles {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : L.d j i ≫ k = 0) (φ : K ⟶ L) :
    opcyclesMap φ i ≫ L.descOpcycles k j hj hk = K.descOpcycles (φ.f i ≫ k) j hj
      (by rw [← φ.comm_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.liftCycles_comp_cyclesMap** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i =
 j) (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) : K.liftCycles k j hj hk ≫ cyclesMap φ i 
= L.liftCycles (k ≫ φ.f i) j hj (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp
])
参数：k : A ⟶ K.X i；j : ι；hj : c.next i = j；hk : k ≫ K.d i j = 0；φ : K ⟶ L。
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
· 使用定理 `HomologicalComplex.liftCycles_i_assoc`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.liftCycles_i`：liftCycles_i {A : C} (k : A ⟶ K.X i) (j
 : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iC
ycles i = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) :
    K.liftCycles k j hj hk ≫ cyclesMap φ i = L.liftCycles (k ≫ φ.f i) j hj
      (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

section

variable (C c i)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

/-- The `i`th homology functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
/-
**HomologicalComplex.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：homologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C wher
e obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th homology functor `HomologicalComplex C c ⥤ C`.
-/
noncomputable def homologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.homology i
  map f := homologyMap f i

/-- The homology functor to graded objects. -/
@[simps]
/-
**HomologicalComplex.gradedHomologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Homologica
lComplex`。
形式化陈述：gradedHomologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ 
GradedObject ι C where obj K i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology functor to graded objects.
-/
noncomputable def gradedHomologyFunctor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ GradedObject ι C where
  obj K i := K.homology i
  map f i := homologyMap f i

/-- The `i`th cycles functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
/-
**HomologicalComplex.cyclesFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：cyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where 
obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th cycles functor `HomologicalComplex C c ⥤ C`.
-/
noncomputable def cyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.cycles i
  map f := cyclesMap f i

/-- The `i`th opcycles functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
/-
**HomologicalComplex.opcyclesFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：opcyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C wher
e obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th opcycles functor `HomologicalComplex C c ⥤ C`.
-/
noncomputable def opcyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.opcycles i
  map f := opcyclesMap f i

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.homologyπ i : K.cycles i ⟶ K.homology i`
for all `K : HomologicalComplex C c`. -/
@[simps]
/-
**HomologicalComplex.natTransHomology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `K.homologyπ i : K.cycles i ⟶ K.homology i`
for all `K : HomologicalComplex C c`.
-/
noncomputable def natTransHomologyπ [CategoryWithHomology C] :
    cyclesFunctor C c i ⟶ homologyFunctor C c i where
  app K := K.homologyπ i

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.homologyι i : K.homology i ⟶ K.opcycles i`
for all `K : HomologicalComplex C c`. -/
@[simps]
/-
**HomologicalComplex.natTransHomology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `K.homologyι i : K.homology i ⟶ K.opcycles i`
for all `K : HomologicalComplex C c`.
-/
noncomputable def natTransHomologyι [CategoryWithHomology C] :
    homologyFunctor C c i ⟶ opcyclesFunctor C c i where
  app K := K.homologyι i

/-- The natural isomorphism `K.homology i ≅ (K.sc i).homology`
for all homological complexes `K`. -/
@[simps!]
/-
**HomologicalComplex.homologyFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：homologyFunctorIso [CategoryWithHomology C] : homologyFunctor C c i ≅ shor
tComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `K.homology i ≅ (K.sc i).homology`
for all homological complexes `K`.
-/
noncomputable def homologyFunctorIso [CategoryWithHomology C] :
    homologyFunctor C c i ≅
      shortComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C :=
  Iso.refl _

/-- The natural isomorphism `K.homology j ≅ (K.sc' i j k).homology`
for all homological complexes `K` when `c.prev j = i` and `c.next j = k`. -/
/-
**HomologicalComplex.homologyFunctorIso'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex`。
形式化陈述：homologyFunctorIso' [CategoryWithHomology C] (hi : c.prev j = i) (hk : c.n
ext j = k) : homologyFunctor C c j ≅ shortComplexFunctor' C c i j k ⋙ ShortCompl
ex.homologyFunctor C
参数：hi : c.prev j = i；hk : c.next j = k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `K.homology j ≅ (K.sc' i j k).homology`
for all homological complexes `K` when `c.prev j = i` and `c.next j = k`.
-/
noncomputable def homologyFunctorIso' [CategoryWithHomology C]
    (hi : c.prev j = i) (hk : c.next j = k) :
    homologyFunctor C c j ≅
      shortComplexFunctor' C c i j k ⋙ ShortComplex.homologyFunctor C :=
  homologyFunctorIso C c j ≪≫ Functor.isoWhiskerRight (natIsoSc' C c i j k hi hk) _
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : (homologyFunctor C c i).PreservesZeroMorphisms where
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : (opcyclesFunctor C c i).PreservesZeroMorphisms where
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : (cyclesFunctor C c i).PreservesZeroMorphisms where

end

end

section

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]
include hj h

/-
**HomologicalComplex.isIso_iCycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
形式化陈述：isIso_iCycles : IsIso (K.iCycles i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.isIso_iCycles`：isIso_iCycles (hg : S.g = 0) 
: IsIso S.iCycles
-/
lemma isIso_iCycles : IsIso (K.iCycles i) := by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

/-- The canonical isomorphism `K.cycles i ≅ K.X i` when the differential from `i` is zero. -/
@[simps! hom]
/-
**HomologicalComplex.iCyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：iCyclesIso : K.cycles i ≅ K.X i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isIso_iCycles`：isIso_iCycles : IsIso (K.iCycles i)

--- 原说明 ---
The canonical isomorphism `K.cycles i ≅ K.X i` when the differential from `i` is
 zero.
-/
noncomputable def iCyclesIso : K.cycles i ≅ K.X i :=
  have := K.isIso_iCycles i j hj h
  asIso (K.iCycles i)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.iCyclesIso_hom_inv_id** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex`。
形式化陈述：iCyclesIso_hom_inv_id : K.iCycles i ≫ (K.iCyclesIso i j hj h).inv = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma iCyclesIso_hom_inv_id :
    K.iCycles i ≫ (K.iCyclesIso i j hj h).inv = 𝟙 _ :=
  (K.iCyclesIso i j hj h).hom_inv_id

@[reassoc (attr := simp)]
/-
**HomologicalComplex.iCyclesIso_inv_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex`。
形式化陈述：iCyclesIso_inv_hom_id : (K.iCyclesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma iCyclesIso_inv_hom_id :
    (K.iCyclesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _ :=
  (K.iCyclesIso i j hj h).inv_hom_id
/-
**HomologicalComplex.isIso_homology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_homologyι : IsIso (K.homologyι i) :=
  ShortComplex.isIso_homologyι _ (by cat_disch)

/-- The canonical isomorphism `K.homology i ≅ K.opcycles i`
when the differential from `i` is zero. -/
@[simps! hom]
/-
**HomologicalComplex.isoHomology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.homology i ≅ K.opcycles i`
when the differential from `i` is zero.
-/
noncomputable def isoHomologyι : K.homology i ≅ K.opcycles i :=
  have := K.isIso_homologyι i j hj h
  asIso (K.homologyι i)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.isoHomology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomologyι_hom_inv_id :
    K.homologyι i ≫ (K.isoHomologyι i j hj h).inv = 𝟙 _ :=
  (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]
/-
**HomologicalComplex.isoHomology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomologyι_inv_hom_id :
    (K.isoHomologyι i j hj h).inv ≫ K.homologyι i = 𝟙 _ :=
  (K.isoHomologyι i j hj h).inv_hom_id

end

section

variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]
include hi h

/-
**HomologicalComplex.isIso_pOpcycles** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：isIso_pOpcycles : IsIso (K.pOpcycles j)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.isIso_pOpcycles`：isIso_pOpcycles (hf : S.f =
 0) : IsIso S.pOpcycles
-/
lemma isIso_pOpcycles : IsIso (K.pOpcycles j) := by
  obtain rfl := hi
  exact ShortComplex.isIso_pOpcycles _ h

/-- The canonical isomorphism `K.X j ≅ K.opCycles j` when the differential to `j` is zero. -/
@[simps! hom]
/-
**HomologicalComplex.pOpcyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：pOpcyclesIso : K.X j ≅ K.opcycles j
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isIso_pOpcycles`：isIso_pOpcycles : IsIso (K.pOpcycles
 j)

--- 原说明 ---
The canonical isomorphism `K.X j ≅ K.opCycles j` when the differential to `j` is
 zero.
-/
noncomputable def pOpcyclesIso : K.X j ≅ K.opcycles j :=
  have := K.isIso_pOpcycles i j hi h
  asIso (K.pOpcycles j)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcyclesIso_hom_inv_id** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：pOpcyclesIso_hom_inv_id : K.pOpcycles j ≫ (K.pOpcyclesIso i j hi h).inv = 
𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma pOpcyclesIso_hom_inv_id :
    K.pOpcycles j ≫ (K.pOpcyclesIso i j hi h).inv = 𝟙 _ :=
  (K.pOpcyclesIso i j hi h).hom_inv_id

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcyclesIso_inv_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：pOpcyclesIso_inv_hom_id : (K.pOpcyclesIso i j hi h).inv ≫ K.pOpcycles j = 
𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma pOpcyclesIso_inv_hom_id :
    (K.pOpcyclesIso i j hi h).inv ≫ K.pOpcycles j = 𝟙 _ :=
  (K.pOpcyclesIso i j hi h).inv_hom_id
/-
**HomologicalComplex.isIso_homology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_homologyπ : IsIso (K.homologyπ j) :=
  ShortComplex.isIso_homologyπ _ (by cat_disch)

/-- The canonical isomorphism `K.cycles j ≅ K.homology j`
when the differential to `j` is zero. -/
@[simps! hom]
/-
**HomologicalComplex.isoHomology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.cycles j ≅ K.homology j`
when the differential to `j` is zero.
-/
noncomputable def isoHomologyπ : K.cycles j ≅ K.homology j :=
  have := K.isIso_homologyπ i j hi h
  asIso (K.homologyπ j)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.isoHomology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomologyπ_hom_inv_id :
    K.homologyπ j ≫ (K.isoHomologyπ i j hi h).inv = 𝟙 _ :=
  (K.isoHomologyπ i j hi h).hom_inv_id

@[reassoc (attr := simp)]
/-
**HomologicalComplex.isoHomology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomologyπ_inv_hom_id :
    (K.isoHomologyπ i j hi h).inv ≫ K.homologyπ j = 𝟙 _ :=
  (K.isoHomologyπ i j hi h).inv_hom_id

end

section

variable {K L}

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.epi_homologyMap_of_epi_of_not_rel** 是 Mathlib 中的一个引理，位于命名空间
 `HomologicalComplex`。
形式化陈述：epi_homologyMap_of_epi_of_not_rel (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L
.HasHomology i] [Epi (φ.f i)] (hi : forall j, ¬ c.Rel i j) : Epi (homologyMap φ 
i)
参数：φ : K ⟶ L；i : ι；φ.f i；hi : forall j, ¬ c.Rel i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.isoHomologyι_hom`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.homologyι_naturality`：homologyι_naturality : homology
Map φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MorphismProperty.epimorphisms.infer_property`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Catego
ryTheory.Epi f],   CategoryTheory.MorphismPropert…
· 使用定理 `HomologicalComplex.instEpiOpcyclesMapOfF`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {ι : Type u_2} {c : Com…
-/
lemma epi_homologyMap_of_epi_of_not_rel (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [Epi (φ.f i)] (hi : ∀ j, ¬ c.Rel i j) :
    Epi (homologyMap φ i) :=
  ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyι i _ rfl (shape _ _ _ (by tauto))))).2
      (MorphismProperty.epimorphisms.infer_property (opcyclesMap φ i))

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.mono_homologyMap_of_mono_of_not_rel** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex`。
形式化陈述：mono_homologyMap_of_mono_of_not_rel (φ : K ⟶ L) (j : ι) [K.HasHomology j] 
[L.HasHomology j] [Mono (φ.f j)] (hj : forall i, ¬ c.Rel i j) : Mono (homologyMa
p φ j)
参数：φ : K ⟶ L；j : ι；φ.f j；hj : forall i, ¬ c.Rel i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.isoHomologyπ_hom`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.homologyπ_naturality`：homologyπ_naturality : K.homolo
gyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.infer_property`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Categ
oryTheory.Mono f],   CategoryTheory.MorphismProper…
· 使用定理 `HomologicalComplex.instMonoCyclesMapOfF`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {ι : Type u_2} {c : Com…
-/
lemma mono_homologyMap_of_mono_of_not_rel (φ : K ⟶ L) (j : ι)
    [K.HasHomology j] [L.HasHomology j] [Mono (φ.f j)] (hj : ∀ i, ¬ c.Rel i j) :
    Mono (homologyMap φ j) :=
  ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyπ _ j rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyπ _ j rfl (shape _ _ _ (by tauto))))).1
      (MorphismProperty.monomorphisms.infer_property (cyclesMap φ j))

end

/-- A homological complex `K` is exact at `i` if the short complex `K.sc i` is exact. -/
/-
**HomologicalComplex.ExactAt** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：ExactAt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homological complex `K` is exact at `i` if the short complex `K.sc i` is exact
.
-/
def ExactAt := (K.sc i).Exact
/-
**HomologicalComplex.exactAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：exactAt_iff : K.ExactAt i ↔ (K.sc i).Exact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exactAt_iff :
    K.ExactAt i ↔ (K.sc i).Exact := by rfl

variable {K i} in
/-
**HomologicalComplex.ExactAt.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x.ExactAt`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} {
K : HomologicalComplex C c} {i : ι},   K.ExactAt i → ∀ {L : HomologicalComplex C
 c} (e : K ≅ L), L.ExactAt i
参数：e : K ≅ L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.exactAt_iff`：exactAt_iff : K.ExactAt i ↔ (K.sc i).Exa
ct
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
-/
lemma ExactAt.of_iso (hK : K.ExactAt i) {L : HomologicalComplex C c} (e : K ≅ L) :
    L.ExactAt i := by
  rw [exactAt_iff] at hK ⊢
  exact ShortComplex.exact_of_iso ((shortComplexFunctor C c i).mapIso e) hK

variable {K i} in
/-
**HomologicalComplex.ExactAt.of_isZero** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCom
plex.ExactAt`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} {
K : HomologicalComplex C c} {i : ι},   CategoryTheory.Limits.IsZero (K.X i) → K.
ExactAt i
参数：K.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
-/
lemma ExactAt.of_isZero (h : IsZero (K.X i)) : K.ExactAt i :=
  ShortComplex.exact_of_isZero_X₂ _ h
/-
**HomologicalComplex.exactAt_iff'** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：exactAt_iff' (hi : c.prev j = i) (hk : c.next j = k) : K.ExactAt j ↔ (K.sc
' i j k).Exact
参数：hi : c.prev j = i；hk : c.next j = k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_iso`：exact_iff_of_iso (e : S₁ ≅
 S₂) : S₁.Exact ↔ S₂.Exact
-/
lemma exactAt_iff' (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ (K.sc' i j k).Exact :=
  ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)
/-
**HomologicalComplex.exactAt_iff_isZero_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：exactAt_iff_isZero_homology [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.ho
mology i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.exactAt_iff`：exactAt_iff : K.ExactAt i ↔ (K.sc i).Exa
ct
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_isZero_homology`：exact_iff_isZero_
homology [S.HasHomology] : S.Exact ↔ IsZero S.homology
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exactAt_iff_isZero_homology [K.HasHomology i] :
    K.ExactAt i ↔ IsZero (K.homology i) := by
  dsimp [homology]
  rw [exactAt_iff, ShortComplex.exact_iff_isZero_homology]

variable {K i} in
/-
**HomologicalComplex.ExactAt.isZero_homology** 是 Mathlib 中的一个定理，位于命名空间 `Homologi
calComplex.ExactAt`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} {
K : HomologicalComplex C c} {i : ι} [inst_2 : K.HasHomology i],   K.ExactAt i → 
CategoryTheory.Limits.IsZero (K.homology i)
参数：K.homology i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
-/
lemma ExactAt.isZero_homology [K.HasHomology i] (h : K.ExactAt i) :
    IsZero (K.homology i) := by
  rwa [← exactAt_iff_isZero_homology]

/-- A homological complex `K` is acyclic if it is exact at `i` for any `i`. -/
/-
**HomologicalComplex.Acyclic** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：Acyclic
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homological complex `K` is acyclic if it is exact at `i` for any `i`.
-/
def Acyclic := ∀ i, K.ExactAt i
/-
**HomologicalComplex.acyclic_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：acyclic_iff : K.Acyclic ↔ forall i, K.ExactAt i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma acyclic_iff :
    K.Acyclic ↔ ∀ i, K.ExactAt i := by rfl
/-
**HomologicalComplex.acyclic_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：acyclic_of_isZero (hK : IsZero K) : K.Acyclic
参数：hK : IsZero K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.acyclic_iff`：acyclic_iff : K.Acyclic ↔ forall i, K.Ex
actAt i
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
-/
lemma acyclic_of_isZero (hK : IsZero K) :
    K.Acyclic := by
  rw [acyclic_iff]
  intro i
  apply ShortComplex.exact_of_isZero_X₂
  exact (eval _ _ i).map_isZero hK

end HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : ChainComplex C ℕ) (φ : K ⟶ L) [K.HasHomology 0]

/-
**ChainComplex.isIso_iCycles** 是 Mathlib 中的一个实例，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_iCycles₀ : IsIso (K.iCycles 0) :=
  K.isIso_iCycles 0 0 (by simp) (by simp)

/-- The canonical isomorphism `K.cycles 0 ≅ K.X 0` for a chain complex `K`
indexed by `ℕ`. -/
/-
**ChainComplex.cycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.cycles 0 ≅ K.X 0` for a chain complex `K`
indexed by `ℕ`.
-/
noncomputable abbrev cycles₀Iso : K.cycles 0 ≅ K.X 0 :=
  K.iCyclesIso 0 0 (by simp) (by simp)
/-
**ChainComplex.isIso_homology** 是 Mathlib 中的一个实例，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_homologyι₀ :
    IsIso (K.homologyι 0) :=
  K.isIso_homologyι 0 _ rfl (by simp)

/-- The canonical isomorphism `K.homology 0 ≅ K.opcycles 0` for a chain complex `K`
indexed by `ℕ`. -/
/-
**ChainComplex.isoHomology** 是 Mathlib 中的一个缩写定义，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.homology 0 ≅ K.opcycles 0` for a chain complex `K`
indexed by `ℕ`.
-/
noncomputable abbrev isoHomologyι₀ : K.homology 0 ≅ K.opcycles 0 :=
  K.isoHomologyι 0 _ rfl (by simp)

variable {K L}

@[reassoc (attr := simp)]
/-
**ChainComplex.isoHomology** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomologyι₀_inv_naturality [L.HasHomology 0] :
    K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.opcyclesMap φ 0 ≫ L.isoHomologyι₀.inv := by
  simp only [assoc, ← cancel_mono (L.homologyι 0),
    HomologicalComplex.homologyι_naturality, HomologicalComplex.isoHomologyι_inv_hom_id_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, comp_id]

end ChainComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : CochainComplex C ℕ) (φ : K ⟶ L) [K.HasHomology 0]

/-
**CochainComplex.isIso_pOpcycles** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_pOpcycles₀ : IsIso (K.pOpcycles 0) :=
  K.isIso_pOpcycles 0 0 (by simp) (by simp)

/-- The canonical isomorphism `K.X 0 ≅ K.opcycles 0` for a cochain complex `K`
indexed by `ℕ`. -/
/-
**CochainComplex.opcycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.X 0 ≅ K.opcycles 0` for a cochain complex `K`
indexed by `ℕ`.
-/
noncomputable abbrev opcycles₀Iso : K.X 0 ≅ K.opcycles 0 :=
  K.pOpcyclesIso 0 0 (by simp) (by simp)
/-
**CochainComplex.isIso_homology** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_homologyπ₀ :
    IsIso (K.homologyπ 0) :=
  K.isIso_homologyπ _ 0 rfl (by simp)

/-- The canonical isomorphism `K.cycles 0 ≅ K.homology 0` for a cochain complex `K`
indexed by `ℕ`. -/
/-
**CochainComplex.isoHomology** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.cycles 0 ≅ K.homology 0` for a cochain complex `K`
indexed by `ℕ`.
-/
noncomputable abbrev isoHomologyπ₀ : K.cycles 0 ≅ K.homology 0 :=
  K.isoHomologyπ _ 0 rfl (by simp)

variable {K L}

@[reassoc (attr := simp)]
/-
**CochainComplex.isoHomology** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomologyπ₀_inv_naturality [L.HasHomology 0] :
    HomologicalComplex.homologyMap φ 0 ≫ L.isoHomologyπ₀.inv =
      K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap φ 0 := by
  simp only [← cancel_epi (K.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id, comp_id,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

end CochainComplex

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (φ ψ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HomologicalComplex.homologyMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：homologyMap_neg : homologyMap (-φ) i = -homologyMap φ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_neg`：homologyMap_neg : homologyM
ap (-φ) = -homologyMap φ
-/
lemma homologyMap_neg : homologyMap (-φ) i = -homologyMap φ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HomologicalComplex.homologyMap_add** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：homologyMap_add : homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ 
i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_add`：homologyMap_add : homologyM
ap (φ + φ') = homologyMap φ + homologyMap φ'
-/
lemma homologyMap_add : homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HomologicalComplex.homologyMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：homologyMap_sub : homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ 
i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_sub`：homologyMap_sub : homologyM
ap (φ - φ') = homologyMap φ - homologyMap φ'
-/
lemma homologyMap_sub : homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : (homologyFunctor C c i).Additive where

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.isIso_liftCycles_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`
。
形式化陈述：isIso_liftCycles_iff (K : CochainComplex C Nat) {X : C} (φ : X ⟶ K.X 0) [K
.HasHomology 0] (hφ : φ ≫ K.d 0 1 = 0) : IsIso (K.liftCycles φ 1 (by simp) hφ) ↔
 (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ
参数：K : CochainComplex C Nat；φ : X ⟶ K.X 0；hφ : φ ≫ K.d 0 1 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.shortComplexFunctor_obj_f`：∀ (C : Type u_1) [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CochainComplex.prev_nat_zero`：prev_nat_zero : (ComplexShape.up Nat).prev
 0 = 0
· 使用定理 `ComplexShape.up_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRightCa
ncelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.up α).Rel i j = (i + 1 = 
j)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.shortComplexFunctor_obj_g`：∀ (C : Type u_1) [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_isIso_liftCycles`：quasiIso_iff_
isIso_liftCycles (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0
) : QuasiIso φ ↔ IsIso (S₂.liftCycles φ.τ₂ (by …
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_of_zeros`：quasiIso_iff_of_zeros
 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ :
 S₂.f = 0) : QuasiIso φ ↔ (ShortComplex…
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
-/
lemma isIso_liftCycles_iff (K : CochainComplex C ℕ) {X : C} (φ : X ⟶ K.X 0)
    [K.HasHomology 0] (hφ : φ ≫ K.d 0 1 = 0) :
    IsIso (K.liftCycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.up ℕ).next 0 = i)
    (hφ : φ ≫ K.d 0 i = 0), IsIso (K.liftCycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) ⟶ K.sc 0 :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_liftCycles α rfl rfl (by simp)).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros α rfl rfl (by simp))

end CochainComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-
**ChainComplex.isIso_descOpcycles_iff** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
形式化陈述：isIso_descOpcycles_iff (K : ChainComplex C Nat) {X : C} (φ : K.X 0 ⟶ X) [K
.HasHomology 0] (hφ : K.d 1 0 ≫ φ = 0) : IsIso (K.descOpcycles φ 1 (by simp) hφ)
 ↔ (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ
参数：K : ChainComplex C Nat；φ : K.X 0 ⟶ X；hφ : K.d 1 0 ≫ φ = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.shortComplexFunctor_obj_f`：∀ (C : Type u_1) [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `HomologicalComplex.shortComplexFunctor_obj_g`：∀ (C : Type u_1) [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `ChainComplex.next_nat_zero`：next_nat_zero : (ComplexShape.down Nat).next
 0 = 0
· 使用定理 `ComplexShape.down_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRight
CancelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.down α).Rel i j = (j + 
1 = i)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_isIso_descOpcycles`：quasiIso_if
f_isIso_descOpcycles (φ : S₁ ⟶ S₂) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g
 = 0) : QuasiIso φ ↔ IsIso (S₁.descOpcycles φ.τ₂ …
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_of_zeros'`：quasiIso_iff_of_zero
s' {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂
 : S₂.g = 0) : QuasiIso φ ↔ (ShortComple…
· 使用定理 `ChainComplex.prev`：prev (α : Type*) [AddRightCancelSemigroup α] [One α] 
(i : α) : (ComplexShape.down α).prev i = i + 1
-/
lemma isIso_descOpcycles_iff (K : ChainComplex C ℕ) {X : C} (φ : K.X 0 ⟶ X)
    [K.HasHomology 0] (hφ : K.d 1 0 ≫ φ = 0) :
    IsIso (K.descOpcycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.down ℕ).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

end ChainComplex

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

/-- The cycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
/-
**HomologicalComplex.cyclesIsoSc'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：cyclesIsoSc' : K.cycles j ≅ (K.sc' i j k).cycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`.
-/
noncomputable def cyclesIsoSc' : K.cycles j ≅ (K.sc' i j k).cycles :=
  ShortComplex.cyclesMapIso (K.isoSc' i j k hi hk)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.cyclesIsoSc'_hom_iCycles** 是 Mathlib 中的一个定理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) 
  [inst_2 : K.HasHomology j] [inst_3 : (K.sc' i j k).HasHomology],   CategoryThe
ory.CategoryStruct.comp (K.cyclesIsoSc' i j k hi hk).hom (K.sc' i j k).iCycles =
 K.iCycles j
参数：K : HomologicalComplex C c；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc
' i j k；K.cyclesIsoSc' i j k hi hk；K.sc' i j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ ≫ S₂.
iCycles = S₁.iCycles ≫ φ.τ₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma cyclesIsoSc'_hom_iCycles :
    (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).iCycles = K.iCycles j := by
  dsimp [cyclesIsoSc']
  simp only [ShortComplex.cyclesMap_i, shortComplexFunctor_obj_X₂, shortComplexFunctor'_obj_X₂,
    natIsoSc'_hom_app_τ₂, comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.cyclesIsoSc'_inv_iCycles** 是 Mathlib 中的一个定理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) 
  [inst_2 : K.HasHomology j] [inst_3 : (K.sc' i j k).HasHomology],   CategoryThe
ory.CategoryStruct.comp (K.cyclesIsoSc' i j k hi hk).inv (K.iCycles j) = (K.sc' 
i j k).iCycles
参数：K : HomologicalComplex C c；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc
' i j k；K.cyclesIsoSc' i j k hi hk；K.iCycles j；K.sc' i j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ ≫ S₂.
iCycles = S₁.iCycles ≫ φ.τ₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesIsoSc'_inv_iCycles :
    (K.cyclesIsoSc' i j k hi hk).inv ≫ K.iCycles j = (K.sc' i j k).iCycles := by
  simp [cyclesIsoSc', iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.toCycles_cyclesIsoSc'_hom** 是 Mathlib 中的一个定理，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) 
  [inst_2 : K.HasHomology j] [inst_3 : (K.sc' i j k).HasHomology],   CategoryThe
ory.CategoryStruct.comp (K.toCycles i j) (K.cyclesIsoSc' i j k hi hk).hom = (K.s
c' i j k).toCycles
参数：K : HomologicalComplex C c；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc
' i j k；K.toCycles i j；K.cyclesIsoSc' i j k hi hk；K.sc' i j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.cyclesIsoSc'_hom_iCycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.toCycles_i`：toCycles_i [K.HasHomology j] : K.toCycles
 i j ≫ K.iCycles j = K.d i j
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `HomologicalComplex.shortComplexFunctor'_obj_f`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toCycles_cyclesIsoSc'_hom :
    K.toCycles i j ≫ (K.cyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).toCycles := by
  simp only [← cancel_mono (K.sc' i j k).iCycles, assoc, cyclesIsoSc'_hom_iCycles,
    toCycles_i, ShortComplex.toCycles_i, shortComplexFunctor'_obj_f]

/-- The homology of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
/-
**HomologicalComplex.opcyclesIsoSc'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：opcyclesIsoSc' : K.opcycles j ≅ (K.sc' i j k).opcycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`.
-/
noncomputable def opcyclesIsoSc' : K.opcycles j ≅ (K.sc' i j k).opcycles :=
  ShortComplex.opcyclesMapIso (K.isoSc' i j k hi hk)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcycles_opcyclesIsoSc'_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) 
  [inst_2 : K.HasHomology j] [inst_3 : (K.sc' i j k).HasHomology],   CategoryThe
ory.CategoryStruct.comp (K.sc' i j k).pOpcycles (K.opcyclesIsoSc' i j k hi hk).i
nv = K.pOpcycles j
参数：K : HomologicalComplex C c；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc
' i j k；K.sc' i j k；K.opcyclesIsoSc' i j k hi hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.ShortComplex.p_opcyclesMap`：p_opcyclesMap : S₁.pOpcycles 
≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma pOpcycles_opcyclesIsoSc'_inv :
    (K.sc' i j k).pOpcycles ≫ (K.opcyclesIsoSc' i j k hi hk).inv = K.pOpcycles j := by
  dsimp [opcyclesIsoSc']
  simp only [ShortComplex.p_opcyclesMap, shortComplexFunctor'_obj_X₂, shortComplexFunctor_obj_X₂,
    natIsoSc'_inv_app_τ₂, id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom** 是 Mathlib 中的一个定理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) 
  [inst_2 : K.HasHomology j] [inst_3 : (K.sc' i j k).HasHomology],   CategoryThe
ory.CategoryStruct.comp (K.pOpcycles j) (K.opcyclesIsoSc' i j k hi hk).hom = (K.
sc' i j k).pOpcycles
参数：K : HomologicalComplex C c；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc
' i j k；K.pOpcycles j；K.opcyclesIsoSc' i j k hi hk；K.sc' i j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.p_opcyclesMap`：p_opcyclesMap : S₁.pOpcycles 
≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pOpcycles_opcyclesIsoSc'_hom :
    K.pOpcycles j ≫ (K.opcyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).pOpcycles := by
  simp [opcyclesIsoSc', pOpcycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.opcyclesIsoSc'_inv_fromOpcycles** 是 Mathlib 中的一个定理，位于命名空间 `
HomologicalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) 
  [inst_2 : K.HasHomology j] [inst_3 : (K.sc' i j k).HasHomology],   CategoryThe
ory.CategoryStruct.comp (K.opcyclesIsoSc' i j k hi hk).inv (K.fromOpcycles j k) 
=     (K.sc' i j k).fromOpcycles
参数：K : HomologicalComplex C c；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc
' i j k；K.opcyclesIsoSc' i j k hi hk；K.fromOpcycles j k；K.sc' i j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.pOpcycles_opcyclesIsoSc'_inv_assoc`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.p_fromOpcycles`：p_fromOpcycles : K.pOpcycles i ≫ K.fr
omOpcycles i j = K.d i j
· 使用引理 `CategoryTheory.ShortComplex.p_fromOpcycles`：p_fromOpcycles : S.pOpcycles
 ≫ S.fromOpcycles = S.g
· 使用定理 `HomologicalComplex.shortComplexFunctor'_obj_g`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesIsoSc'_inv_fromOpcycles :
    (K.opcyclesIsoSc' i j k hi hk).inv ≫ K.fromOpcycles j k =
      (K.sc' i j k).fromOpcycles := by
  simp only [← cancel_epi (K.sc' i j k).pOpcycles, pOpcycles_opcyclesIsoSc'_inv_assoc,
    p_fromOpcycles, ShortComplex.p_fromOpcycles, shortComplexFunctor'_obj_g]

/-- The opcycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
/-
**HomologicalComplex.homologyIsoSc'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：homologyIsoSc' : K.homology j ≅ (K.sc' i j k).homology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opcycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`.
-/
noncomputable def homologyIsoSc' : K.homology j ≅ (K.sc' i j k).homology :=
  ShortComplex.homologyMapIso (K.isoSc' i j k hi hk)

@[simp]
/-
**HomologicalComplex.homology_sc'_eq_homology** 是 Mathlib 中的一个定理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (j : ι) [inst_2 : K.HasHomology j]   [inst_3 : (K.sc
' (c.prev j) j (c.next j)).HasHomology], (K.sc' (c.prev j) j (c.next j)).homolog
y = K.homology j
参数：K : HomologicalComplex C c；j : ι；K.sc' (c.prev j) j (c.next j)；K.sc' (c.prev 
j) j (c.next j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homology_sc'_eq_homology [(K.sc' (c.prev j) j (c.next j)).HasHomology] :
    (K.sc' (c.prev j) j (c.next j)).homology = K.homology j := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**HomologicalComplex.homologyIsoSc'_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Homologic
alComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} (
K : HomologicalComplex C c) (j : ι) [inst_2 : K.HasHomology j]   [inst_3 : (K.sc
' (c.prev j) j (c.next j)).HasHomology],   K.homologyIsoSc' (c.prev j) j (c.next
 j) ⋯ ⋯ = CategoryTheory.Iso.refl (K.homology j)
参数：K : HomologicalComplex C c；j : ι；K.sc' (c.prev j) j (c.next j)；c.prev j；c.nex
t j；K.homology j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_id`：homologyMap_id [HasHomology 
S] : homologyMap (𝟙 S) = 𝟙 _
-/
lemma homologyIsoSc'_eq_refl
    [(K.sc' (c.prev j) j (c.next j)).HasHomology] :
    dsimp% K.homologyIsoSc' _ j _ rfl rfl = Iso.refl _ := by
  ext : 1
  apply ShortComplex.homologyMap_id

@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_homologyIsoSc'_hom :
    K.homologyπ j ≫ (K.homologyIsoSc' i j k hi hk).hom =
      (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyπ := by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_homologyIsoSc'_inv :
    (K.sc' i j k).homologyπ ≫ (K.homologyIsoSc' i j k hi hk).inv =
      (K.cyclesIsoSc' i j k hi hk).inv ≫ K.homologyπ j := by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homologyIsoSc'_hom_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyIsoSc'_hom_ι :
    (K.homologyIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyι =
      K.homologyι j ≫ (K.opcyclesIsoSc' i j k hi hk).hom := by
  apply ShortComplex.homologyι_naturality

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homologyIsoSc'_inv_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyIsoSc'_inv_ι :
    (K.homologyIsoSc' i j k hi hk).inv ≫ K.homologyι j =
      (K.sc' i j k).homologyι ≫ (K.opcyclesIsoSc' i j k hi hk).inv := by
  apply ShortComplex.homologyι_naturality

end HomologicalComplex

