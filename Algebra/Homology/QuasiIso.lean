/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

-/

@[expose] public section


open CategoryTheory Limits

universe v u

open HomologicalComplex

section

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

/-- A morphism of homological complexes `f : K ⟶ L` is a quasi-isomorphism in degree `i`
when it induces a quasi-isomorphism of short complexes `K.sc i ⟶ L.sc i`. -/
/-
**QuasiIsoAt** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, 
u} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {c :
 ComplexShape ι} →           {K L : HomologicalComplex C c} → (K ⟶ L) → (i : ι) 
→ [K.HasHomology i] → [L.HasHomology i] → Prop
参数：K ⟶ L；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of homological complexes `f : K ⟶ L` is a quasi-isomorphism in degree
 `i`
when it induces a quasi-isomorphism of short complexes `K.sc i ⟶ L.sc i`.
-/
class QuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : Prop where
  quasiIso : ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f)
/-
**quasiIsoAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : Q
uasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f)
参数：f : K ⟶ L；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiIsoAt.quasiIso`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
-/
lemma quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔
      ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f) := by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩
/-
**quasiIsoAt_of_isIso** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：quasiIsoAt_of_isIso (f : K ⟶ L) [IsIso f] (i : ι) [K.HasHomology i] [L.Has
Homology i] : QuasiIsoAt f i
参数：f : K ⟶ L；i : ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
-/
instance quasiIsoAt_of_isIso (f : K ⟶ L) [IsIso f] (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff]
  infer_instance
/-
**quasiIsoAt_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff' (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j
 = k) [K.HasHomology j] [L.HasHomology j] [(K.sc' i j k).HasHomology] [(L.sc' i 
j k).HasHomology] : QuasiIsoAt f j ↔ ShortComplex.QuasiIso ((shortComplexFunctor
' C c i j k).map f)
参数：f : K ⟶ L；i j k : ι；hi : c.prev j = i；hk : c.next j = k；K.sc' i j k；L.sc' i j
 k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_of_arrow_mk_iso`：quasiIso_iff_o
f_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ') : Qua
siIso φ ↔ QuasiIso φ'
-/
lemma quasiIsoAt_iff' (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j] [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    QuasiIsoAt f j ↔
      ShortComplex.QuasiIso ((shortComplexFunctor' C c i j k).map f) := by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (natIsoSc' C c i j k hi hk) (Arrow.mk f))
/-
**quasiIsoAt_of_retract** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'} (h : RetractArrow f f') (
i : ι) [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
 [hf' : QuasiIsoAt f' i] : QuasiIsoAt f i
参数：h : RetractArrow f f'；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_of_retract`：quasiIso_of_retract (h 
: RetractArrow f₁ f₂) [hf₂ : QuasiIso f₂] : QuasiIso f₁
-/
lemma quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') (i : ι) [K.HasHomology i] [L.HasHomology i]
    [K'.HasHomology i] [L'.HasHomology i] [hf' : QuasiIsoAt f' i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))
/-
**quasiIsoAt_iff_isIso_homologyMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff_isIso_homologyMap (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ IsIso (homologyMap f i)
参数：f : K ⟶ L；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIsoAt_iff_isIso_homologyMap (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔ IsIso (homologyMap f i) := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  rfl
/-
**quasiIsoAt_iff_exactAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomolog
y i] (hK : K.ExactAt i) : QuasiIsoAt f i ↔ L.ExactAt i
参数：f : K ⟶ L；i : ι；hK : K.ExactAt i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
lemma quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : K.ExactAt i) :
    QuasiIsoAt f i ↔ L.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩
/-
**quasiIsoAt_iff_exactAt'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomolo
gy i] (hL : L.ExactAt i) : QuasiIsoAt f i ↔ K.ExactAt i
参数：f : K ⟶ L；i : ι；hL : L.ExactAt i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
lemma quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hL : L.ExactAt i) :
    QuasiIsoAt f i ↔ K.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩
/-
**exactAt_iff_of_quasiIsoAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomo
logy i] [QuasiIsoAt f i] : K.ExactAt i ↔ L.ExactAt i
参数：f : K ⟶ L；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `quasiIsoAt_iff_exactAt`：quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.Ha
sHomology i] [L.HasHomology i] (hK : K.ExactAt i) : QuasiIsoAt f i ↔ L.ExactAt i
· 使用引理 `quasiIsoAt_iff_exactAt'`：quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.
HasHomology i] [L.HasHomology i] (hL : L.ExactAt i) : QuasiIsoAt f i ↔ K.ExactAt
 i
-/
lemma exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] :
    K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] [hf : QuasiIsoAt f i] :
    IsIso (homologyMap f i) := by
  simpa only [quasiIsoAt_iff, ShortComplex.quasiIso_iff] using! hf

/-- The isomorphism `K.homology i ≅ L.homology i` induced by a morphism `f : K ⟶ L` such
that `[QuasiIsoAt f i]` holds. -/
@[simps! hom]
/-
**isoOfQuasiIsoAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isoOfQuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] [Q
uasiIsoAt f i] : K.homology i ≅ L.homology i
参数：f : K ⟶ L；i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsIsoHomologyMapOfQuasiIsoAt`：∀ {ι : Type u_1} {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] {c : ComplexSh…

--- 原说明 ---
The isomorphism `K.homology i ≅ L.homology i` induced by a morphism `f : K ⟶ L` 
such
that `[QuasiIsoAt f i]` holds.
-/
noncomputable def isoOfQuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] : K.homology i ≅ L.homology i :=
  asIso (homologyMap f i)

@[reassoc (attr := simp)]
/-
**isoOfQuasiIsoAt_hom_inv_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isoOfQuasiIsoAt_hom_inv_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHom
ology i] [QuasiIsoAt f i] : homologyMap f i ≫ (isoOfQuasiIsoAt f i).inv = 𝟙 _
参数：f : K ⟶ L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma isoOfQuasiIsoAt_hom_inv_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    homologyMap f i ≫ (isoOfQuasiIsoAt f i).inv = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).hom_inv_id

@[reassoc (attr := simp)]
/-
**isoOfQuasiIsoAt_inv_hom_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isoOfQuasiIsoAt_inv_hom_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHom
ology i] [QuasiIsoAt f i] : (isoOfQuasiIsoAt f i).inv ≫ homologyMap f i = 𝟙 _
参数：f : K ⟶ L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma isoOfQuasiIsoAt_inv_hom_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    (isoOfQuasiIsoAt f i).inv ≫ homologyMap f i = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).inv_hom_id
/-
**CochainComplex.quasiIsoAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CochainComplex.quasiIsoAt₀_iff {K L : CochainComplex C ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 0 0 1).HasHomology] [(L.sc' 0 0 1).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 0 0 1).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)
/-
**ChainComplex.quasiIsoAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ChainComplex.quasiIsoAt₀_iff {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 1 0 0).HasHomology] [(L.sc' 1 0 0).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 1 0 0).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

/-- A morphism of homological complexes `f : K ⟶ L` is a quasi-isomorphism when it
is so in every degree, i.e. when the induced maps `homologyMap f i : K.homology i ⟶ L.homology i`
are all isomorphisms (see `quasiIso_iff` and `quasiIsoAt_iff_isIso_homologyMap`). -/
/-
**QuasiIso** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：QuasiIso (f : K ⟶ L) [forall i, K.HasHomology i] [forall i, L.HasHomology 
i] : Prop where quasiIsoAt : forall i, QuasiIsoAt f i
参数：f : K ⟶ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of homological complexes `f : K ⟶ L` is a quasi-isomorphism when it
is so in every degree, i.e. when the induced maps `homologyMap f i : K.homology 
i ⟶ L.homology i`
are all isomorphisms (see `quasiIso_iff` and `quasiIsoAt_iff_isIso_homologyMap`)
.
-/
class QuasiIso (f : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] : Prop where
  quasiIsoAt : ∀ i, QuasiIsoAt f i := by infer_instance
/-
**quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_iff (f : K ⟶ L) [forall i, K.HasHomology i] [forall i, L.HasHomol
ogy i] : QuasiIso f ↔ forall i, QuasiIsoAt f i
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
-/
lemma quasiIso_iff (f : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f ↔ ∀ i, QuasiIsoAt f i :=
  ⟨fun h => h.quasiIsoAt, fun h => ⟨h⟩⟩

attribute [instance] QuasiIso.quasiIsoAt
/-
**quasiIso_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   
[inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {c : ComplexShape ι} {K L : 
HomologicalComplex C c} (f : K ⟶ L)   [CategoryTheory.IsIso f] [inst_3 : ∀ (i : 
ι), K.HasHomology i] [inst_4 : ∀ (i : ι), L.HasHomology i], QuasiIso f
参数：f : K ⟶ L；i : ι；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance quasiIso_of_isIso (f : K ⟶ L) [IsIso f] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f where
/-
**quasiIsoAt_comp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：quasiIsoAt_comp (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i] [L.HasH
omology i] [M.HasHomology i] [hφ : QuasiIsoAt φ i] [hφ' : QuasiIsoAt φ' i] : Qua
siIsoAt (φ ≫ φ') i
参数：φ : K ⟶ L；φ' : L ⟶ M；i : ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
instance quasiIsoAt_comp (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφ' : QuasiIsoAt φ' i] :
    QuasiIsoAt (φ ≫ φ') i := by
  rw [quasiIsoAt_iff] at hφ hφ' ⊢
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _
/-
**quasiIso_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   
[inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {c : ComplexShape ι} {K L M 
: HomologicalComplex C c} (φ : K ⟶ L)   (φ' : L ⟶ M) [inst_2 : ∀ (i : ι), K.HasH
omology i] [inst_3 : ∀ (i : ι), L.HasHomology i]   [inst_4 : ∀ (i : ι), M.HasHom
ology i] [hφ : QuasiIso φ] [hφ' : QuasiIso φ'],   QuasiIso (CategoryTheory.Categ
oryStruct.comp φ φ')
参数：φ : K ⟶ L；φ' : L ⟶ M；i : ι；i : ι；i : ι；CategoryTheory.CategoryStruct.comp φ φ
'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
-/
instance quasiIso_comp (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') where
/-
**quasiIsoAt_of_comp_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
 [L.HasHomology i] [M.HasHomology i] [hφ : QuasiIsoAt φ i] [hφφ' : QuasiIsoAt (φ
 ≫ φ') i] : QuasiIsoAt φ' i
参数：φ : K ⟶ L；φ' : L ⟶ M；i : ι；φ ≫ φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff_isIso_homologyMap`：quasiIsoAt_iff_isIso_homologyMap (f : 
K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt f i ↔ IsIso (hom
ologyMap f i)
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用引理 `HomologicalComplex.homologyMap_comp`：homologyMap_comp : homologyMap (φ ≫
 ψ) i = homologyMap φ i ≫ homologyMap ψ i
-/
lemma quasiIsoAt_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ' i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ i) (homologyMap φ' i)
/-
**quasiIsoAt_iff_comp_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i
] [L.HasHomology i] [M.HasHomology i] [hφ : QuasiIsoAt φ i] : QuasiIsoAt (φ ≫ φ'
) i ↔ QuasiIsoAt φ' i
参数：φ : K ⟶ L；φ' : L ⟶ M；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `quasiIsoAt_of_comp_left`：quasiIsoAt_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M
) (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i] [hφ : QuasiIsoAt
 φ i] [hφφ' :…
-/
lemma quasiIsoAt_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ' i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_left φ φ' i
  · intro
    infer_instance
/-
**quasiIso_iff_comp_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i
] [forall i, L.HasHomology i] [forall i, M.HasHomology i] [hφ : QuasiIso φ] : Qu
asiIso (φ ≫ φ') ↔ QuasiIso φ'
参数：φ : K ⟶ L；φ' : L ⟶ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `quasiIsoAt_iff_comp_left`：quasiIsoAt_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶
 M) (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i] [hφ : QuasiIso
At φ i] : Quas…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quasiIso_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_left φ φ']
/-
**quasiIso_of_comp_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
 [forall i, L.HasHomology i] [forall i, M.HasHomology i] [hφ : QuasiIso φ] [hφφ'
 : QuasiIso (φ ≫ φ')] : QuasiIso φ'
参数：φ : K ⟶ L；φ' : L ⟶ M；φ ≫ φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasiIso_iff_comp_left`：quasiIso_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) 
[forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, M.HasHomology
 i] [hφ : Qu…
-/
lemma quasiIso_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' := by
  rw [← quasiIso_iff_comp_left φ φ']
  infer_instance
/-
**quasiIsoAt_of_comp_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i
] [L.HasHomology i] [M.HasHomology i] [hφ' : QuasiIsoAt φ' i] [hφφ' : QuasiIsoAt
 (φ ≫ φ') i] : QuasiIsoAt φ i
参数：φ : K ⟶ L；φ' : L ⟶ M；i : ι；φ ≫ φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff_isIso_homologyMap`：quasiIsoAt_iff_isIso_homologyMap (f : 
K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt f i ↔ IsIso (hom
ologyMap f i)
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_right`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) [CategoryTheory.I
sIso f]   [CategoryTheory.IsIs…
· 使用引理 `HomologicalComplex.homologyMap_comp`：homologyMap_comp : homologyMap (φ ≫
 ψ) i = homologyMap φ i ≫ homologyMap ψ i
-/
lemma quasiIsoAt_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ' : QuasiIsoAt φ' i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ i) (homologyMap φ' i)
/-
**quasiIsoAt_iff_comp_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIsoAt_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology 
i] [L.HasHomology i] [M.HasHomology i] [hφ' : QuasiIsoAt φ' i] : QuasiIsoAt (φ ≫
 φ') i ↔ QuasiIsoAt φ i
参数：φ : K ⟶ L；φ' : L ⟶ M；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `quasiIsoAt_of_comp_right`：quasiIsoAt_of_comp_right (φ : K ⟶ L) (φ' : L ⟶
 M) (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i] [hφ' : QuasiIs
oAt φ' i] [hφφ…
-/
lemma quasiIsoAt_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ' : QuasiIsoAt φ' i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_right φ φ' i
  · intro
    infer_instance
/-
**quasiIso_iff_comp_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology 
i] [forall i, L.HasHomology i] [forall i, M.HasHomology i] [hφ' : QuasiIso φ'] :
 QuasiIso (φ ≫ φ') ↔ QuasiIso φ
参数：φ : K ⟶ L；φ' : L ⟶ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `quasiIsoAt_iff_comp_right`：quasiIsoAt_iff_comp_right (φ : K ⟶ L) (φ' : L
 ⟶ M) (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i] [hφ' : Quasi
IsoAt φ' i] : Q…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_right φ φ']
/-
**quasiIso_of_comp_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i
] [forall i, L.HasHomology i] [forall i, M.HasHomology i] [hφ : QuasiIso φ'] [hφ
φ' : QuasiIso (φ ≫ φ')] : QuasiIso φ
参数：φ : K ⟶ L；φ' : L ⟶ M；φ ≫ φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasiIso_iff_comp_right`：quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M
) [forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, M.HasHomolo
gy i] [hφ' : …
-/
lemma quasiIso_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ := by
  rw [← quasiIso_iff_comp_right φ φ']
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**quasiIso_iff_of_arrow_mk_iso** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_iff_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ 
Arrow.mk φ') [forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, 
K'.HasHomology i] [forall i, L'.HasHomology i] : QuasiIso φ ↔ QuasiIso φ'
参数：φ : K ⟶ L；φ' : K' ⟶ L'；e : Arrow.mk φ ≅ Arrow.mk φ'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasiIso_iff_comp_left`：quasiIso_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) 
[forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, M.HasHomology
 i] [hφ : Qu…
· 使用定理 `quasiIso_of_isIso`：∀ {ι : Type u_1} {C : Type u} [inst : CategoryTheory.
Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {c : Co
mplexSh…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `QuasiIso.congr_simp`：∀ {ι : Type u_1} {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {c : 
ComplexSh…
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用引理 `quasiIso_iff_comp_right`：quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M
) [forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, M.HasHomolo
gy i] [hφ' : …
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quasiIso_iff_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i] :
    QuasiIso φ ↔ QuasiIso φ' := by
  simp [← quasiIso_iff_comp_left (show K' ⟶ K from e.inv.left) φ,
    ← quasiIso_iff_comp_right φ' (show L' ⟶ L from e.inv.right)]
/-
**quasiIso_of_arrow_mk_iso** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arro
w.mk φ') [forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, K'.H
asHomology i] [forall i, L'.HasHomology i] [hφ : QuasiIso φ] : QuasiIso φ'
参数：φ : K ⟶ L；φ' : K' ⟶ L'；e : Arrow.mk φ ≅ Arrow.mk φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasiIso_iff_of_arrow_mk_iso`：quasiIso_iff_of_arrow_mk_iso (φ : K ⟶ L) (
φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ') [forall i, K.HasHomology i] [forall
 i, L.HasHomology …
-/
lemma quasiIso_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i]
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  simpa only [← quasiIso_iff_of_arrow_mk_iso φ φ' e]
/-
**quasiIso_of_retractArrow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiIso_of_retractArrow {f : K ⟶ L} {f' : K' ⟶ L'} (h : RetractArrow f f'
) [forall i, K.HasHomology i] [forall i, L.HasHomology i] [forall i, K'.HasHomol
ogy i] [forall i, L'.HasHomology i] [QuasiIso f'] : QuasiIso f where quasiIsoAt 
i
参数：h : RetractArrow f f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `quasiIsoAt_of_retract`：quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'} 
(h : RetractArrow f f') (i : ι) [K.HasHomology i] [L.HasHomology i] [K'.HasHomol
ogy i] [L'.…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
-/
lemma quasiIso_of_retractArrow {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i] [QuasiIso f'] :
    QuasiIso f where
  quasiIsoAt i := quasiIsoAt_of_retract h i

namespace HomologicalComplex

section PreservesHomology

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Preadditive C₁] [Preadditive C₂]
  {K L : HomologicalComplex C₁ c} (φ : K ⟶ L) (F : C₁ ⥤ C₂) [F.Additive]
  [F.PreservesHomology]

section

variable (i : ι) [K.HasHomology i] [L.HasHomology i]
  [((F.mapHomologicalComplex c).obj K).HasHomology i]
  [((F.mapHomologicalComplex c).obj L).HasHomology i]

/-
**HomologicalComplex.quasiIsoAt_map_of_preservesHomology** 是 Mathlib 中的一个实例，位于命名
空间 `HomologicalComplex`。
形式化陈述：quasiIsoAt_map_of_preservesHomology [hφ : QuasiIsoAt φ i] : QuasiIsoAt ((F
.mapHomologicalComplex c).map φ) i
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance quasiIsoAt_map_of_preservesHomology [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i := by
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)
/-
**HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology** 是 Mathlib 中的一个引理，
位于命名空间 `HomologicalComplex`。
形式化陈述：quasiIsoAt_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] : QuasiIs
oAt ((F.mapHomologicalComplex c).map φ) i ↔ QuasiIsoAt φ i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_map_iff_of_preservesLeftHomology`：q
uasiIso_map_iff_of_preservesLeftHomology [F.PreservesLeftHomologyOf S₁] [F.Prese
rvesLeftHomologyOf S₂] [F.ReflectsIsomorphisms] : QuasiIso …
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma quasiIsoAt_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_iff_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

end

section

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
  [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i]
  [∀ i, ((F.mapHomologicalComplex c).obj L).HasHomology i]

/-
**HomologicalComplex.quasiIso_map_of_preservesHomology** 是 Mathlib 中的一个定理，位于命名空间
 `HomologicalComplex`。
形式化陈述：∀ {ι : Type u_1} {c : ComplexShape ι} {C₁ : Type u_2} {C₂ : Type u_3} [ins
t : CategoryTheory.Category.{v_1, u_2} C₁]   [inst_1 : CategoryTheory.Category.{
v_2, u_3} C₂] [inst_2 : CategoryTheory.Preadditive C₁]   [inst_3 : CategoryTheor
y.Preadditive C₂] {K L : HomologicalComplex C₁ c} (φ : K ⟶ L)   (F : CategoryThe
ory.Functor C₁ C₂) [inst_4 : F.Additive] [F.PreservesHomology] [inst_6 : ∀ (i : 
ι), K.HasHomology i]   [inst_7 : ∀ (i : ι), L.HasHomology i] [inst_8 : ∀ (i : ι)
, ((F.mapHomologicalComplex c).obj K).HasHomology i]   [inst_9 : ∀ (i : ι), ((F.
mapHomologicalComplex c).obj L).HasHomology i] [hφ : QuasiIso φ],   QuasiIso ((F
.mapHomologicalComplex c).map φ)
参数：φ : K ⟶ L；F : CategoryTheory.Functor C₁ C₂；i : ι；i : ι；i : ι；(F.mapHomologica
lComplex c).obj K；i : ι；(F.mapHomologicalComplex c).obj L；(F.mapHomologicalCompl
ex c).map φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
-/
instance quasiIso_map_of_preservesHomology [hφ : QuasiIso φ] :
    QuasiIso ((F.mapHomologicalComplex c).map φ) where
/-
**HomologicalComplex.quasiIso_map_iff_of_preservesHomology** 是 Mathlib 中的一个引理，位于
命名空间 `HomologicalComplex`。
形式化陈述：quasiIso_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] : QuasiIso 
((F.mapHomologicalComplex c).map φ) ↔ QuasiIso φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology`：quasiIsoAt_m
ap_iff_of_preservesHomology [F.ReflectsIsomorphisms] : QuasiIsoAt ((F.mapHomolog
icalComplex c).map φ) i ↔ QuasiIsoAt φ i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quasiIso_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIso ((F.mapHomologicalComplex c).map φ) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_map_iff_of_preservesHomology φ F]

end

end PreservesHomology

variable (C c)

/-- The morphism property on `HomologicalComplex C c` given by quasi-isomorphisms. -/
/-
**HomologicalComplex.quasiIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：quasiIso [CategoryWithHomology C] : MorphismProperty (HomologicalComplex C
 c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property on `HomologicalComplex C c` given by quasi-isomorphisms.
-/
def quasiIso [CategoryWithHomology C] :
    MorphismProperty (HomologicalComplex C c) := fun _ _ f => QuasiIso f

variable {C c} [CategoryWithHomology C]

@[simp]
/-
**HomologicalComplex.mem_quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：mem_quasiIso_iff (f : K ⟶ L) : quasiIso C c f ↔ QuasiIso f
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_quasiIso_iff (f : K ⟶ L) : quasiIso C c f ↔ QuasiIso f := by rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso C c).IsMultiplicative where
  id_mem _ := by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem _ _ hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    infer_instance
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso C c).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    rw [mem_quasiIso_iff] at hg hfg ⊢
    rwa [← quasiIso_iff_comp_right f g]
  of_precomp f g hf hfg := by
    rw [mem_quasiIso_iff] at hf hfg ⊢
    rwa [← quasiIso_iff_comp_left f g]
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso C c).IsStableUnderRetracts where
  of_retract h hg := by
    rw [mem_quasiIso_iff] at hg ⊢
    exact quasiIso_of_retractArrow h
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso C c).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ (_ : IsIso _) ↦ by rw [mem_quasiIso_iff]; infer_instance)

end HomologicalComplex

end

namespace HomotopyEquiv

variable {ι : Type*} {C : Type u} [Category.{v} C] [Preadditive C]
  {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (e : HomotopyEquiv K L)

/-
**HomotopyEquiv.quasiIsoAt_hom** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyEquiv`。
形式化陈述：quasiIsoAt_hom (n : ι) [K.HasHomology n] [L.HasHomology n] : QuasiIsoAt e.
hom n
参数：n : ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff`：quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.
HasHomology i] : QuasiIsoAt f i ↔ ShortComplex.QuasiIso ((shortComplexFunctor C 
c i)…
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance quasiIsoAt_hom (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.hom n := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  exact (e.toHomologyIso n).isIso_hom
/-
**HomotopyEquiv.quasiIsoAt_inv** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyEquiv`。
形式化陈述：quasiIsoAt_inv (n : ι) [K.HasHomology n] [L.HasHomology n] : QuasiIsoAt e.
inv n
参数：n : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance quasiIsoAt_inv (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.inv n :=
  e.symm.quasiIsoAt_hom n
/-
**HomotopyEquiv.quasiIso_hom** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyEquiv`。
形式化陈述：quasiIso_hom [forall n, K.HasHomology n] [forall n, L.HasHomology n] : Qua
siIso e.hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance quasiIso_hom [∀ n, K.HasHomology n] [∀ n, L.HasHomology n] :
    QuasiIso e.hom :=
  ⟨fun _ => inferInstance⟩
/-
**HomotopyEquiv.quasiIso_inv** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyEquiv`。
形式化陈述：quasiIso_inv [forall n, K.HasHomology n] [forall n, L.HasHomology n] : Qua
siIso e.inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance quasiIso_inv [∀ n, K.HasHomology n] [∀ n, L.HasHomology n] :
    QuasiIso e.inv :=
  ⟨fun _ => inferInstance⟩

end HomotopyEquiv

/-
**homotopyEquivalences_le_quasiIso** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：homotopyEquivalences_le_quasiIso {ι : Type*} (C : Type u) [Category.{v} C]
 [Preadditive C] (c : ComplexShape ι) [CategoryWithHomology C] : homotopyEquival
ences C c <= quasiIso C c
参数：C : Type u；c : ComplexShape ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
-/
lemma homotopyEquivalences_le_quasiIso
    {ι : Type*} (C : Type u) [Category.{v} C] [Preadditive C]
    (c : ComplexShape ι) [CategoryWithHomology C] :
    homotopyEquivalences C c ≤ quasiIso C c := by
  rintro K L _ ⟨e, rfl⟩
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance
