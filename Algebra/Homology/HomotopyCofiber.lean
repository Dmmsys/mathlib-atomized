/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-! # The homotopy cofiber of a morphism of homological complexes

In this file, we construct the homotopy cofiber of a morphism `φ : F ⟶ G`
between homological complexes in `HomologicalComplex C c`. In degree `i`,
it is isomorphic to `(F.X j) ⊞ (G.X i)` if there is a `j` such that `c.Rel i j`,
and `G.X i` otherwise. (This is also known as the mapping cone of `φ`. Under
the name `CochainComplex.mappingCone`, a specific API shall be developed
for the case of cochain complexes indexed by `ℤ`.)

When we assume `hc : ∀ j, ∃ i, c.Rel i j` (which holds in the case of chain complexes,
or cochain complexes indexed by `ℤ`), then for any homological complex `K`,
there is a bijection `HomologicalComplex.homotopyCofiber.descEquiv φ K hc`
between `homotopyCofiber φ ⟶ K` and the tuples `(α, hα)` with
`α : G ⟶ K` and `hα : Homotopy (φ ≫ α) 0`.

We shall also study the cylinder of a homological complex `K`: this is the
homotopy cofiber of the morphism  `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`.
Then, a morphism `K.cylinder ⟶ M` is determined by the data of two
morphisms `φ₀ φ₁ : K ⟶ M` and a homotopy `h : Homotopy φ₀ φ₁`,
see `cylinder.desc`. There is also a homotopy equivalence
`cylinder.homotopyEquiv K : HomotopyEquiv K.cylinder K`. From the construction of
the cylinder, we deduce the lemma `Homotopy.map_eq_of_inverts_homotopyEquivalences`
which asserts that if a functor inverts homotopy equivalences, then the images of
two homotopic maps are equal.

-/

@[expose] public section


open CategoryTheory Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

/-- A morphism of homological complexes `φ : F ⟶ G` has a homotopy cofiber if for all
indices `i` and `j` such that `c.Rel i j`, the binary biproduct `F.X j ⊞ G.X i` exists. -/
/-
**HomologicalComplex.HasHomotopyCofiber** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homological
Complex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {ι : Type u_2} → {c : ComplexShape 
ι} → {F G : HomologicalComplex C c} → (F ⟶ G) → Prop
参数：F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of homological complexes `φ : F ⟶ G` has a homotopy cofiber if for al
l
indices `i` and `j` such that `c.Rel i j`, the binary biproduct `F.X j ⊞ G.X i` 
exists.
-/
class HasHomotopyCofiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (i j : ι) (hij : c.Rel i j) : HasBinaryBiproduct (F.X j) (G.X i)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryBiproducts C] : HasHomotopyCofiber φ where
  hasBinaryBiproduct _ _ _ := inferInstance

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

namespace homotopyCofiber

/-- The `X` field of the homological complex `homotopyCofiber φ`. -/
/-
**HomologicalComplex.homotopyCofiber.X** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex.homotopyCofiber`。
形式化陈述：X (i : ι) : C
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `X` field of the homological complex `homotopyCofiber φ`.
-/
noncomputable def X (i : ι) : C :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (F.X (c.next i)) ⊞ (G.X i)
  else G.X i

/-- The canonical isomorphism `(homotopyCofiber φ).X i ≅ F.X j ⊞ G.X i` when `c.Rel i j`. -/
/-
**HomologicalComplex.homotopyCofiber.XIsoBiprod** 是 Mathlib 中的一个定义，位于命名空间 `Homol
ogicalComplex.homotopyCofiber`。
形式化陈述：XIsoBiprod (i j : ι) (hij : c.Rel i j) [HasBinaryBiproduct (F.X j) (G.X i)
] : X φ i ≅ F.X j ⊞ G.X i
参数：i j : ι；hij : c.Rel i j；F.X j；G.X i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(homotopyCofiber φ).X i ≅ F.X j ⊞ G.X i` when `c.Rel 
i j`.
-/
noncomputable def XIsoBiprod (i j : ι) (hij : c.Rel i j) [HasBinaryBiproduct (F.X j) (G.X i)] :
    X φ i ≅ F.X j ⊞ G.X i :=
  eqToIso (by
    obtain rfl := c.next_eq' hij
    apply dif_pos hij)

/-- The canonical isomorphism `(homotopyCofiber φ).X i ≅ G.X i` when `¬ c.Rel i (c.next i)`. -/
/-
**HomologicalComplex.homotopyCofiber.XIso** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.homotopyCofiber`。
形式化陈述：XIso (i : ι) (hi : ¬ c.Rel i (c.next i)) : X φ i ≅ G.X i
参数：i : ι；hi : ¬ c.Rel i (c.next i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(homotopyCofiber φ).X i ≅ G.X i` when `¬ c.Rel i (c.n
ext i)`.
-/
noncomputable def XIso (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    X φ i ≅ G.X i :=
  eqToIso (dif_neg hi)
/-
**HomologicalComplex.homotopyCofiber.isZero_X** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex.homotopyCofiber`。
形式化陈述：isZero_X (i : ι) (hG : IsZero (G.X i)) (hF : forall (j : ι), c.Rel i j -> 
IsZero (F.X j)) : IsZero (X φ i)
参数：i : ι；hG : IsZero (G.X i)；hF : forall (j : ι), c.Rel i j -> IsZero (F.X j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
lemma isZero_X (i : ι) (hG : IsZero (G.X i))
    (hF : ∀ (j : ι), c.Rel i j → IsZero (F.X j)) :
    IsZero (X φ i) := by
  by_cases h : c.Rel i (c.next i)
  · have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ h
    refine IsZero.of_iso ?_ (XIsoBiprod φ _ _ h)
    simp only [biprod_isZero_iff]
    exact ⟨hF _ h, hG⟩
  · exact hG.of_iso (XIso φ i h)

/-- The second projection `(homotopyCofiber φ).X i ⟶ G.X i`. -/
/-
**HomologicalComplex.homotopyCofiber.sndX** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.homotopyCofiber`。
形式化陈述：sndX (i : ι) : X φ i ⟶ G.X i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection `(homotopyCofiber φ).X i ⟶ G.X i`.
-/
noncomputable def sndX (i : ι) : X φ i ⟶ G.X i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (XIsoBiprod φ _ _ hi).hom ≫ biprod.snd
  else
    (XIso φ i hi).hom

/-- The right inclusion `G.X i ⟶ (homotopyCofiber φ).X i`. -/
/-
**HomologicalComplex.homotopyCofiber.inrX** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.homotopyCofiber`。
形式化陈述：inrX (i : ι) : G.X i ⟶ X φ i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion `G.X i ⟶ (homotopyCofiber φ).X i`.
-/
noncomputable def inrX (i : ι) : G.X i ⟶ X φ i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    biprod.inr ≫ (XIsoBiprod φ _ _ hi).inv
  else
    (XIso φ i hi).inv

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrX_sndX** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：inrX_sndX (i : ι) : inrX φ i ≫ sndX φ i = 𝟙 _
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma inrX_sndX (i : ι) : inrX φ i ≫ sndX φ i = 𝟙 _ := by
  dsimp [sndX, inrX]
  split_ifs with hi <;> simp

@[reassoc]
/-
**HomologicalComplex.homotopyCofiber.sndX_inrX** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：sndX_inrX (i : ι) (hi : ¬ c.Rel i (c.next i)) : sndX φ i ≫ inrX φ i = 𝟙 _
参数：i : ι；hi : ¬ c.Rel i (c.next i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sndX_inrX (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    sndX φ i ≫ inrX φ i = 𝟙 _ := by
  dsimp [sndX, inrX]
  simp only [dif_neg hi, Iso.hom_inv_id]

/-- The first projection `(homotopyCofiber φ).X i ⟶ F.X j` when `c.Rel i j`. -/
/-
**HomologicalComplex.homotopyCofiber.fstX** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.homotopyCofiber`。
形式化陈述：fstX (i j : ι) (hij : c.Rel i j) : X φ i ⟶ F.X j
参数：i j : ι；hij : c.Rel i j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…

--- 原说明 ---
The first projection `(homotopyCofiber φ).X i ⟶ F.X j` when `c.Rel i j`.
-/
noncomputable def fstX (i j : ι) (hij : c.Rel i j) : X φ i ⟶ F.X j :=
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  (XIsoBiprod φ i j hij).hom ≫ biprod.fst

/-- The left inclusion `F.X i ⟶ (homotopyCofiber φ).X j` when `c.Rel j i`. -/
/-
**HomologicalComplex.homotopyCofiber.inlX** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.homotopyCofiber`。
形式化陈述：inlX (i j : ι) (hij : c.Rel j i) : F.X i ⟶ X φ j
参数：i j : ι；hij : c.Rel j i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…

--- 原说明 ---
The left inclusion `F.X i ⟶ (homotopyCofiber φ).X j` when `c.Rel j i`.
-/
noncomputable def inlX (i j : ι) (hij : c.Rel j i) : F.X i ⟶ X φ j :=
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  biprod.inl ≫ (XIsoBiprod φ j i hij).inv

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inlX_fstX** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：inlX_fstX (i j : ι) (hij : c.Rel j i) : inlX φ i j hij ≫ fstX φ j i hij = 
𝟙 _
参数：i j : ι；hij : c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inlX_fstX (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _ := by
  simp [inlX, fstX]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inlX_sndX** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：inlX_sndX (i j : ι) (hij : c.Rel j i) : inlX φ i j hij ≫ sndX φ j = 0
参数：i j : ι；hij : c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma inlX_sndX (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ sndX φ j = 0 := by
  obtain rfl := c.next_eq' hij
  simp [inlX, sndX, dif_pos hij]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrX_fstX** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：inrX_fstX (i j : ι) (hij : c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
参数：i j : ι；hij : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma inrX_fstX (i j : ι) (hij : c.Rel i j) :
    inrX φ i ≫ fstX φ i j hij = 0 := by
  obtain rfl := c.next_eq' hij
  simp [inrX, fstX, dif_pos hij]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inlX_XIsoBiprod_hom (i j : ι) (hij : c.Rel j i) : haveI
参数：i j : ι；hij : c.Rel j i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inlX_XIsoBiprod_hom (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inlX φ i j hij ≫ (XIsoBiprod φ j i hij).hom = biprod.inl := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inlX]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inl_XIsoBiprod_inv (i j : ι) (hij : c.Rel j i) : haveI
参数：i j : ι；hij : c.Rel j i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_XIsoBiprod_inv (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inl ≫ (XIsoBiprod φ j i hij).inv = inlX φ i j hij := by
  simp [inlX]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inrX_XIsoBiprod_hom (i j : ι) (hij : c.Rel j i) : haveI
参数：i j : ι；hij : c.Rel j i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma inrX_XIsoBiprod_hom (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inrX φ j ≫ (XIsoBiprod φ j i hij).hom = biprod.inr := by
  obtain rfl := c.next_eq' hij
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inrX, XIsoBiprod, dif_pos hij]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inr_XIsoBiprod_inv (i j : ι) (hij : c.Rel j i) : haveI
参数：i j : ι；hij : c.Rel j i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom`：inrX_XIsoBiprod_
hom (i j : ι) (hij : c.Rel j i) : haveI
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma inr_XIsoBiprod_inv (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inr ≫ (XIsoBiprod φ j i hij).inv = inrX φ j := by
  rw [← inrX_XIsoBiprod_hom φ i j hij, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The `d` field of the homological complex `homotopyCofiber φ`. -/
/-
**HomologicalComplex.homotopyCofiber.d** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex.homotopyCofiber`。
形式化陈述：d (i j : ι) : X φ i ⟶ X φ j
参数：i j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `d` field of the homological complex `homotopyCofiber φ`.
-/
noncomputable def d (i j : ι) : X φ i ⟶ X φ j :=
  if hij : c.Rel i j
  then
    (if hj : c.Rel j (c.next j) then -fstX φ i j hij ≫ F.d _ _ ≫ inlX φ _ _ hj else 0) +
      fstX φ i j hij ≫ φ.f j ≫ inrX φ j + sndX φ i ≫ G.d i j ≫ inrX φ j
  else
    0
/-
**HomologicalComplex.homotopyCofiber.ext_to_X** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex.homotopyCofiber`。
形式化陈述：ext_to_X (i j : ι) (hij : c.Rel i j) {A : C} {f g : A ⟶ X φ i} (h₁ : f ≫ f
stX φ i j hij = g ≫ fstX φ i j hij) (h₂ : f ≫ sndX φ i = g ≫ sndX φ i) : f = g
参数：i j : ι；hij : c.Rel i j；h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hij；h₂ : f ≫
 sndX φ i = g ≫ sndX φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
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
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma ext_to_X (i j : ι) (hij : c.Rel i j) {A : C} {f g : A ⟶ X φ i}
    (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hij) (h₂ : f ≫ sndX φ i = g ≫ sndX φ i) :
    f = g := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_mono (XIsoBiprod φ i j hij).hom]
  apply biprod.hom_ext
  · simpa using! h₁
  · obtain rfl := c.next_eq' hij
    simpa [sndX, dif_pos hij] using! h₂
/-
**HomologicalComplex.homotopyCofiber.ext_to_X'** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：ext_to_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i} (h
 : f ≫ sndX φ i = g ≫ sndX φ i) : f = g
参数：i : ι；hi : ¬ c.Rel i (c.next i)；h : f ≫ sndX φ i = g ≫ sndX φ i。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma ext_to_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i}
    (h : f ≫ sndX φ i = g ≫ sndX φ i) : f = g := by
  rw [← cancel_mono (XIso φ i hi).hom]
  simpa only [sndX, dif_neg hi] using h
/-
**HomologicalComplex.homotopyCofiber.ext_from_X** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex.homotopyCofiber`。
形式化陈述：ext_from_X (i j : ι) (hij : c.Rel j i) {A : C} {f g : X φ j ⟶ A} (h₁ : inl
X φ i j hij ≫ f = inlX φ i j hij ≫ g) (h₂ : inrX φ j ≫ f = inrX φ j ≫ g) : f = g
参数：i j : ι；hij : c.Rel j i；h₁ : inlX φ i j hij ≫ f = inlX φ i j hij ≫ g；h₂ : inr
X φ j ≫ f = inrX φ j ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
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
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pre
additive C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma ext_from_X (i j : ι) (hij : c.Rel j i) {A : C} {f g : X φ j ⟶ A}
    (h₁ : inlX φ i j hij ≫ f = inlX φ i j hij ≫ g) (h₂ : inrX φ j ≫ f = inrX φ j ≫ g) :
    f = g := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_epi (XIsoBiprod φ j i hij).inv]
  apply biprod.hom_ext'
  · simpa
  · obtain rfl := c.next_eq' hij
    simpa [-inr_XIsoBiprod_inv, -inr_XIsoBiprod_inv_assoc, inrX, dif_pos hij] using h₂
/-
**HomologicalComplex.homotopyCofiber.ext_from_X'** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex.homotopyCofiber`。
形式化陈述：ext_from_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A} 
(h : inrX φ i ≫ f = inrX φ i ≫ g) : f = g
参数：i : ι；hi : ¬ c.Rel i (c.next i)；h : inrX φ i ≫ f = inrX φ i ≫ g。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma ext_from_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A}
    (h : inrX φ i ≫ f = inrX φ i ≫ g) : f = g := by
  rw [← cancel_epi (XIso φ i hi).inv]
  simpa only [inrX, dif_neg hi] using h

@[reassoc]
/-
**HomologicalComplex.homotopyCofiber.d_fstX** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.homotopyCofiber`。
形式化陈述：d_fstX (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) : d φ i j ≫ fstX φ 
j k hjk = -fstX φ i j hij ≫ F.d j k
参数：i j k : ι；hij : c.Rel i j；hjk : c.Rel j k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_fstX`：inlX_fstX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_fstX`：inrX_fstX (i j : ι) (hij :
 c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma d_fstX (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    d φ i j ≫ fstX φ j k hjk = -fstX φ i j hij ≫ F.d j k := by
  obtain rfl := c.next_eq' hjk
  simp [d, dif_pos hij, dif_pos hjk]

@[reassoc]
/-
**HomologicalComplex.homotopyCofiber.d_sndX** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.homotopyCofiber`。
形式化陈述：d_sndX (i j : ι) (hij : c.Rel i j) : d φ i j ≫ sndX φ j = fstX φ i j hij ≫
 φ.f j + sndX φ i ≫ G.d i j
参数：i j : ι；hij : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_sndX`：inlX_sndX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ sndX φ j = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma d_sndX (i j : ι) (hij : c.Rel i j) :
    d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j := by
  dsimp [d]
  split_ifs with hij <;> simp

@[reassoc]
/-
**HomologicalComplex.homotopyCofiber.inlX_d** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.homotopyCofiber`。
形式化陈述：inlX_d (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) : inlX φ j i hij ≫ 
d φ i j = -F.d j k ≫ inlX φ k j hjk + φ.f j ≫ inrX φ j
参数：i j k : ι；hij : c.Rel i j；hjk : c.Rel j k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X`：ext_to_X (i j : ι) (hij : c
.Rel i j) {A : C} {f g : A ⟶ X φ i} (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hi
j) (h₂ : f ≫ sndX φ i = g ≫ sndX …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.d_fstX`：d_fstX (i j k : ι) (hij : c.R
el i j) (hjk : c.Rel j k) : d φ i j ≫ fstX φ j k hjk = -fstX φ i j hij ≫ F.d j k
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_fstX`：inlX_fstX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_fstX`：inrX_fstX (i j : ι) (hij :
 c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.homotopyCofiber.d_sndX`：d_sndX (i j : ι) (hij : c.Rel
 i j) : d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_sndX`：inlX_sndX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ sndX φ j = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma inlX_d (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    inlX φ j i hij ≫ d φ i j = -F.d j k ≫ inlX φ k j hjk + φ.f j ≫ inrX φ j := by
  apply ext_to_X φ j k hjk
  · simp [d_fstX φ _ _ _ hij hjk]
  · simp [d_sndX φ _ _ hij]

@[reassoc]
/-
**HomologicalComplex.homotopyCofiber.inlX_d'** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex.homotopyCofiber`。
形式化陈述：inlX_d' (i j : ι) (hij : c.Rel i j) (hj : ¬ c.Rel j (c.next j)) : inlX φ j
 i hij ≫ d φ i j = φ.f j ≫ inrX φ j
参数：i j : ι；hij : c.Rel i j；hj : ¬ c.Rel j (c.next j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X'`：ext_to_X' (i : ι) (hi : ¬ 
c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i} (h : f ≫ sndX φ i = g ≫ sndX φ i) 
: f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.d_sndX`：d_sndX (i j : ι) (hij : c.Rel
 i j) : d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inlX_d' (i j : ι) (hij : c.Rel i j) (hj : ¬ c.Rel j (c.next j)) :
    inlX φ j i hij ≫ d φ i j = φ.f j ≫ inrX φ j := by
  apply ext_to_X' _ _ hj
  simp [d_sndX φ i j hij]
/-
**HomologicalComplex.homotopyCofiber.shape** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex.homotopyCofiber`。
形式化陈述：shape (i j : ι) (hij : ¬ c.Rel i j) : d φ i j = 0
参数：i j : ι；hij : ¬ c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma shape (i j : ι) (hij : ¬ c.Rel i j) :
    d φ i j = 0 :=
  dif_neg hij

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrX_d** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.homotopyCofiber`。
形式化陈述：inrX_d (i j : ι) : inrX φ i ≫ d φ i j = G.d i j ≫ inrX φ j
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X`：ext_to_X (i j : ι) (hij : c
.Rel i j) {A : C} {f g : A ⟶ X φ i} (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hi
j) (h₂ : f ≫ sndX φ i = g ≫ sndX …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.d_fstX`：d_fstX (i j k : ι) (hij : c.R
el i j) (hjk : c.Rel j k) : d φ i j ≫ fstX φ j k hjk = -fstX φ i j hij ≫ F.d j k
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_fstX`：inrX_fstX (i j : ι) (hij :
 c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.homotopyCofiber.d_sndX`：d_sndX (i j : ι) (hij : c.Rel
 i j) : d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X'`：ext_to_X' (i : ι) (hi : ¬ 
c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i} (h : f ≫ sndX φ i = g ≫ sndX φ i) 
: f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.shape`：shape (i j : ι) (hij : ¬ c.Rel
 i j) : d φ i j = 0
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
-/
lemma inrX_d (i j : ι) :
    inrX φ i ≫ d φ i j = G.d i j ≫ inrX φ j := by
  by_cases hij : c.Rel i j
  · by_cases hj : c.Rel j (c.next j)
    · apply ext_to_X _ _ _ hj
      · simp [d_fstX φ _ _ _ hij]
      · simp [d_sndX φ _ _ hij]
    · apply ext_to_X' _ _ hj
      simp [d_sndX φ _ _ hij]
  · rw [shape φ _ _ hij, G.shape _ _ hij, zero_comp, comp_zero]

end homotopyCofiber

/-- The homotopy cofiber of a morphism of homological complexes,
also known as the mapping cone. -/
@[simps, implicit_reducible]
/-
**HomologicalComplex.homotopyCofiber** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：homotopyCofiber : HomologicalComplex C c where X i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homotopyCofiber.shape`：shape (i j : ι) (hij : ¬ c.Rel
 i j) : d φ i j = 0

--- 原说明 ---
The homotopy cofiber of a morphism of homological complexes,
also known as the mapping cone.
-/
noncomputable def homotopyCofiber : HomologicalComplex C c where
  X i := homotopyCofiber.X φ i
  d i j := homotopyCofiber.d φ i j
  shape i j hij := homotopyCofiber.shape φ i j hij
  d_comp_d' i j k hij hjk := by
    apply homotopyCofiber.ext_from_X φ j i hij
    · simp only [comp_zero, homotopyCofiber.inlX_d_assoc φ i j k hij hjk,
        add_comp, assoc, homotopyCofiber.inrX_d, Hom.comm_assoc, neg_comp]
      by_cases hk : c.Rel k (c.next k)
      · simp [homotopyCofiber.inlX_d φ j k _ hjk hk]
      · simp [homotopyCofiber.inlX_d' φ j k hjk hk]
    · simp

namespace homotopyCofiber

set_option backward.defeqAttrib.useBackward true in
/-- The right inclusion `G ⟶ homotopyCofiber φ`. -/
@[simps!]
/-
**HomologicalComplex.homotopyCofiber.inr** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex.homotopyCofiber`。
形式化陈述：inr : G ⟶ homotopyCofiber φ where f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion `G ⟶ homotopyCofiber φ`.
-/
noncomputable def inr : G ⟶ homotopyCofiber φ where
  f i := inrX φ i

section

set_option backward.isDefEq.respectTransparency false in
/-- The composition `φ ≫ mappingCone.inr φ` is homotopic to `0`. -/
/-
**HomologicalComplex.homotopyCofiber.inrCompHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `
HomologicalComplex.homotopyCofiber`。
形式化陈述：inrCompHomotopy (hc : forall j, exists i, c.Rel i j) : Homotopy (φ ≫ inr φ
) 0 where hom i j
参数：hc : forall j, exists i, c.Rel i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition `φ ≫ mappingCone.inr φ` is homotopic to `0`.
-/
noncomputable def inrCompHomotopy (hc : ∀ j, ∃ i, c.Rel i j) :
    Homotopy (φ ≫ inr φ) 0 where
  hom i j :=
    if hij : c.Rel j i then inlX φ i j hij else 0
  zero _ _ hij := dif_neg hij
  comm j := by
    obtain ⟨i, hij⟩ := hc j
    rw [prevD_eq _ hij, dif_pos hij]
    by_cases hj : c.Rel j (c.next j)
    · simp only [comp_f, homotopyCofiber_d, zero_f, add_zero,
        inlX_d φ i j _ hij hj, dNext_eq _ hj, dif_pos hj,
        add_neg_cancel_left, inr_f]
    · rw [dNext_eq_zero _ _ hj, zero_add, zero_f, add_zero, homotopyCofiber_d,
        inlX_d' _ _ _ _ hj, comp_f, inr_f]

variable (hc : ∀ j, ∃ i, c.Rel i j)
/-
**HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inrCompHomotopy_hom (i j : ι) (hij : c.Rel j i) : (inrCompHomotopy φ hc).h
om i j = inlX φ i j hij
参数：i j : ι；hij : c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma inrCompHomotopy_hom (i j : ι) (hij : c.Rel j i) :
    (inrCompHomotopy φ hc).hom i j = inlX φ i j hij := dif_pos hij
/-
**HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom_eq_zero** 是 Mathlib 中的一
个引理，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inrCompHomotopy_hom_eq_zero (i j : ι) (hij : ¬ c.Rel j i) : (inrCompHomoto
py φ hc).hom i j = 0
参数：i j : ι；hij : ¬ c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma inrCompHomotopy_hom_eq_zero (i j : ι) (hij : ¬ c.Rel j i) :
    (inrCompHomotopy φ hc).hom i j = 0 := dif_neg hij

end

section

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `homotopyCofiber φ ⟶ K` that is induced by a morphism `α : G ⟶ K`
and a homotopy `hα : Homotopy (φ ≫ α) 0`. -/
/-
**HomologicalComplex.homotopyCofiber.desc** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex.homotopyCofiber`。
形式化陈述：desc : homotopyCofiber φ ⟶ K where f j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `homotopyCofiber φ ⟶ K` that is induced by a morphism `α : G ⟶ K`
and a homotopy `hα : Homotopy (φ ≫ α) 0`.
-/
noncomputable def desc :
    homotopyCofiber φ ⟶ K where
  f j :=
    if hj : c.Rel j (c.next j)
    then fstX φ j _ hj ≫ hα.hom _ j + sndX φ j ≫ α.f j
    else sndX φ j ≫ α.f j
  comm' j k hjk := by
    obtain rfl := c.next_eq' hjk
    simp [dif_pos hjk]
    have H := hα.comm (c.next j)
    simp only [comp_f, zero_f, add_zero, prevD_eq _ hjk] at H
    split_ifs with hj
    · simp only [comp_add, d_sndX_assoc _ _ _ hjk, add_comp, assoc, H,
        d_fstX_assoc _ _ _ _ hjk, neg_comp, dNext, AddMonoidHom.mk'_apply]
      abel
    · simp only [d_sndX_assoc _ _ _ hjk, add_comp, assoc, H, dNext_eq_zero _ _ hj, zero_add]
/-
**HomologicalComplex.homotopyCofiber.desc_f** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.homotopyCofiber`。
形式化陈述：desc_f (j k : ι) (hjk : c.Rel j k) : (desc φ α hα).f j = fstX φ j _ hjk ≫ 
hα.hom _ j + sndX φ j ≫ α.f j
参数：j k : ι；hjk : c.Rel j k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma desc_f (j k : ι) (hjk : c.Rel j k) :
    (desc φ α hα).f j = fstX φ j _ hjk ≫ hα.hom _ j + sndX φ j ≫ α.f j := by
  obtain rfl := c.next_eq' hjk
  apply dif_pos hjk
/-
**HomologicalComplex.homotopyCofiber.desc_f'** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex.homotopyCofiber`。
形式化陈述：desc_f' (j : ι) (hj : ¬ c.Rel j (c.next j)) : (desc φ α hα).f j = sndX φ j
 ≫ α.f j
参数：j : ι；hj : ¬ c.Rel j (c.next j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma desc_f' (j : ι) (hj : ¬ c.Rel j (c.next j)) :
    (desc φ α hα).f j = sndX φ j ≫ α.f j := by
  apply dif_neg hj

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inlX_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex.homotopyCofiber`。
形式化陈述：inlX_desc_f (i j : ι) (hjk : c.Rel j i) : inlX φ i j hjk ≫ (desc φ α hα).f
 j = hα.hom i j
参数：i j : ι；hjk : c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma inlX_desc_f (i j : ι) (hjk : c.Rel j i) :
    inlX φ i j hjk ≫ (desc φ α hα).f j = hα.hom i j := by
  obtain rfl := c.next_eq' hjk
  dsimp [desc]
  rw [dif_pos hjk, comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrX_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex.homotopyCofiber`。
形式化陈述：inrX_desc_f (i : ι) : inrX φ i ≫ (desc φ α hα).f i = α.f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma inrX_desc_f (i : ι) :
    inrX φ i ≫ (desc φ α hα).f i = α.f i := by
  dsimp [desc]
  split_ifs <;> simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inr_desc** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex.homotopyCofiber`。
形式化陈述：inr_desc : inr φ ≫ desc φ α hα = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_desc_f`：inrX_desc_f (i : ι) : in
rX φ i ≫ (desc φ α hα).f i = α.f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_desc :
    inr φ ≫ desc φ α hα = α := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom_desc_hom** 是 Mathlib 中的
一个引理，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inrCompHomotopy_hom_desc_hom (hc : forall j, exists i, c.Rel i j) (i j : ι
) : (inrCompHomotopy φ hc).hom i j ≫ (desc φ α hα).f j = hα.hom i j
参数：hc : forall j, exists i, c.Rel i j；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom`：inrCompHomotopy_
hom (i j : ι) (hij : c.Rel j i) : (inrCompHomotopy φ hc).hom i j = inlX φ i j hi
j
· 使用引理 `HomologicalComplex.homotopyCofiber.desc_f`：desc_f (j k : ι) (hjk : c.Rel
 j k) : (desc φ α hα).f j = fstX φ j _ hjk ≫ hα.hom _ j + sndX φ j ≫ α.f j
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Homotopy.zero`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Cate
gory.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C
 D …
-/
lemma inrCompHomotopy_hom_desc_hom (hc : ∀ j, ∃ i, c.Rel i j) (i j : ι) :
    (inrCompHomotopy φ hc).hom i j ≫ (desc φ α hα).f j = hα.hom i j := by
  by_cases hij : c.Rel j i
  · dsimp
    simp only [inrCompHomotopy_hom φ hc i j hij, desc_f φ α hα _ _ hij,
      comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
  · simp only [Homotopy.zero _ _ _ hij, zero_comp]

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.homotopyCofiber.eq_desc** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex.homotopyCofiber`。
形式化陈述：eq_desc (f : homotopyCofiber φ ⟶ K) (hc : forall j, exists i, c.Rel i j) :
 f = desc φ (inr φ ≫ f) (Homotopy.trans (Homotopy.ofEq (by simp)) (((inrCompHomo
topy φ hc).compRight f).trans (Homotopy.ofEq (by simp))))
参数：f : homotopyCofiber φ ⟶ K；hc : forall j, exists i, c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_from_X`：ext_from_X (i j : ι) (hij
 : c.Rel j i) {A : C} {f g : X φ j ⟶ A} (h₁ : inlX φ i j hij ≫ f = inlX φ i j hi
j ≫ g) (h₂ : inrX φ j ≫ f = inrX φ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_desc_f`：inlX_desc_f (i j : ι) (h
jk : c.Rel j i) : inlX φ i j hjk ≫ (desc φ α hα).f j = hα.hom i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom`：inrCompHomotopy_
hom (i j : ι) (hij : c.Rel j i) : (inrCompHomotopy φ hc).hom i j = inlX φ i j hi
j
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_desc_f`：inrX_desc_f (i : ι) : in
rX φ i ≫ (desc φ α hα).f i = α.f i
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_from_X'`：ext_from_X' (i : ι) (hi 
: ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A} (h : inrX φ i ≫ f = inrX φ i ≫
 g) : f = g
-/
lemma eq_desc (f : homotopyCofiber φ ⟶ K) (hc : ∀ j, ∃ i, c.Rel i j) :
    f = desc φ (inr φ ≫ f) (Homotopy.trans (Homotopy.ofEq (by simp))
      (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))) := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ _ _ hj
    · simp [inrCompHomotopy_hom _ _ _ _ hj]
    · simp
  · apply ext_from_X' φ _ hj
    simp

end

omit [DecidableRel c.Rel] in
/-
**HomologicalComplex.homotopyCofiber.descSigma_ext_iff** 是 Mathlib 中的一个引理，位于命名空间
 `HomologicalComplex.homotopyCofiber`。
形式化陈述：descSigma_ext_iff {φ : F ⟶ G} {K : HomologicalComplex C c} (x y : Σ (α : G
 ⟶ K), Homotopy (φ ≫ α) 0) : x = y ↔ x.1 = y.1 ∧ (forall (i j : ι) (_ : c.Rel j 
i), x.2.hom i j = y.2.hom i j)
参数：x y : Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Homotopy.ext`：∀ {ι : Type u_1} {V : Type u} {inst : CategoryTheory.Categ
ory.{v, u} V} {inst_1 : CategoryTheory.Preadditive V}   {c : ComplexShape ι} {C 
D …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Homotopy.zero`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Cate
gory.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C
 D …
-/
lemma descSigma_ext_iff {φ : F ⟶ G} {K : HomologicalComplex C c}
    (x y : Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) :
    x = y ↔ x.1 = y.1 ∧ (∀ (i j : ι) (_ : c.Rel j i), x.2.hom i j = y.2.hom i j) := by
  constructor
  · rintro rfl
    tauto
  · obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    rintro ⟨rfl, h⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · simp only [Homotopy.zero _ _ _ hij]

/-- Morphisms `homotopyCofiber φ ⟶ K` are uniquely determined by
a morphism `α : G ⟶ K` and a homotopy from `φ ≫ α` to `0`. -/
/-
**HomologicalComplex.homotopyCofiber.descEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Homolo
gicalComplex.homotopyCofiber`。
形式化陈述：descEquiv (K : HomologicalComplex C c) (hc : forall j, exists i, c.Rel i j
) : (Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) ≃ (homotopyCofiber φ ⟶ K) where toFun
参数：K : HomologicalComplex C c；hc : forall j, exists i, c.Rel i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms `homotopyCofiber φ ⟶ K` are uniquely determined by
a morphism `α : G ⟶ K` and a homotopy from `φ ≫ α` to `0`.
-/
noncomputable def descEquiv (K : HomologicalComplex C c) (hc : ∀ j, ∃ i, c.Rel i j) :
    (Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) ≃ (homotopyCofiber φ ⟶ K) where
  toFun := fun ⟨α, hα⟩ => desc φ α hα
  invFun f := ⟨inr φ ≫ f, Homotopy.trans (Homotopy.ofEq (by simp))
    (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))⟩
  right_inv f := (eq_desc φ f hc).symm
  left_inv := fun ⟨α, hα⟩ => by
    rw [descSigma_ext_iff]
    cat_disch

section

variable {F' F'' G' G'' : HomologicalComplex C c} (φ' : F' ⟶ G') (φ'' : F'' ⟶ G'')
  [HasHomotopyCofiber φ'] [HasHomotopyCofiber φ'']
  (H : ∀ (j : ι), ∃ i, c.Rel i j)

set_option backward.defeqAttrib.useBackward true in
/-- The morphism between homotopy cofibers that is induced by a
morphism of arrows. -/
/-
**HomologicalComplex.homotopyCofiber.mapArrowHom** 是 Mathlib 中的一个定义，位于命名空间 `Homo
logicalComplex.homotopyCofiber`。
形式化陈述：mapArrowHom (α : Arrow.mk φ ⟶ Arrow.mk φ') : homotopyCofiber φ ⟶ homotopyC
ofiber φ'
参数：α : Arrow.mk φ ⟶ Arrow.mk φ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between homotopy cofibers that is induced by a
morphism of arrows.
-/
noncomputable def mapArrowHom (α : Arrow.mk φ ⟶ Arrow.mk φ') :
    homotopyCofiber φ ⟶ homotopyCofiber φ' :=
  desc _ (α.right ≫ homotopyCofiber.inr φ')
    ((Homotopy.ofEq (by
        simp [reassoc_of% dsimp% α.w])).trans (((inrCompHomotopy φ' H).compLeft α.left).trans
      (Homotopy.ofEq (by simp))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HomologicalComplex.homotopyCofiber.mapArrowHom_id** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex.homotopyCofiber`。
形式化陈述：mapArrowHom_id : mapArrowHom φ φ H (𝟙 _) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X`：ext_to_X (i j : ι) (hij : c
.Rel i j) {A : C} {f g : A ⟶ X φ i} (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hi
j) (h₂ : f ≫ sndX φ i = g ≫ sndX …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.homotopyCofiber.desc_f`：desc_f (j k : ι) (hjk : c.Rel
 j k) : (desc φ α hα).f j = fstX φ j _ hjk ≫ hα.hom _ j + sndX φ j ≫ α.f j
· 使用引理 `HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom`：inrCompHomotopy_
hom (i j : ι) (hij : c.Rel j i) : (inrCompHomotopy φ hc).hom i j = inlX φ i j hi
j
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_fstX`：inlX_fstX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_fstX`：inrX_fstX (i j : ι) (hij :
 c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_sndX`：inlX_sndX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ sndX φ j = 0
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X'`：ext_to_X' (i : ι) (hi : ¬ 
c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i} (h : f ≫ sndX φ i = g ≫ sndX φ i) 
: f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.desc_f'`：desc_f' (j : ι) (hj : ¬ c.Re
l j (c.next j)) : (desc φ α hα).f j = sndX φ j ≫ α.f j
-/
lemma mapArrowHom_id : mapArrowHom φ φ H (𝟙 _) = 𝟙 _ := by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.homotopyCofiber.mapArrowHom_comp** 是 Mathlib 中的一个引理，位于命名空间 
`HomologicalComplex.homotopyCofiber`。
形式化陈述：mapArrowHom_comp (α : Arrow.mk φ ⟶ Arrow.mk φ') (β : Arrow.mk φ' ⟶ Arrow.m
k φ'') : mapArrowHom φ φ'' H (α ≫ β) = mapArrowHom φ φ' H α ≫ mapArrowHom φ' φ''
 H β
参数：α : Arrow.mk φ ⟶ Arrow.mk φ'；β : Arrow.mk φ' ⟶ Arrow.mk φ''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X`：ext_to_X (i j : ι) (hij : c
.Rel i j) {A : C} {f g : A ⟶ X φ i} (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hi
j) (h₂ : f ≫ sndX φ i = g ≫ sndX …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.homotopyCofiber.desc_f`：desc_f (j k : ι) (hjk : c.Rel
 j k) : (desc φ α hα).f j = fstX φ j _ hjk ≫ hα.hom _ j + sndX φ j ≫ α.f j
· 使用引理 `HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom`：inrCompHomotopy_
hom (i j : ι) (hij : c.Rel j i) : (inrCompHomotopy φ hc).hom i j = inlX φ i j hi
j
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_fstX`：inlX_fstX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_fstX`：inrX_fstX (i j : ι) (hij :
 c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_sndX`：inlX_sndX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ sndX φ j = 0
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X'`：ext_to_X' (i : ι) (hi : ¬ 
c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i} (h : f ≫ sndX φ i = g ≫ sndX φ i) 
: f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.desc_f'`：desc_f' (j : ι) (hj : ¬ c.Re
l j (c.next j)) : (desc φ α hα).f j = sndX φ j ≫ α.f j
-/
lemma mapArrowHom_comp
    (α : Arrow.mk φ ⟶ Arrow.mk φ') (β : Arrow.mk φ' ⟶ Arrow.mk φ'') :
    mapArrowHom φ φ'' H (α ≫ β) = mapArrowHom φ φ' H α ≫ mapArrowHom φ' φ'' H β := by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

/-- The isomorphism between homotopy cofibers that is induced by an
isomorphism of arrows. -/
@[simps]
/-
**HomologicalComplex.homotopyCofiber.mapArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `Homo
logicalComplex.homotopyCofiber`。
形式化陈述：mapArrowIso (α : Arrow.mk φ ≅ Arrow.mk φ') : homotopyCofiber φ ≅ homotopyC
ofiber φ' where hom
参数：α : Arrow.mk φ ≅ Arrow.mk φ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between homotopy cofibers that is induced by an
isomorphism of arrows.
-/
noncomputable def mapArrowIso (α : Arrow.mk φ ≅ Arrow.mk φ') :
    homotopyCofiber φ ≅ homotopyCofiber φ' where
  hom := mapArrowHom φ φ' H α.hom
  inv := mapArrowHom φ' φ H α.inv
  hom_inv_id := by rw [← mapArrowHom_comp, Iso.hom_inv_id, mapArrowHom_id]
  inv_hom_id := by rw [← mapArrowHom_comp, Iso.inv_hom_id, mapArrowHom_id]

end

section

variable {D : Type*} [Category* D] [Preadditive D] (H : C ⥤ D) [H.Additive]
  [HasHomotopyCofiber ((H.mapHomologicalComplex c).map φ)]

/-- Auxiliary definition for `mapHomologicalComplexObjIso`. -/
/-
**HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjXIso** 是 Mathlib 中的
一个定义，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：mapHomologicalComplexObjXIso (i : ι) : H.obj ((homotopyCofiber φ).X i) ≅ (
homotopyCofiber ((H.mapHomologicalComplex c).map φ)).X i
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Auxiliary definition for `mapHomologicalComplexObjIso`.
-/
noncomputable def mapHomologicalComplexObjXIso (i : ι) :
    H.obj ((homotopyCofiber φ).X i) ≅
      (homotopyCofiber ((H.mapHomologicalComplex c).map φ)).X i :=
  if hi : c.Rel i (c.next i)
  then by
    haveI := preservesBinaryBiproducts_of_preservesBiproducts H
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    haveI := HasHomotopyCofiber.hasBinaryBiproduct ((H.mapHomologicalComplex c).map φ) _ _ hi
    exact H.mapIso (homotopyCofiber.XIsoBiprod φ _ _ hi) ≪≫ H.mapBiprod _ _ ≪≫
      (homotopyCofiber.XIsoBiprod ((H.mapHomologicalComplex c).map φ) _ _ hi).symm
  else H.mapIso (homotopyCofiber.XIso φ i hi) ≪≫
    (homotopyCofiber.XIso ((H.mapHomologicalComplex c).map φ) i hi).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv** 是 M
athlib 中的一个引理，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inlX_mapHomologicalComplexObjXIso_inv (i j : ι) (hij : c.Rel j i) : inlX (
(H.mapHomologicalComplex c).map φ) i j hij ≫ (mapHomologicalComplexObjXIso φ H j
).inv = H.map (inlX φ i j hij)
参数：i j : ι；hij : c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Limits.biprod.uniqueUpToIso_inv`：∀ {C : Type uC} [inst : 
CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (X Y : C) [inst_2 : Categ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.mapBinaryBicone_inl`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.mapBinaryBicone_inr`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pr
eadditive C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用引理 `HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv`：inl_XIsoBiprod_in
v (i j : ι) (hij : c.Rel j i) : haveI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
lemma inlX_mapHomologicalComplexObjXIso_inv
    (i j : ι) (hij : c.Rel j i) :
    inlX ((H.mapHomologicalComplex c).map φ) i j hij ≫
      (mapHomologicalComplexObjXIso φ H j).inv = H.map (inlX φ i j hij) := by
  obtain rfl := c.next_eq' hij
  simp [mapHomologicalComplexObjXIso, dif_pos hij, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv** 是 M
athlib 中的一个引理，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inrX_mapHomologicalComplexObjXIso_inv (i : ι) : inrX ((H.mapHomologicalCom
plex c).map φ) i ≫ (mapHomologicalComplexObjXIso φ H i).inv = H.map (inrX φ i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Limits.biprod.uniqueUpToIso_inv`：∀ {C : Type uC} [inst : 
CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (X Y : C) [inst_2 : Categ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.mapBinaryBicone_inl`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.mapBinaryBicone_inr`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pr
eadditive C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用引理 `HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv`：inr_XIsoBiprod_in
v (i j : ι) (hij : c.Rel j i) : haveI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma inrX_mapHomologicalComplexObjXIso_inv (i : ι) :
    inrX ((H.mapHomologicalComplex c).map φ) i ≫
      (mapHomologicalComplexObjXIso φ H i).inv = H.map (inrX φ i) := by
  by_cases hi : c.Rel i (c.next i)
  · simp [mapHomologicalComplexObjXIso, dif_pos hi, ← Functor.map_comp]
  · dsimp [mapHomologicalComplexObjXIso, XIso, inrX]
    simp [dif_neg hi]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso_hom**
 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：map_inrX_mapHomologicalComplexObjXIso_hom (i : ι) : H.map (inrX φ i) ≫ (ma
pHomologicalComplexObjXIso φ H i).hom = inrX ((H.mapHomologicalComplex c).map φ)
 i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv
_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 :
 CategoryTheory.Preadditive C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma map_inrX_mapHomologicalComplexObjXIso_hom (i : ι) :
    H.map (inrX φ i) ≫ (mapHomologicalComplexObjXIso φ H i).hom =
      inrX ((H.mapHomologicalComplex c).map φ) i := by
  rw [← inrX_mapHomologicalComplexObjXIso_inv_assoc, Iso.inv_hom_id, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism expressing the commutation between taking
the homotopy cofiber of a morphism of homological complexes and
applying an additive functor. -/
/-
**HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso** 是 Mathlib 中的一
个定义，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：mapHomologicalComplexObjIso : (H.mapHomologicalComplex c).obj (homotopyCof
iber φ) ≅ homotopyCofiber ((H.mapHomologicalComplex c).map φ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The isomorphism expressing the commutation between taking
the homotopy cofiber of a morphism of homological complexes and
applying an additive functor.
-/
noncomputable def mapHomologicalComplexObjIso :
    (H.mapHomologicalComplex c).obj (homotopyCofiber φ) ≅
      homotopyCofiber ((H.mapHomologicalComplex c).map φ) :=
  Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (mapHomologicalComplexObjXIso φ H i).symm)
    (fun i j hij ↦ by
      dsimp
      apply ext_from_X _ _ _ hij
      · by_cases hj : c.Rel j (c.next j)
        · simp [← Functor.map_comp, inlX_d _ _ _ _ _ hj, inlX_d_assoc _ _ _ _ _ hj]
        · simp [← Functor.map_comp, inlX_d' _ _ _ _ hj, inlX_d'_assoc _ _ _ _ hj]
      · simp [← Functor.map_comp]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homotopyCofiber.inr_mapHomologicalComplexObjIso_hom** 是 Mat
hlib 中的一个引理，位于命名空间 `HomologicalComplex.homotopyCofiber`。
形式化陈述：inr_mapHomologicalComplexObjIso_hom : (H.mapHomologicalComplex c).map (inr
 φ) ≫ (mapHomologicalComplexObjIso φ H).hom = inr _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapHomologicalComplex_map_f`：∀ {ι : Type u_1} {W₁
 : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁]   [i
nst_1 : CategoryTheory.Category.{v_3, u_…
· 使用定理 `HomologicalComplex.homotopyCofiber.inr_f`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {ι : Ty
pe u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.Hom.isoOfComponents_inv_f`：∀ {ι : Type u_1} {V : Type
 u} [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms V] {c : ComplexSh…
· 使用引理 `HomologicalComplex.homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso
_hom`：map_inrX_mapHomologicalComplexObjXIso_hom (i : ι) : H.map (inrX φ i) ≫ (ma
pHomologicalComplexObjXIso φ H i).hom = inrX ((H.mapHomologicalCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_mapHomologicalComplexObjIso_hom :
    (H.mapHomologicalComplex c).map (inr φ) ≫
      (mapHomologicalComplexObjIso φ H).hom = inr _ := by
  ext
  simp [mapHomologicalComplexObjIso]

end

end homotopyCofiber

section

variable (K)
variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

/-- Given a homological complex `K`, this is the property that the morphism
`K ⟶ K ⊞ K` induced by `𝟙 K` and `-𝟙 K` has a cofiber, which allows
to define `K.cylinder` as this cofiber. -/
/-
**HomologicalComplex.HasCylinder** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：HasCylinder : Prop
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
Given a homological complex `K`, this is the property that the morphism
`K ⟶ K ⊞ K` induced by `𝟙 K` and `-𝟙 K` has a cofiber, which allows
to define `K.cylinder` as this cofiber.
-/
abbrev HasCylinder : Prop := HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

variable [K.HasCylinder]

/-- The cylinder object of a homological complex `K` is the homotopy cofiber
of the morphism  `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`. -/
/-
**HomologicalComplex.cylinder** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：cylinder
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
The cylinder object of a homological complex `K` is the homotopy cofiber
of the morphism  `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`.
-/
noncomputable abbrev cylinder := homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

namespace cylinder

/-- The left inclusion `K ⟶ K.cylinder`. -/
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inclusion `K ⟶ K.cylinder`.
-/
noncomputable def ι₀ : K ⟶ K.cylinder := biprod.inl ≫ homotopyCofiber.inr _

/-- The right inclusion `K ⟶ K.cylinder`. -/
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion `K ⟶ K.cylinder`.
-/
noncomputable def ι₁ : K ⟶ K.cylinder := biprod.inr ≫ homotopyCofiber.inr _

variable {K}

section

variable (φ₀ φ₁ : K ⟶ F) (h : Homotopy φ₀ φ₁)

/-- The morphism `K.cylinder ⟶ F` that is induced by two morphisms `φ₀ φ₁ : K ⟶ F`
and a homotopy `h : Homotopy φ₀ φ₁`. -/
/-
**HomologicalComplex.cylinder.desc** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
.cylinder`。
形式化陈述：desc : K.cylinder ⟶ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
The morphism `K.cylinder ⟶ F` that is induced by two morphisms `φ₀ φ₁ : K ⟶ F`
and a homotopy `h : Homotopy φ₀ φ₁`.
-/
noncomputable def desc : K.cylinder ⟶ F :=
  homotopyCofiber.desc _ (biprod.desc φ₀ φ₁)
    (Homotopy.trans (Homotopy.ofEq (by
      simp only [biprod.lift_desc, id_comp, neg_comp, sub_eq_add_neg]))
      ((Homotopy.equivSubZero h)))

@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_desc : ι₀ K ≫ desc φ₀ φ₁ h = φ₀ := by simp [ι₀, desc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_desc : ι₁ K ≫ desc φ₀ φ₁ h = φ₁ := by simp [ι₁, desc]

end

variable (K)

/-- The projection `π : K.cylinder ⟶ K`. -/
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `π : K.cylinder ⟶ K`.
-/
noncomputable def π : K.cylinder ⟶ K := desc (𝟙 K) (𝟙 K) (Homotopy.refl _)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_π : ι₀ K ≫ π K = 𝟙 K := by simp [π]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_π : ι₁ K ≫ π K = 𝟙 K := by simp [π]

/-- The left inclusion `K.X i ⟶ K.cylinder.X j` when `c.Rel j i`. -/
/-
**HomologicalComplex.cylinder.inlX** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCompl
ex.cylinder`。
形式化陈述：inlX (i j : ι) (hij : c.Rel j i) : K.X i ⟶ K.cylinder.X j
参数：i j : ι；hij : c.Rel j i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
The left inclusion `K.X i ⟶ K.cylinder.X j` when `c.Rel j i`.
-/
noncomputable abbrev inlX (i j : ι) (hij : c.Rel j i) : K.X i ⟶ K.cylinder.X j :=
  homotopyCofiber.inlX (biprod.lift (𝟙 K) (-𝟙 K)) i j hij

/-- The right inclusion `(K ⊞ K).X i ⟶ K.cylinder.X i`. -/
/-
**HomologicalComplex.cylinder.inrX** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCompl
ex.cylinder`。
形式化陈述：inrX (i : ι) : (K ⊞ K).X i ⟶ K.cylinder.X i
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
The right inclusion `(K ⊞ K).X i ⟶ K.cylinder.X i`.
-/
noncomputable abbrev inrX (i : ι) : (K ⊞ K).X i ⟶ K.cylinder.X i :=
  homotopyCofiber.inrX (biprod.lift (𝟙 K) (-𝟙 K)) i

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.inlX_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.cylinder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inlX_π (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (π K).f j = 0 := by
  simp [HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, Homotopy.equivSubZero]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.inrX_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.cylinder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inrX_π (i : ι) :
    inrX K i ≫ (π K).f i = (biprod.desc (𝟙 _) (𝟙 K)).f i :=
  homotopyCofiber.inrX_desc_f _ _ _ _

section

variable (hc : ∀ j, ∃ i, c.Rel i j)

namespace πCompι₀Homotopy

/-- A null homotopic map `K.cylinder ⟶ K.cylinder` which identifies to
`π K ≫ ι₀ K - 𝟙 _`, see `nullHomotopicMap_eq`. -/
/-
**HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap** 是 Mathlib 中的一个定
义，位于命名空间 `HomologicalComplex.cylinder.πCompι₀Homotopy`。
形式化陈述：nullHomotopicMap : K.cylinder ⟶ K.cylinder
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
A null homotopic map `K.cylinder ⟶ K.cylinder` which identifies to
`π K ≫ ι₀ K - 𝟙 _`, see `nullHomotopicMap_eq`.
-/
noncomputable def nullHomotopicMap : K.cylinder ⟶ K.cylinder :=
  Homotopy.nullHomotopicMap'
    (fun i j hij => homotopyCofiber.sndX (biprod.lift (𝟙 K) (-𝟙 K)) i ≫
      (biprod.snd : K ⊞ K ⟶ K).f i ≫ inlX K i j hij)

/-- The obvious homotopy from `nullHomotopicMap K` to zero. -/
/-
**HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopy** 是 Mathlib 中的一个定义，位于
命名空间 `HomologicalComplex.cylinder.πCompι₀Homotopy`。
形式化陈述：nullHomotopy : Homotopy (nullHomotopicMap K) 0
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
The obvious homotopy from `nullHomotopicMap K` to zero.
-/
noncomputable def nullHomotopy : Homotopy (nullHomotopicMap K) 0 :=
  Homotopy.nullHomotopy' _

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.cylinder.πCompι₀Homotopy.inlX_nullHomotopy_f** 是 Mathlib 中的
一个引理，位于命名空间 `HomologicalComplex.cylinder.πCompι₀Homotopy`。
形式化陈述：inlX_nullHomotopy_f (i j : ι) (hij : c.Rel j i) : inlX K i j hij ≫ (nullHo
motopicMap K).f j = inlX K i j hij ≫ (π K ≫ ι₀ K - 𝟙 _).f j
参数：i j : ι；hij : c.Rel j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap'_f`：∀ {ι : Type u_1} {V : Type u} [inst : Cate
goryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : Com
plexShape ι} {C D …
· 使用定理 `HomologicalComplex.homotopyCofiber.d_sndX_assoc`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
{ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_fstX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inlX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `HomologicalComplex.cylinder.inlX_π_assoc`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {ι : Ty
pe u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Homotopy.nullHomotopicMap'_f_of_not_rel_right`：∀ {ι : Type u_1} {V : Typ
e u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preaddit
ive V]   {c : ComplexShape ι} {C D …
-/
lemma inlX_nullHomotopy_f (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (nullHomotopicMap K).f j =
      inlX K i j hij ≫ (π K ≫ ι₀ K - 𝟙 _).f j := by
  dsimp [nullHomotopicMap]
  by_cases! hj : ∃ (k : ι), c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f hjk hij, homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc, zero_comp, add_zero, comp_sub, inlX_π_assoc, comp_id,
      zero_sub, ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f,
      neg_comp, id_comp]
  · simp only [Homotopy.nullHomotopicMap'_f_of_not_rel_right hij hj, homotopyCofiber_d, assoc,
    comp_sub, comp_id,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, zero_comp, add_zero,
      homotopyCofiber.inlX_fstX_assoc, homotopyCofiber.inlX_sndX_assoc,
      ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f, neg_comp,
      id_comp, inlX_π_assoc, zero_sub]

include hc

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.cylinder.πCompι₀Homotopy.inrX_nullHomotopy_f** 是 Mathlib 中的
一个引理，位于命名空间 `HomologicalComplex.cylinder.πCompι₀Homotopy`。
形式化陈述：inrX_nullHomotopy_f (j : ι) : inrX K j ≫ (nullHomotopicMap K).f j = inrX K
 j ≫ (π K ≫ ι₀ K - 𝟙 _).f j
参数：j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Homotopy.nullHomotopicMap'_f`：∀ {ι : Type u_1} {V : Type u} [inst : Cate
goryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : Com
plexShape ι} {C D …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_d`：inlX_d (i j k : ι) (hij : c.R
el i j) (hjk : c.Rel j k) : inlX φ j i hij ≫ d φ i j = -F.d j k ≫ inlX φ k j hjk
 + φ.f j ≫ inrX φ j
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_d_assoc`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
{ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.homotopyCofiber.inrX_sndX_assoc`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `add_neg_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a +
 (-a + b) = b
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `HomologicalComplex.cylinder.inrX_π_assoc`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {ι : Ty
pe u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
（共 46 条，此处仅展示前 30 条）
-/
lemma inrX_nullHomotopy_f (j : ι) :
    inrX K j ≫ (nullHomotopicMap K).f j = inrX K j ≫ (π K ≫ ι₀ K - 𝟙 _).f j := by
  have : biprod.lift (𝟙 K) (-𝟙 K) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  obtain ⟨i, hij⟩ := hc j
  dsimp [nullHomotopicMap]
  by_cases hj : ∃ (k : ι), c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Homotopy.nullHomotopicMap'_f hij hjk, homotopyCofiber_d, assoc, comp_add,
      homotopyCofiber.inrX_d_assoc, homotopyCofiber.inrX_sndX_assoc, comp_sub,
      inrX_π_assoc, comp_id, ← Hom.comm_assoc, homotopyCofiber.inlX_d _ _ _ _ _ hjk,
      comp_neg, add_neg_cancel_left]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp [ι₀]
    · simp only [inr_biprodXIso_inv_assoc, biprod_inr_snd_f_assoc, comp_sub,
        biprod_inr_desc_f_assoc, id_f, id_comp, ι₀, comp_f, this,
        sub_f_apply, sub_comp, homotopyCofiber.inr_f]
  · simp only [not_exists] at hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f_of_not_rel_left hij hj,
      homotopyCofiber_d, homotopyCofiber.inlX_d' _ _ _ _ (hj _), homotopyCofiber.inrX_sndX_assoc,
      comp_sub, inrX_π_assoc, comp_id, ι₀, comp_f, homotopyCofiber.inr_f]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp
    · simp [this]
/-
**HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap_eq** 是 Mathlib 中的
一个引理，位于命名空间 `HomologicalComplex.cylinder.πCompι₀Homotopy`。
形式化陈述：nullHomotopicMap_eq : nullHomotopicMap K = π K ≫ ι₀ K - 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_from_X`：ext_from_X (i j : ι) (hij
 : c.Rel j i) {A : C} {f g : X φ j ⟶ A} (h₁ : inlX φ i j hij ≫ f = inlX φ i j hi
j ≫ g) (h₂ : inrX φ j ≫ f = inrX φ …
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用引理 `HomologicalComplex.cylinder.πCompι₀Homotopy.inlX_nullHomotopy_f`：inlX_nu
llHomotopy_f (i j : ι) (hij : c.Rel j i) : inlX K i j hij ≫ (nullHomotopicMap K)
.f j = inlX K i j hij ≫ (π K ≫ ι₀ K - 𝟙 _).f j
· 使用引理 `HomologicalComplex.cylinder.πCompι₀Homotopy.inrX_nullHomotopy_f`：inrX_nu
llHomotopy_f (j : ι) : inrX K j ≫ (nullHomotopicMap K).f j = inrX K j ≫ (π K ≫ ι
₀ K - 𝟙 _).f j
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_from_X'`：ext_from_X' (i : ι) (hi 
: ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A} (h : inrX φ i ≫ f = inrX φ i ≫
 g) : f = g
-/
lemma nullHomotopicMap_eq : nullHomotopicMap K = π K ≫ ι₀ K - 𝟙 _ := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (biprod.lift (𝟙 K) (-𝟙 K)) (c.next i) i hi
      (inlX_nullHomotopy_f _ _ _ _) (inrX_nullHomotopy_f _ hc _)
  · exact homotopyCofiber.ext_from_X' (biprod.lift (𝟙 K) (-𝟙 K)) _ hi (inrX_nullHomotopy_f _ hc _)

end πCompι₀Homotopy

/-- The homotopy between `π K ≫ ι₀ K` and `𝟙 K.cylinder`. -/
/-
**HomologicalComplex.cylinder.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between `π K ≫ ι₀ K` and `𝟙 K.cylinder`.
-/
noncomputable def πCompι₀Homotopy : Homotopy (π K ≫ ι₀ K) (𝟙 K.cylinder) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (πCompι₀Homotopy.nullHomotopicMap_eq K hc).symm).trans
      (πCompι₀Homotopy.nullHomotopy K))

/-- The homotopy equivalence between `K.cylinder` and `K`. -/
@[simps]
/-
**HomologicalComplex.cylinder.homotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Homologic
alComplex.cylinder`。
形式化陈述：homotopyEquiv : HomotopyEquiv K.cylinder K where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy equivalence between `K.cylinder` and `K`.
-/
noncomputable def homotopyEquiv : HomotopyEquiv K.cylinder K where
  hom := π K
  inv := ι₀ K
  homotopyHomInvId := πCompι₀Homotopy K hc
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- The homotopy between `cylinder.ι₀ K` and `cylinder.ι₁ K`. -/
/-
**HomologicalComplex.cylinder.homotopy** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex.cylinder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between `cylinder.ι₀ K` and `cylinder.ι₁ K`.
-/
noncomputable def homotopy₀₁ : Homotopy (ι₀ K) (ι₁ K) :=
  (Homotopy.ofEq (by simp)).trans (((πCompι₀Homotopy K hc).compLeft (ι₁ K)).trans
    (Homotopy.ofEq (by simp)))

include hc in
/-
**HomologicalComplex.cylinder.map_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
.cylinder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ι₀_eq_map_ι₁ {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map (ι₀ K) = H.map (ι₁ K) := by
  have : IsIso (H.map (cylinder.π K)) := hH _ ⟨homotopyEquiv K hc, rfl⟩
  simp only [← cancel_mono (H.map (cylinder.π K)), ← H.map_comp, ι₀_π, H.map_id, ι₁_π]

end


section

variable (F) {D : Type*} [Category* D] [Preadditive D] (H : C ⥤ D) [H.Additive]
  [∀ i, HasBinaryBiproduct (F.X i) (F.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 F) (-𝟙 F))]
  [∀ i, HasBinaryBiproduct (((H.mapHomologicalComplex c).obj F).X i)
    (((H.mapHomologicalComplex c).obj F).X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 ((H.mapHomologicalComplex c).obj F))
    (-𝟙 ((H.mapHomologicalComplex c).obj F)))]
  [HasHomotopyCofiber ((H.mapHomologicalComplex c).map (biprod.lift (𝟙 F) (-𝟙 F)))]
  (hc : ∀ (j : ι), ∃ i, c.Rel i j)

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism expressing the commutation between taking
the cylinder of a homological complex and applying an additive functor. -/
/-
**HomologicalComplex.cylinder.mapHomologicalComplexObjIso** 是 Mathlib 中的一个定义，位于命
名空间 `HomologicalComplex.cylinder`。
形式化陈述：mapHomologicalComplexObjIso : (H.mapHomologicalComplex c).obj (cylinder F)
 ≅ cylinder ((H.mapHomologicalComplex c).obj F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The isomorphism expressing the commutation between taking
the cylinder of a homological complex and applying an additive functor.
-/
noncomputable def mapHomologicalComplexObjIso :
    (H.mapHomologicalComplex c).obj (cylinder F) ≅
      cylinder ((H.mapHomologicalComplex c).obj F) :=
  homotopyCofiber.mapHomologicalComplexObjIso _ H ≪≫
    homotopyCofiber.mapArrowIso _ _ hc
      (Arrow.isoMk (Iso.refl _) ((H.mapHomologicalComplex c).mapBiprod F F) (by
        apply biprod.hom_ext <;> simp [← Functor.map_comp]))

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.map_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
.cylinder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ι₀_mapHomologicalComplexObjIso_hom :
    (H.mapHomologicalComplex c).map (cylinder.ι₀ F) ≫ (mapHomologicalComplexObjIso F H hc).hom =
      cylinder.ι₀ _ := by
  dsimp [mapHomologicalComplexObjIso, ι₀, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp, assoc, homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc,
    homotopyCofiber.inr_desc, ← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.cylinder.map_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
.cylinder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ι₁_mapHomologicalComplexObjIso_hom :
    (H.mapHomologicalComplex c).map (cylinder.ι₁ F) ≫ (mapHomologicalComplexObjIso F H hc).hom =
      cylinder.ι₁ _ := by
  dsimp [mapHomologicalComplexObjIso, ι₁, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp, assoc, homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc,
    homotopyCofiber.inr_desc, ← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

end

end cylinder

omit [DecidableRel c.Rel] in
/-- If a functor inverts homotopy equivalences, it sends homotopic maps to the same map. -/
/-
**HomologicalComplex._root_.Homotopy.map_eq_of_inverts_homotopyEquivalences** 是 
Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor inverts homotopy equivalences, it sends homotopic maps to the same 
map.
-/
lemma _root_.Homotopy.map_eq_of_inverts_homotopyEquivalences
    {φ₀ φ₁ : F ⟶ G} (h : Homotopy φ₀ φ₁) (hc : ∀ j, ∃ i, c.Rel i j)
    [∀ i, HasBinaryBiproduct (F.X i) (F.X i)]
    [HasHomotopyCofiber (biprod.lift (𝟙 F) (-𝟙 F))]
    {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map φ₀ = H.map φ₁ := by
  classical
  simp only [← cylinder.ι₀_desc _ _ h, ← cylinder.ι₁_desc _ _ h, H.map_comp,
    cylinder.map_ι₀_eq_map_ι₁ _ hc _ hH]

end

end HomologicalComplex

