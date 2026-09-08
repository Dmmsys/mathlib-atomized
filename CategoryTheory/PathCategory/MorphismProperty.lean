/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `Mathlib/CategoryTheory/PathCategory/Basic.lean` in
order to reduce transitive imports.

We also define a morpism property `W.paths : MorphismProperty (Paths C)` for any
`W : MorphismProperty C`, consisting of all paths in `C` that consist only of morphisms in `W`. -/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory.Paths

section
variable (V : Type u₁) [Quiver.{v₁} V]

/-- A reformulation of `CategoryTheory.Paths.induction` in terms of `MorphismProperty`. -/
/-
**CategoryTheory.Paths.morphismProperty_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Paths`。
形式化陈述：morphismProperty_eq_top (P : MorphismProperty (Paths V)) (id : forall {v :
 V}, P (𝟙 ((of V).obj v))) (comp : forall {u v w : V} (p : (of V).obj u ⟶ (of V)
.obj v) (q : v ⟶ w), P p -> P (p ≫ (of V).map q)) : P = ⊤
参数：P : MorphismProperty (Paths V)；id : forall {v : V}, P (𝟙 ((of V).obj v))；comp
 : forall {u v w : V} (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p -> P (p
 ≫ (of V).map q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `CategoryTheory.Paths.induction`：induction (P : forall {a b : Paths V}, (
a ⟶ b) -> Prop) (id : forall {v : V}, P (𝟙 ((of V).obj v))) (comp : forall {u v 
w : V} (p : (of V).o…

--- 原说明 ---
A reformulation of `CategoryTheory.Paths.induction` in terms of `MorphismPropert
y`.
-/
lemma morphismProperty_eq_top
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p → P (p ≫ (of V).map q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction (fun f ↦ P f) id comp _

/-- A reformulation of `CategoryTheory.Paths.induction'` in terms of `MorphismProperty`. -/
/-
**CategoryTheory.Paths.morphismProperty_eq_top'** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Paths`。
形式化陈述：morphismProperty_eq_top' (P : MorphismProperty (Paths V)) (id : forall {v 
: V}, P (𝟙 ((of V).obj v))) (comp : forall {u v w : V} (p : u ⟶ v) (q : (of V).o
bj v ⟶ (of V).obj w), P q -> P ((of V).map p ≫ q)) : P = ⊤
参数：P : MorphismProperty (Paths V)；id : forall {v : V}, P (𝟙 ((of V).obj v))；comp
 : forall {u v w : V} (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w), P q -> P ((
of V).map p ≫ q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `CategoryTheory.Paths.induction'`：induction' (P : forall {a b : Paths V},
 (a ⟶ b) -> Prop) (id : forall {v : V}, P (𝟙 ((of V).obj v))) (comp : forall {u 
v w : V} (p : u ⟶ v) …

--- 原说明 ---
A reformulation of `CategoryTheory.Paths.induction'` in terms of `MorphismProper
ty`.
-/
lemma morphismProperty_eq_top'
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w), P q → P ((of V).map p ≫ q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction' (fun f ↦ P f) id comp _
/-
**CategoryTheory.Paths.morphismProperty_eq_top_of_isMultiplicative** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Paths`。
形式化陈述：morphismProperty_eq_top_of_isMultiplicative (P : MorphismProperty (Paths V
)) [P.IsMultiplicative] (hP : forall {u v : V} (p : u ⟶ v), P ((of V).map p)) : 
P = ⊤
参数：P : MorphismProperty (Paths V)；hP : forall {u v : V} (p : u ⟶ v), P ((of V).m
ap p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Paths.morphismProperty_eq_top`：morphismProperty_eq_top (P
 : MorphismProperty (Paths V)) (id : forall {v : V}, P (𝟙 ((of V).obj v))) (comp
 : forall {u v w : V} (p : (of V).…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
-/
lemma morphismProperty_eq_top_of_isMultiplicative (P : MorphismProperty (Paths V))
    [P.IsMultiplicative]
    (hP : ∀ {u v : V} (p : u ⟶ v), P ((of V).map p)) : P = ⊤ :=
  morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp ↦ P.comp_mem _ _ hp (hP q))
end
section

variable {C : Type*} [Category* C] {V : Type u₁} [Quiver.{v₁} V]

set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps]
/-
**CategoryTheory.Paths.liftNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pa
ths`。
形式化陈述：liftNatTrans {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ⟶ G.obj v)) 
(α_nat : {X Y : V} -> (f : X ⟶ Y) -> F.map (Quiver.Hom.toPath f) ≫ α_app Y = α_a
pp X ≫ G.map (Quiver.Hom.toPath f)) : F ⟶ G where app
参数：α_app : (v : V) -> (F.obj v ⟶ G.obj v)；α_nat : {X Y : V} -> (f : X ⟶ Y) -> F.
map (Quiver.Hom.toPath f) ≫ α_app Y = α_app X ≫ G.map (Quiver.Hom.toPath f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation between `F G : Paths V ⥤ C` is defined by its component
s and
its unary naturality squares.
-/
def liftNatTrans {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ⟶ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ α_app Y = α_app X ≫ G.map (Quiver.Hom.toPath f)) : F ⟶ G where
  app := α_app
  naturality := by
    apply MorphismProperty.of_eq_top
      (P := MorphismProperty.naturalityProperty (F₁ := F) α_app)
    exact morphismProperty_eq_top_of_isMultiplicative _ _ α_nat

/-- A natural isomorphism between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps!]
/-
**CategoryTheory.Paths.liftNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Path
s`。
形式化陈述：liftNatIso {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.ob
j v ≅ G.obj v)) (α_nat : {X Y : V} -> (f : X ⟶ Y) -> F.map (Quiver.Hom.toPath f)
 ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.toPath f)) : F ≅ G
参数：α_app : (v : V) -> (F.obj v ≅ G.obj v)；α_nat : {X Y : V} -> (f : X ⟶ Y) -> F.
map (Quiver.Hom.toPath f) ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.to
Path f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between `F G : Paths V ⥤ C` is defined by its components a
nd
its unary naturality squares.
-/
def liftNatIso {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ≅ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.toPath f)) :
    F ≅ G :=
  NatIso.ofComponents α_app (fun f ↦ (liftNatTrans (fun v ↦ (α_app v).hom) α_nat).naturality f)

end

end CategoryTheory.Paths

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

open Quiver

/-- For any morphism property `W` on `C`, `W.paths` is the morphism property on `Paths C`
containing all paths of morphisms in `W`. -/
/-
**CategoryTheory.MorphismProperty.paths** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：paths (W : MorphismProperty C) : MorphismProperty (Paths C)
参数：W : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any morphism property `W` on `C`, `W.paths` is the morphism property on `Pat
hs C`
containing all paths of morphisms in `W`.
-/
def paths (W : MorphismProperty C) : MorphismProperty (Paths C) :=
  fun _ _ p ↦ p.rec True fun _ f P ↦ P ∧ W f

@[simp]
/-
**CategoryTheory.MorphismProperty.nil_mem_paths** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：nil_mem_paths {W : MorphismProperty C} {X : C} : W.paths (.nil (a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
lemma nil_mem_paths {W : MorphismProperty C} {X : C} : W.paths (.nil (a := X)) := trivial
/-
**CategoryTheory.MorphismProperty.cons_mem_paths** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：cons_mem_paths {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y 
⟶ Z} (hp : W.paths p) (hf : W f) : W.paths (p.cons f)
参数：hp : W.paths p；hf : W f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cons_mem_paths {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
    (hp : W.paths p) (hf : W f) : W.paths (p.cons f) :=
  ⟨hp, hf⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.cons_mem_paths_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：cons_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f 
: Y ⟶ Z} : W.paths (p.cons f) ↔ W.paths p ∧ W f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cons_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z} :
    W.paths (p.cons f) ↔ W.paths p ∧ W f :=
  Iff.rfl
/-
**CategoryTheory.MorphismProperty.toPath_mem_paths** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：toPath_mem_paths {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} (hf : W f)
 : W.paths f.toPath
参数：hf : W f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
lemma toPath_mem_paths {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} (hf : W f) :
    W.paths f.toPath :=
  ⟨trivial, hf⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.toPath_mem_paths_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：toPath_mem_paths_iff {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} : W.pa
ths f.toPath ↔ W f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.MorphismProperty.toPath_mem_paths`：toPath_mem_paths {W : 
MorphismProperty C} {X Y : C} {f : X ⟶ Y} (hf : W f) : W.paths f.toPath
-/
lemma toPath_mem_paths_iff {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} :
    W.paths f.toPath ↔ W f :=
  ⟨fun h ↦ h.2, toPath_mem_paths⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.comp_mem_paths_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：comp_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {q 
: Path Y Z} : W.paths (p.comp q) ↔ W.paths p ∧ W.paths q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.comp_cons`：comp_cons {a b c d : V} (p : Path a b) (q : Path 
b c) (e : c ⟶ d) : p.comp (q.cons e) = (p.comp q).cons e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma comp_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {q : Path Y Z} :
    W.paths (p.comp q) ↔ W.paths p ∧ W.paths q := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hp, hq⟩ ↦ ?_⟩
  · induction q with
    | nil => simpa using h
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact h' h.1
  · induction q with
    | nil => simp
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact ⟨h' h.1, h.2⟩
  · induction q with
    | nil => exact hp
    | cons q q' h => exact ⟨h ⟨hp, hq.1⟩ hq.1, hq.2⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.comp_mem_paths_iff'** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：comp_mem_paths_iff' {W : MorphismProperty C} {X Y Z : Paths C} {p : X ⟶ Y}
 {q : Y ⟶ Z} : W.paths (p ≫ q) ↔ W.paths p ∧ W.paths q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem_paths_iff`：comp_mem_paths_iff {
W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {q : Path Y Z} : W.paths (p.c
omp q) ↔ W.paths p ∧ W.paths q
-/
lemma comp_mem_paths_iff' {W : MorphismProperty C} {X Y Z : Paths C} {p : X ⟶ Y} {q : Y ⟶ Z} :
    W.paths (p ≫ q) ↔ W.paths p ∧ W.paths q :=
  W.comp_mem_paths_iff
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty C) : W.paths.IsMultiplicative where
  id_mem _ := nil_mem_paths
  comp_mem _ _ hf hg := W.comp_mem_paths_iff'.2 ⟨hf, hg⟩

/-- If `W` and `W'` are morphism properties on `C` such that `W ≤ W'`, then `W.paths ≤ W'.paths`. -/
@[gcongr]
/-
**CategoryTheory.MorphismProperty.monotone_paths** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：monotone_paths : Monotone (paths (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `W` and `W'` are morphism properties on `C` such that `W ≤ W'`, then `W.paths
 ≤ W'.paths`.
-/
lemma monotone_paths : Monotone (paths (C := C)) :=
  fun _ _ h _ _ p ↦ p.rec (fun _ ↦ trivial) (fun _ _ hp' hp ↦ ⟨hp' hp.1, h _ hp.2⟩)
/-
**CategoryTheory.MorphismProperty.composePath_mem_of_id_mem** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：composePath_mem_of_id_mem (W : MorphismProperty C) [W.IsStableUnderComposi
tion] {X Y : C} {p : Path X Y} (hp : W.paths p) (h : W (𝟙 X)) : W (composePath p
)
参数：W : MorphismProperty C；hp : W.paths p；h : W (𝟙 X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma composePath_mem_of_id_mem (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
    {p : Path X Y} (hp : W.paths p) (h : W (𝟙 X)) : W (composePath p) := by
  revert hp
  exact p.rec (by simpa) fun p f hp hp' ↦ W.comp_mem _ _ (hp hp'.1) hp'.2
/-
**CategoryTheory.MorphismProperty.composePath_mem_of_length_pos** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：composePath_mem_of_length_pos (W : MorphismProperty C) [W.IsStableUnderCom
position] {X Y : C} {p : Path X Y} (hp : W.paths p) (h : 0 < p.length) : W (comp
osePath p)
参数：W : MorphismProperty C；hp : W.paths p；h : 0 < p.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma composePath_mem_of_length_pos (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
    {p : Path X Y} (hp : W.paths p) (h : 0 < p.length) : W (composePath p) := by
  revert hp h
  refine p.rec (by simp) fun p f hp hp' hp'' ↦ ?_
  cases p
  · simpa [paths] using hp'
  · refine W.comp_mem _ _ (hp hp'.1 (by simp)) hp'.2
/-
**CategoryTheory.MorphismProperty.composePath_mem** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：composePath_mem (W : MorphismProperty C) [W.IsMultiplicative] {X Y : C} {p
 : Path X Y} (hp : W.paths p) : W (composePath p)
参数：W : MorphismProperty C；hp : W.paths p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.composePath_mem_of_id_mem`：composePath_m
em_of_id_mem (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C} {p 
: Path X Y} (hp : W.paths p) (h : W (𝟙 X)) : W …
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
-/
lemma composePath_mem (W : MorphismProperty C) [W.IsMultiplicative] {X Y : C}
    {p : Path X Y} (hp : W.paths p) : W (composePath p) :=
  W.composePath_mem_of_id_mem hp <| W.id_mem X
/-
**CategoryTheory.MorphismProperty.paths_le_inverseImage** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：paths_le_inverseImage (W : MorphismProperty C) [W.IsMultiplicative] : W.pa
ths <= W.inverseImage (pathComposition C)
参数：W : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.composePath_mem`：composePath_mem (W : Mo
rphismProperty C) [W.IsMultiplicative] {X Y : C} {p : Path X Y} (hp : W.paths p)
 : W (composePath p)
-/
lemma paths_le_inverseImage (W : MorphismProperty C) [W.IsMultiplicative] :
    W.paths ≤ W.inverseImage (pathComposition C) :=
  fun _ _ _ ↦ W.composePath_mem

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty C) : IsMultiplicative (W.paths.strictMap (pathComposition C)) where
  id_mem X := W.paths.map_mem_strictMap (pathComposition C) _ (W.paths.id_mem X)
  comp_mem := fun _ _ ⟨hp⟩ ⟨hq⟩ ↦ by
    simpa using! W.paths.map_mem_strictMap (pathComposition C) _ <| W.paths.comp_mem _ _ hp hq

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure_eq_strictMap_paths** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：multiplicativeClosure_eq_strictMap_paths (W : MorphismProperty C) : W.mult
iplicativeClosure = W.paths.strictMap (pathComposition C)
参数：W : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.MorphismProperty.multiplicativeClosure_le_iff`：multiplica
tiveClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] : multiplicat
iveClosure W <= W' ↔ W <= W' where .trans h mp h
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeStrictMapPathsPathsP
athComposition`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (
W : CategoryTheory.MorphismProperty C),   (W.paths.strictMap (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.pathComposition_map`：∀ (C : Type u₁) [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y : CategoryTheory.Paths C} (f : X ⟶ Y),   (CategoryT
heory.pathComposition C)…
· 使用定理 `CategoryTheory.composePath_toPath`：composePath_toPath {X Y : C} (f : X ⟶
 Y) : composePath f.toPath = f
· 使用引理 `CategoryTheory.MorphismProperty.map_mem_strictMap`：map_mem_strictMap (P 
: MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) : (P.strictMa
p F) (F.map f)
· 使用引理 `CategoryTheory.MorphismProperty.composePath_mem`：composePath_mem (W : Mo
rphismProperty C) [W.IsMultiplicative] {X Y : C} {p : Path X Y} (hp : W.paths p)
 : W (composePath p)
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.
MorphismProperty C),   W.multiplicativeClosure.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.monotone_paths`：monotone_paths : Monoton
e (paths (C
· 使用引理 `CategoryTheory.MorphismProperty.le_multiplicativeClosure`：le_multiplicat
iveClosure : W <= W.multiplicativeClosure
-/
lemma multiplicativeClosure_eq_strictMap_paths (W : MorphismProperty C) :
    W.multiplicativeClosure = W.paths.strictMap (pathComposition C) := by
  refine le_antisymm ?_ fun _ _ _ ⟨h⟩ ↦ ?_
  · refine (W.multiplicativeClosure_le_iff _).2 fun X Y f hf ↦ ?_
    simpa using! W.paths.map_mem_strictMap (pathComposition C) f.toPath (by simpa)
  · exact composePath_mem _ <| monotone_paths W.le_multiplicativeClosure _ h

end CategoryTheory.MorphismProperty

