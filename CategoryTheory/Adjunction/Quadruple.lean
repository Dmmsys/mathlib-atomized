/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Adjoint quadruples

This file concerns adjoint quadruples `L ⊣ F ⊣ G ⊣ R` of functors `L G : C ⥤ D`, `F R : D ⥤ C`.
We bundle the adjunctions in a structure `Quadruple L F G R` and make the two triples `Triple L F G`
and `Triple F G R` accessible as `Quadruple.leftTriple` and `Quadruple.rightTriple`.

Currently the only two results are the following:
* When `F` and `R` are fully faithful, the components of the induced natural transformation `G ⟶ L`
  are epimorphisms iff the components of the natural transformation `F ⟶ R` are monomorphisms.
* When `L` and `G` are fully faithful, the components of the induced natural transformation `L ⟶ G`
  are epimorphisms iff the components of the natural transformation `R ⟶ F` are monomorphisms.

This is in particular relevant for the adjoint quadruples `π₀ ⊣ disc ⊣ Γ ⊣ codisc` that appear in
cohesive topoi, and can be found e.g. as proposition 2.7
[here](https://ncatlab.org/nlab/show/cohesive+topos).

Note that by `Triple.fullyFaithfulEquiv`, in an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` `L` is fully
faithful iff `G` is and `F` is fully faithful iff `R` is; these lemmas thus cover all cases in which
some of the functors are fully faithful. We opt to include only those typeclass assumptions that are
needed for the theorem statements, so some lemmas require only e.g. `F` to be fully faithful when
really this means `F` and `R` both must be.
-/

@[expose] public section

open CategoryTheory Limits Functor Adjunction Triple

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (L : C ⥤ D) (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C)

/-- Structure containing the three adjunctions of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
/-
**CategoryTheory.Adjunction.Quadruple** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Functor C D →           CategoryTheory.Functor D C →             Category
Theory.Functor C D → CategoryTheory.Functor D C → Type (max (max (max u₁ u₂) v₁)
 v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the three adjunctions of an adjoint quadruple `L ⊣ F ⊣ G ⊣ 
R`.
-/
structure CategoryTheory.Adjunction.Quadruple where
  /-- Adjunction `L ⊣ F` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₁ : L ⊣ F
  /-- Adjunction `F ⊣ G` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₂ : F ⊣ G
  /-- Adjunction `G ⊣ R` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₃ : G ⊣ R

namespace CategoryTheory.Adjunction.Quadruple

variable {L F G R} (q : Quadruple L F G R)

/-- The left part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
/-
**CategoryTheory.Adjunction.Quadruple.leftTriple** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Adjunction.Quadruple`。
形式化陈述：leftTriple : Triple L F G where adj₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`.
-/
def leftTriple : Triple L F G where
  adj₁ := q.adj₁
  adj₂ := q.adj₂

/-- The right part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
/-
**CategoryTheory.Adjunction.Quadruple.rightTriple** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Adjunction.Quadruple`。
形式化陈述：rightTriple : Triple F G R where adj₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`.
-/
def rightTriple : Triple F G R where
  adj₁ := q.adj₂
  adj₂ := q.adj₃

/-- The adjoint quadruple `R.op ⊣ G.op ⊣ F.op ⊣ L.op` dual to an
adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
/-
**CategoryTheory.Adjunction.Quadruple.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Adjunction.Quadruple`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {L : Cat
egoryTheory.Functor C D} →           {F : CategoryTheory.Functor D C} →         
    {G : CategoryTheory.Functor C D} →               {R : CategoryTheory.Functor
 D C} →                 CategoryTheory.Adjunction.Quadruple L F G R → CategoryTh
eory.Adjunction.Quadruple R.op G.op F.op L.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint quadruple `R.op ⊣ G.op ⊣ F.op ⊣ L.op` dual to an
adjoint quadruple `L ⊣ F ⊣ G ⊣ R`.
-/
protected def op : Quadruple R.op G.op F.op L.op where
  adj₁ := q.adj₃.op
  adj₂ := q.adj₂.op
  adj₃ := q.adj₁.op

@[simp]
/-
**CategoryTheory.Adjunction.Quadruple.op_leftTriple** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Adjunction.Quadruple`。
形式化陈述：op_leftTriple : q.op.leftTriple = q.rightTriple.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_leftTriple : q.op.leftTriple = q.rightTriple.op := rfl

@[simp]
/-
**CategoryTheory.Adjunction.Quadruple.op_rightTriple** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Adjunction.Quadruple`。
形式化陈述：op_rightTriple : q.op.rightTriple = q.leftTriple.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_rightTriple : q.op.rightTriple = q.leftTriple.op := rfl

section RightFullyFaithful

variable [F.Full] [F.Faithful]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` (and hence also `R`) is fully faithful, all
components of the natural transformation `G ⟶ L` are epimorphisms iff all components of the natural
transformation `F ⟶ R` are monomorphisms. -/
/-
**CategoryTheory.Adjunction.Quadruple.epi_leftTriple_rightToLeft_app_iff_mono_ri
ghtTriple_leftToRight_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Q
uadruple`。
形式化陈述：epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app : (for
all X, Epi (q.leftTriple.rightToLeft.app X)) ↔ forall X, Mono (q.rightTriple.lef
tToRight.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Adjunction.Triple.rightToLeft_eq_counits`：rightToLeft_eq_
counits : t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerLeft H t.adj₁.counit) 
≫ (Functor.associator _ _ _).inv ≫ whiskerRig…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Adjunction.homEquiv_symm_id`：homEquiv_symm_id (X : D) : (
adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right_symm`：homEquiv_natur
ality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') : (adj.homEquiv X Y').symm (f ≫ 
G.map g) = (adj.homEquiv X Y).symm f ≫ g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `CategoryTheory.Adjunction.homEquiv_id`：homEquiv_id (X : C) : adj.homEqui
v X _ (𝟙 _) = adj.unit.app X
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` (and hence also `R`) is fully
 faithful, all
components of the natural transformation `G ⟶ L` are epimorphisms iff all compon
ents of the natural
transformation `F ⟶ R` are monomorphisms.
-/
lemma epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app :
    (∀ X, Epi (q.leftTriple.rightToLeft.app X)) ↔ ∀ X, Mono (q.rightTriple.leftToRight.app X) := by
  simp_rw [mono_leftToRight_app_iff_mono_adj₂_unit_app, rightToLeft_eq_counits]
  dsimp
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_comp_iff_of_epi, epi_iff_forall_injective, mono_iff_forall_injective]
  rw [forall_comm]
  refine forall_congr' fun X ↦ forall_congr' fun Y ↦ ?_
  rw [← (q.adj₁.homEquiv _ _).comp_injective _]
  simp_rw [Function.comp_def, q.adj₁.homEquiv_naturality_left]
  refine ((q.adj₁.homEquiv _ _).injective_comp fun f ↦ _).trans ?_
  rw [← ((q.adj₂.homEquiv _ _).trans (q.adj₃.homEquiv _ _)).comp_injective _]
  simp [Function.comp_def, ← q.adj₂.homEquiv_symm_id, ← q.adj₂.homEquiv_naturality_right_symm,
    ← q.adj₃.homEquiv_id, ← q.adj₃.homEquiv_naturality_left]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` (and hence also `R`) is fully faithful and
its domain / codomain has all pushouts resp. pullbacks, the natural transformation `G ⟶ L` is an
epimorphism iff the natural transformation `F ⟶ R` is a monomorphism. -/
/-
**CategoryTheory.Adjunction.Quadruple.epi_leftTriple_rightToLeft_iff_mono_rightT
riple_leftToRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Quadruple
`。
形式化陈述：epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight [HasPullbacks 
C] [HasPushouts D] : Epi q.leftTriple.rightToLeft ↔ Mono q.rightTriple.leftToRig
ht
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.epi_iff_epi_app`：∀ {K : Type u} [inst : Category
Theory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.mono_iff_mono_app`：∀ {K : Type u} [inst : Catego
ryTheory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v',
 u'} C]   {F G : CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.Quadruple.epi_leftTriple_rightToLeft_app_iff_m
ono_rightTriple_leftToRight_app`：epi_leftTriple_rightToLeft_app_iff_mono_rightTr
iple_leftToRight_app : (forall X, Epi (q.leftTriple.rightToLeft.app X)) ↔ forall
 X, Mono (q.r…

--- 原说明 ---
For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` (and hence also `R`) is fully
 faithful and
its domain / codomain has all pushouts resp. pullbacks, the natural transformati
on `G ⟶ L` is an
epimorphism iff the natural transformation `F ⟶ R` is a monomorphism.
-/
lemma epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.rightToLeft ↔ Mono q.rightTriple.leftToRight := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app

end RightFullyFaithful

section LeftFullyFaithful

variable [L.Full] [L.Faithful] [G.Full] [G.Faithful]

set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, all components
of the natural transformation `L ⟶ G` are epimorphisms iff all components of the natural
transformation `R ⟶ F` are monomorphisms. -/
/-
**CategoryTheory.Adjunction.Quadruple.epi_leftTriple_leftToRight_app_iff_mono_ri
ghtTriple_rightToLeft_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Q
uadruple`。
形式化陈述：epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app : (for
all X, Epi (q.leftTriple.leftToRight.app X)) ↔ forall X, Mono (q.rightTriple.rig
htToLeft.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Adjunction.Quadruple.epi_leftTriple_rightToLeft_app_iff_m
ono_rightTriple_leftToRight_app`：epi_leftTriple_rightToLeft_app_iff_mono_rightTr
iple_leftToRight_app : (forall X, Epi (q.leftTriple.rightToLeft.app X)) ↔ forall
 X, Mono (q.r…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Adjunction.Triple.leftToRight_op`：leftToRight_op : t.op.l
eftToRight = NatTrans.op t.leftToRight
· 使用引理 `CategoryTheory.Adjunction.Triple.op_rightToLeft`：op_rightToLeft : t.op.r
ightToLeft = NatTrans.op t.rightToLeft
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b

--- 原说明 ---
For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, a
ll components
of the natural transformation `L ⟶ G` are epimorphisms iff all components of the
 natural
transformation `R ⟶ F` are monomorphisms.
-/
lemma epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app :
    (∀ X, Epi (q.leftTriple.leftToRight.app X)) ↔ ∀ X, Mono (q.rightTriple.rightToLeft.app X) := by
  have h := q.op.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simpa using h.symm

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful and their domain
and codomain have all pullbacks resp. pushouts, the natural transformation `L ⟶ G` is an
epimorphism iff the natural transformation `R ⟶ F` is a monomorphism. -/
/-
**CategoryTheory.Adjunction.Quadruple.epi_leftTriple_leftToRight_iff_mono_rightT
riple_rightToLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Quadruple
`。
形式化陈述：epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft [HasPullbacks 
C] [HasPushouts D] : Epi q.leftTriple.leftToRight ↔ Mono q.rightTriple.rightToLe
ft
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.epi_iff_epi_app`：∀ {K : Type u} [inst : Category
Theory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.mono_iff_mono_app`：∀ {K : Type u} [inst : Catego
ryTheory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v',
 u'} C]   {F G : CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.Quadruple.epi_leftTriple_leftToRight_app_iff_m
ono_rightTriple_rightToLeft_app`：epi_leftTriple_leftToRight_app_iff_mono_rightTr
iple_rightToLeft_app : (forall X, Epi (q.leftTriple.leftToRight.app X)) ↔ forall
 X, Mono (q.r…

--- 原说明 ---
For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful an
d their domain
and codomain have all pullbacks resp. pushouts, the natural transformation `L ⟶ 
G` is an
epimorphism iff the natural transformation `R ⟶ F` is a monomorphism.
-/
lemma epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.leftToRight ↔ Mono q.rightTriple.rightToLeft := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app

end LeftFullyFaithful

end CategoryTheory.Adjunction.Quadruple

