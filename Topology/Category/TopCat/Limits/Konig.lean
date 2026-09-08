/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limitCone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [Preorder J] [IsDirectedOrder J]` and
`F : Jᵒᵖ ⥤ TopCat`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in lemmas `nonempty_sections_of_finite_cofiltered_system` and
`nonempty_sections_of_finite_inverse_system` in `Mathlib/CategoryTheory/CofilteredSystem.lean`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/

@[expose] public section

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

section TopologicalKonig

variable {J : Type u} [SmallCategory J]

variable (F : J ⥤ TopCat.{v})

set_option backward.privateInPublic true in
/-
**TopCat.FiniteDiagramArrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private abbrev FiniteDiagramArrow {J : Type u} [SmallCategory J] (G : Finset J) :=
  Σ' (X Y : J) (_ : X ∈ G) (_ : Y ∈ G), X ⟶ Y

set_option backward.privateInPublic true in
/-
**TopCat.FiniteDiagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private abbrev FiniteDiagram (J : Type u) [SmallCategory J] :=
  Σ G : Finset J, Finset (FiniteDiagramArrow G)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
/-
**TopCat.partialSections** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：partialSections {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{v}) {G : F
inset J} (H : Finset (FiniteDiagramArrow G)) : Set (forall j, F.obj j)
参数：F : J ⥤ TopCat.{v}；H : Finset (FiniteDiagramArrow G)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partialSections {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{v}) {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : Set (∀ j, F.obj j) :=
  {u | ∀ {f : FiniteDiagramArrow G} (_ : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopCat.partialSections.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.partialSecti
ons`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.SmallCategory J] (F : CategoryTheory
.Functor J TopCat)   [CategoryTheory.IsCofilteredOrEmpty J] [h : ∀ (j : J), None
mpty ↑(F.obj j)] {G : Finset J}   (H : Finset (TopCat.FiniteDiagramArrow✝ G)), (
TopCat.partialSections F H).Nonempty
参数：F : CategoryTheory.Functor J TopCat；j : J；F.obj j；H : Finset (TopCat.FiniteDi
agramArrow✝ G)；TopCat.partialSections F H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.comp_app`：comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (
x : X) : (f ≫ g : X -> Z) x = g (f x)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsCofiltered.infTo_commutes`：infTo_commutes {X Y : C} (mX
 : X in O) (mY : Y in O) {f : X ⟶ Y} (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ 
: X in O) (_ : Y in O), X ⟶ Y) i…
-/
theorem partialSections.nonempty [IsCofilteredOrEmpty J] [h : ∀ j : J, Nonempty (F.obj j)]
    {G : Finset J} (H : Finset (FiniteDiagramArrow G)) : (partialSections F H).Nonempty := by
  classical
  cases isEmpty_or_nonempty J
  · exact ⟨isEmptyElim, fun {j} => IsEmpty.elim' inferInstance j.1⟩
  have : IsCofiltered J := ⟨⟩
  use fun j : J =>
    if hj : j ∈ G then F.map (IsCofiltered.infTo G H hj) (h (IsCofiltered.inf G H)).some
    else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ hf
  dsimp only
  rwa [dif_pos hX, dif_pos hY, ← comp_app, ← F.map_comp, @IsCofiltered.infTo_commutes _ _ _ G H]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopCat.partialSections.directed** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.partialSecti
ons`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.SmallCategory J] (F : CategoryTheory
.Functor J TopCat),   Directed GE.ge fun G => TopCat.partialSections F G.snd
参数：F : CategoryTheory.Functor J TopCat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
theorem partialSections.directed :
    Directed GE.ge fun G : FiniteDiagram J => partialSections F G.2 := by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.1 → FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.1 → FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, ?_, ?_⟩
  · rintro u hu f hf
    have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB := by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    exact hu this
  · rintro u hu f hf
    have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB := by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    exact hu this

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopCat.partialSections.closed** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.partialSection
s`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.SmallCategory J] (F : CategoryTheory
.Functor J TopCat)   [∀ (j : J), T2Space ↑(F.obj j)] {G : Finset J} (H : Finset 
(TopCat.FiniteDiagramArrow✝ G)),   IsClosed (TopCat.partialSections F H)
参数：F : CategoryTheory.Functor J TopCat；j : J；F.obj j；H : Finset (TopCat.FiniteDi
agramArrow✝ G)；TopCat.partialSections F H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem partialSections.closed [∀ j : J, T2Space (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : IsClosed (partialSections F H) := by
  have :
    partialSections F H =
      ⋂ (f : FiniteDiagramArrow G) (_ : f ∈ H), {u | F.map f.2.2.2.2 (u f.1) = u f.2.1} := by
    ext1
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [this]
  apply isClosed_biInter
  intro f _
  apply isClosed_eq <;> fun_prop

/-- Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
-/
/-
**TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system** 是 Mathlib 中的一个定理，位
于命名空间 `TopCat`。
形式化陈述：nonempty_limitCone_of_compact_t2_cofiltered_system (F : J ⥤ TopCat.{max v 
u}) [IsCofilteredOrEmpty J] [forall j : J, Nonempty (F.obj j)] [forall j : J, Co
mpactSpace (F.obj j)] [forall j : J, T2Space (F.obj j)] : Nonempty (TopCat.limit
Cone F).pt
参数：F : J ⥤ TopCat.{max v u}；F.obj j；F.obj j；F.obj j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `TopCat.partialSections.directed`：∀ {J : Type u} [inst : CategoryTheory.S
mallCategory J] (F : CategoryTheory.Functor J TopCat),   Directed GE.ge fun G =>
 TopCat.partialSectio…
· 使用定理 `TopCat.partialSections.nonempty`：∀ {J : Type u} [inst : CategoryTheory.S
mallCategory J] (F : CategoryTheory.Functor J TopCat)   [CategoryTheory.IsCofilt
eredOrEmpty J] [h : ∀…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `TopCat.partialSections.closed`：∀ {J : Type u} [inst : CategoryTheory.Sma
llCategory J] (F : CategoryTheory.Functor J TopCat)   [∀ (j : J), T2Space ↑(F.ob
j j)] {G : Finset J…
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)

--- 原说明 ---
Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological 
spaces.
-/
theorem nonempty_limitCone_of_compact_t2_cofiltered_system (F : J ⥤ TopCat.{max v u})
    [IsCofilteredOrEmpty J]
    [∀ j : J, Nonempty (F.obj j)] [∀ j : J, CompactSpace (F.obj j)] [∀ j : J, T2Space (F.obj j)] :
    Nonempty (TopCat.limitCone F).pt := by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun G => partialSections F _)
      (partialSections.directed F) (fun G => partialSections.nonempty F _)
      (fun G => IsClosed.isCompact (partialSections.closed F _)) fun G =>
      partialSections.closed F _
  use u
  intro X Y f
  let G : FiniteDiagram J := ⟨{X, Y}, {⟨X, Y, by grind, by grind, f⟩}⟩
  exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)

end TopologicalKonig

end TopCat

