/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Presheaves on `PUnit`

Presheaves on `PUnit` satisfy sheaf condition iff its value at empty set is a terminal object.
-/

public section


namespace TopCat.Presheaf

universe u v w

open CategoryTheory CategoryTheory.Limits TopCat Opposite

variable {C : Type u} [Category.{v} C]

/-
**TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 
`TopCat.Presheaf`。
形式化陈述：isSheaf_of_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F
 : Presheaf C X) (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf
参数：hind : X.str = ⊤；F : Presheaf C X；it : IsTerminal <| F.obj <| op ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `existsUnique_iff_exists`：∀ {α : Sort u_1} [Subsingleton α] {p : α → Prop
}, (∃! x, p x) ↔ ∃ x, p x
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `CategoryTheory.Sieve.arrows_eq_top_iff`：arrows_eq_top_iff {S : Sieve X} 
: S.arrows = ⊤ ↔ S = ⊤
· 使用定理 `CategoryTheory.Sieve.id_mem_iff_eq_top`：id_mem_iff_eq_top : S (𝟙 X) ↔ S 
= ⊤
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `TopologicalSpace.Opens.eq_bot_or_top`：eq_bot_or_top [IndiscreteTopology 
α] (U : Opens α) : U = ⊥ ∨ U = ⊤
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.Presieve.isSheafFor_top`：isSheafFor_top (P : Cᵒᵖ ⥤ Type w
) : IsSheafFor P (⊤ : Presieve X)
-/
theorem isSheaf_of_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X)
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf := fun c U s hs => by
  have : IndiscreteTopology X := ⟨hind⟩
  obtain rfl | hne := eq_or_ne U ⊥
  · intro _ _
    rw [@existsUnique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine ⟨it.from _, fun U hU hs => IsTerminal.hom_ext ?_ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert! Presieve.isSheafFor_top (F ⋙ coyoneda.obj (@op C c))
    rw [Sieve.arrows_eq_top_iff, ← Sieve.id_mem_iff_eq_top]
    have := U.eq_bot_or_top.resolve_left hne
    subst this
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    · exact (hne <| SetLike.ext'_iff.2 <| Set.univ_eq_empty_iff.2 he).elim
    obtain ⟨U, f, hf, hm⟩ := hs x _root_.trivial
    obtain rfl | rfl := U.eq_bot_or_top
    · cases hm
    · convert! hf
/-
**TopCat.Presheaf.isSheaf_iff_isTerminal_of_indiscrete** 是 Mathlib 中的一个定理，位于命名空间
 `TopCat.Presheaf`。
形式化陈述：isSheaf_iff_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (
F : Presheaf C X) : F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥)
参数：hind : X.str = ⊤；F : Presheaf C X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete`：isSheaf_of_isTermin
al_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X) (it : Is
Terminal <| F.obj <| op ⊥) : F.IsSheaf
-/
theorem isSheaf_iff_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤)
    (F : Presheaf C X) : F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ =>
    isSheaf_of_isTerminal_of_indiscrete hind F it⟩
/-
**TopCat.Presheaf.isSheaf_on_punit_of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `TopC
at.Presheaf`。
形式化陈述：isSheaf_on_punit_of_isTerminal (F : Presheaf C (TopCat.of PUnit)) (it : Is
Terminal <| F.obj <| op ⊥) : F.IsSheaf
参数：F : Presheaf C (TopCat.of PUnit)；it : IsTerminal <| F.obj <| op ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete`：isSheaf_of_isTermin
al_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X) (it : Is
Terminal <| F.obj <| op ⊥) : F.IsSheaf
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem isSheaf_on_punit_of_isTerminal (F : Presheaf C (TopCat.of PUnit))
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf :=
  isSheaf_of_isTerminal_of_indiscrete (@Subsingleton.elim (TopologicalSpace PUnit) _ _ _) F it
/-
**TopCat.Presheaf.isSheaf_on_punit_iff_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `Top
Cat.Presheaf`。
形式化陈述：isSheaf_on_punit_iff_isTerminal (F : Presheaf C (TopCat.of PUnit)) : F.IsS
heaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥)
参数：F : Presheaf C (TopCat.of PUnit)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.isSheaf_on_punit_of_isTerminal`：isSheaf_on_punit_of_isTe
rminal (F : Presheaf C (TopCat.of PUnit)) (it : IsTerminal <| F.obj <| op ⊥) : F
.IsSheaf
-/
theorem isSheaf_on_punit_iff_isTerminal (F : Presheaf C (TopCat.of PUnit)) :
    F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => isSheaf_on_punit_of_isTerminal F it⟩

end TopCat.Presheaf

