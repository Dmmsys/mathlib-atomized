/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Cocontinuous functors between sites.

We define cocontinuous functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cover-lifting* or
*cover-reflecting functors*. We use the original terminology and definition of SGA 4 III 2.1.
However, the notion of cocontinuous functor should not be confused with
the general definition of cocontinuous functors between categories as functors preserving
small colimits.

## Main definitions

* `CategoryTheory.Functor.IsCocontinuous`: a functor between sites is cocontinuous if it
  pulls back covering sieves to covering sieves
* `CategoryTheory.Functor.sheafPushforwardCocontinuous`: A cocontinuous functor
  `G : (C, J) ⥤ (D, K)` induces a functor `Sheaf J A ⥤ Sheaf K A`.

## Main results
* `CategoryTheory.ran_isSheaf_of_isCocontinuous`: If `G : C ⥤ D` is cocontinuous, then
  `G.op.ran` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.
* `CategoryTheory.Functor.sheafAdjunctionCocontinuous`: If `G : (C, J) ⥤ (D, K)` is cocontinuous
  and continuous, then `G.sheafPushforwardContinuous A J K` and
  `G.sheafPushforwardCocontinuous A J K` are adjoint.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/

@[expose] public section


universe w' w v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

section IsCocontinuous

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E] (G : C ⥤ D)
  (G' : D ⥤ E)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called cocontinuous (SGA 4 III 2.1)
if for all covering sieves `R` in `D`, `R.pullback G` is a covering sieve in `C`.
-/
/-
**CategoryTheory.Functor.IsCocontinuous** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D →           CategoryTheory.GrothendieckTopology C → Cat
egoryTheory.GrothendieckTopology D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : (C, J) ⥤ (D, K)` between sites is called cocontinuous (SGA 4 III 
2.1)
if for all covering sieves `R` in `D`, `R.pullback G` is a covering sieve in `C`
.
-/
class Functor.IsCocontinuous : Prop where
  cover_lift : ∀ {U : C} {S : Sieve (G.obj U)} (_ : S ∈ K (G.obj U)), S.functorPullback G ∈ J U
/-
**CategoryTheory.Functor.cover_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : CategoryTheory.Functo
r C D)   (J : CategoryTheory.GrothendieckTopology C) (K : CategoryTheory.Grothen
dieckTopology D) [G.IsCocontinuous J K] {U : C}   {S : CategoryTheory.Sieve (G.o
bj U)}, S ∈ K (G.obj U) → CategoryTheory.Sieve.functorPullback G S ∈ J U
参数：G : CategoryTheory.Functor C D；J : CategoryTheory.GrothendieckTopology C；K : 
CategoryTheory.GrothendieckTopology D；G.obj U；G.obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocontinuous.cover_lift`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D} {G : Categor…
-/
lemma Functor.cover_lift [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
    (hS : S ∈ K (G.obj U)) : S.functorPullback G ∈ J U :=
  IsCocontinuous.cover_lift hS

/-- The identity functor on a site is cocontinuous. -/
/-
**CategoryTheory.isCocontinuous_id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isCocontinuous_id : Functor.IsCocontinuous (𝟭 C) J J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPullback_id`：functorPullback_id (R : Sieve X
) : R.functorPullback (𝟭 _) = R

--- 原说明 ---
The identity functor on a site is cocontinuous.
-/
instance isCocontinuous_id : Functor.IsCocontinuous (𝟭 C) J J :=
  ⟨fun h => by simpa using! h⟩

/-- The composition of two cocontinuous functors is cocontinuous. -/
/-
**CategoryTheory.isCocontinuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCocontinuous_comp [G.IsCocontinuous J K] [G'.IsCocontinuous K L] : (G ⋙ 
G').IsCocontinuous J L where cover_lift h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…

--- 原说明 ---
The composition of two cocontinuous functors is cocontinuous.
-/
theorem isCocontinuous_comp [G.IsCocontinuous J K] [G'.IsCocontinuous K L] :
    (G ⋙ G').IsCocontinuous J L where
  cover_lift h := G.cover_lift J K (G'.cover_lift K L h)

variable {J K} in
/-
**CategoryTheory.Functor.IsCocontinuous.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsCocontinuous`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {J : CategoryTheory.Grothe
ndieckTopology C}   {K : CategoryTheory.GrothendieckTopology D} {F G : CategoryT
heory.Functor C D} (e : F ≅ G) [F.IsCocontinuous J K],   G.IsCocontinuous J K
参数：e : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
lemma Functor.IsCocontinuous.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsCocontinuous J K] :
    G.IsCocontinuous J K where
  cover_lift {U} S hS := by
    refine J.superset_covering ?_ (F.cover_lift J K (K.pullback_stable (e.hom.app U) hS))
    intro Y f (hf : S.arrows (F.map f ≫ e.hom.app U))
    have := S.downward_closed hf (e.inv.app Y)
    rwa [e.hom.naturality f, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at this

variable {J K} in
/-
**CategoryTheory.Functor.IsCocontinuous.iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.IsCocontinuous`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {J : CategoryTheory.Grothe
ndieckTopology C}   {K : CategoryTheory.GrothendieckTopology D} {F G : CategoryT
heory.Functor C D} (e : F ≅ G),   F.IsCocontinuous J K ↔ G.IsCocontinuous J K
参数：e : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocontinuous.of_iso`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] {J : Categor…
-/
lemma Functor.IsCocontinuous.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsCocontinuous J K ↔ G.IsCocontinuous J K :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩
/-
**CategoryTheory.CoverPreserving.of_comp_of_isCocontinuous** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.CoverPreserving`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {E : Type u_3} [inst_2 : C
ategoryTheory.Category.{v_3, u_3} E]   (J : CategoryTheory.GrothendieckTopology 
C) (K : CategoryTheory.GrothendieckTopology D)   {L : CategoryTheory.Grothendiec
kTopology E} {F : CategoryTheory.Functor C D} (G : CategoryTheory.Functor D E), 
  CategoryTheory.CoverPreserving J L (F.comp G) →     ∀ [G.IsCocontinuous K L] [
G.Full] [G.Faithful], CategoryTheory.CoverPreserving J K F
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPushforward_comp`：functorPushforward_comp (R
 : Sieve X) : R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPus
hforward G
· 使用引理 `CategoryTheory.Sieve.functorPullback_functorPushforward_eq`：functorPullb
ack_functorPushforward_eq {X : C} {S : Sieve X} [F.Full] [F.Faithful] : Sieve.fu
nctorPullback F (Sieve.functorPushforward F S) =…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
-/
lemma CoverPreserving.of_comp_of_isCocontinuous {F : C ⥤ D} (G : D ⥤ E)
    (h : CoverPreserving J L (F ⋙ G)) [G.IsCocontinuous K L] [G.Full] [G.Faithful] :
    CoverPreserving J K F where
  cover_preserve {U} S hS := by
    refine K.superset_covering ?_ (G.cover_lift K _ (h.cover_preserve hS))
    rw [Sieve.functorPushforward_comp, Sieve.functorPullback_functorPushforward_eq G]

section

variable {F : C ⥤ D} {G : D ⥤ C}

/-
**CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (J : CategoryTheory.Grothe
ndieckTopology C)   (K : CategoryTheory.GrothendieckTopology D) {F : CategoryThe
ory.Functor C D} {G : CategoryTheory.Functor D C}   (adj : F ⊣ G), F.IsCocontinu
ous J K ↔ CategoryTheory.CoverPreserving K J G
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.IsCocontinuous.cover_lift`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D} {G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`：homEquiv_natura
lity_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) : (adj.homEquiv X' Y).symm (f ≫ g)
 = F.map f ≫ (adj.homEquiv X Y).symm g
· 使用引理 `CategoryTheory.Adjunction.homEquiv_symm_unit`：homEquiv_symm_unit (X : C)
 : dsimp% (adj.homEquiv _ _).symm (adj.unit.app X) = 𝟙 _
· 使用定理 `CategoryTheory.Sieve.functorPullback_apply`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
-/
lemma Adjunction.isCocontinuous_iff_coverPreserving (adj : F ⊣ G) :
    F.IsCocontinuous J K ↔ CoverPreserving K J G := by
  refine ⟨fun h ↦ ⟨?_⟩, fun h ↦ ⟨?_⟩⟩
  · intro U S hS
    refine J.superset_covering ?_ <| h.cover_lift (K.pullback_stable (adj.counit.app _) hS)
    intro X f hf
    refine ⟨F.obj X, F.map f ≫ adj.counit.app _, adj.unit.app _, hf, by simp⟩
  · intro U S hS
    refine J.superset_covering ?_ (J.pullback_stable (adj.unit.app U) <| h.cover_preserve hS)
    intro X f ⟨Y, g, u, hg, heq⟩
    suffices F.map f = (adj.homEquiv _ _).symm u ≫ g by
      simp [this, S.downward_closed hg]
    simp [← Adjunction.homEquiv_naturality_right_symm, ← heq,
      Adjunction.homEquiv_naturality_left_symm]
/-
**CategoryTheory.Adjunction.isContinuous_of_isCocontinuous** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Adjunction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (J : CategoryTheory.Grothe
ndieckTopology C)   (K : CategoryTheory.GrothendieckTopology D) {F : CategoryThe
ory.Functor C D} {G : CategoryTheory.Functor D C}   (adj : F ⊣ G) [F.IsCocontinu
ous J K], G.IsContinuous K J
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isContinuous_of_coverPreserving`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.compatiblePreservingOfFlat`：compatiblePreservingOfFlat {C
 : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (K : GrothendieckT
opology D) (G : C ⥤ D) [Represe…
· 使用定理 `CategoryTheory.RepresentablyFlat.of_isRightAdjoint`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} D] (J : Categor…
-/
lemma Adjunction.isContinuous_of_isCocontinuous (adj : F ⊣ G) [F.IsCocontinuous J K] :
    G.IsContinuous K J := by
  have := adj.isRightAdjoint
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat J G)
  rwa [← adj.isCocontinuous_iff_coverPreserving]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsCocontinuous J K] [F.IsLeftAdjoint] : F.rightAdjoint.IsContinuous K J :=
  (Adjunction.ofIsLeftAdjoint F).isContinuous_of_isCocontinuous J K

end

end IsCocontinuous

/-!
We will now prove that `G.op.ran : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` maps sheaves
to sheaves when `G : C ⥤ D` is a cocontinuous functor.

We do not follow the proofs in SGA 4 III 2.2 or <https://stacks.math.columbia.edu/tag/00XK>.
Instead, we verify as directly as possible that if `F : Cᵒᵖ ⥤ A` is a sheaf,
then `G.op.ran.obj F` is a sheaf. In order to do this, we use the "multifork"
characterization of sheaves which involves limits in the category `A`.
As `G.op.ran.obj F` is the chosen right Kan extension of `F` along `G.op : Cᵒᵖ ⥤ Dᵒᵖ`,
we actually verify that any pointwise right Kan extension of `F` along `G.op` is a sheaf.

-/

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
variable {A : Type w} [Category.{w'} A]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsCocontinuous J K]

namespace RanIsSheafOfIsCocontinuous

variable {G}
variable {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F)
variable {R : Dᵒᵖ ⥤ A} (α : G.op ⋙ R ⟶ F)
variable (hR : (Functor.RightExtension.mk _ α).IsPointwiseRightKanExtension)
variable {X : D} {S : K.Cover X} (s : Multifork (S.index R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `lift`. -/
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：liftAux {Y : C} (f : G.obj Y ⟶ X) : s.pt ⟶ F.obj (op Y)
参数：f : G.obj Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `lift`.
-/
def liftAux {Y : C} (f : G.obj Y ⟶ X) : s.pt ⟶ F.obj (op Y) :=
  Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k ↦ s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      intro { fst := ⟨Y₁, p₁, hp₁⟩, snd := ⟨Y₂, p₂, hp₂⟩, r := ⟨W, g₁, g₂, w⟩ }
      dsimp at g₁ g₂ w ⊢
      simp only [Category.assoc, ← α.naturality, Functor.comp_map,
        Functor.op_map, Quiver.Hom.unop_op]
      apply s.condition_assoc
        { fst.hf := hp₁
          snd.hf := hp₂
          r.g₁ := G.map g₁
          r.g₂ := G.map g₂
          r.w := by simpa using G.congr_map w =≫ f
          .. })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.liftAux_map** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：liftAux_map {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow) (h
 : G.obj W ⟶ i.Y) (w : h ≫ i.f = G.map g ≫ f) : liftAux hF α s f ≫ F.map g.op = 
s.ι i ≫ R.map h.op ≫ α.app _
参数：f : G.obj Y ⟶ X；g : W ⟶ Y；i : S.Arrow；h : G.obj W ⟶ i.Y；w : h ≫ i.f = G.map g
 ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `CategoryTheory.Limits.Multifork.IsLimit.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   {I 
: CategoryTheory.Limits.Multicosp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Multifork.condition`：condition (b) : K.ι (J.fst b)
 ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
-/
lemma liftAux_map {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow)
    (h : G.obj W ⟶ i.Y) (w : h ≫ i.f = G.map g ≫ f) :
    liftAux hF α s f ≫ F.map g.op = s.ι i ≫ R.map h.op ≫ α.app _ :=
  (Multifork.IsLimit.fac
    (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩) _ _
      ⟨W, g, by simpa only [Sieve.functorPullback_apply, functorPullback_mem,
        Sieve.pullback_apply, ← w] using S.1.downward_closed i.hf h⟩).trans (by
        dsimp
        simp only [← Category.assoc]
        congr 1
        let r : S.Relation :=
          { fst.f := G.map g ≫ f
            fst.hf := by simpa only [← w] using S.1.downward_closed i.hf h
            snd := i
            r.g₁ := 𝟙 _
            r.g₂ := h
            r.w := by simpa using w.symm
            .. }
        simpa [r] using s.condition r)
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.liftAux_map'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：liftAux_map' {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C} (a :
 W ⟶ Y) (b : W ⟶ Y') (w : G.map a ≫ f = G.map b ≫ f') : liftAux hF α s f ≫ F.map
 a.op = liftAux hF α s f' ≫ F.map b.op
参数：f : G.obj Y ⟶ X；f' : G.obj Y' ⟶ X；a : W ⟶ Y；b : W ⟶ Y'；w : G.map a ≫ f = G.ma
p b ≫ f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `CategoryTheory.RanIsSheafOfIsCocontinuous.liftAux_map`：liftAux_map {Y : 
C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow) (h : G.obj W ⟶ i.Y) (w : 
h ≫ i.f = G.map g ≫ f) : liftAux hF α s f ≫…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma liftAux_map' {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C}
    (a : W ⟶ Y) (b : W ⟶ Y') (w : G.map a ≫ f = G.map b ≫ f') :
    liftAux hF α s f ≫ F.map a.op = liftAux hF α s f' ≫ F.map b.op := by
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable (G.map a ≫ f) S.2)⟩
  rintro ⟨T, g, hg⟩
  dsimp
  have eq₁ := liftAux_map hF α s f (g ≫ a) ⟨_, _, hg⟩ (𝟙 _) (by simp)
  have eq₂ := liftAux_map hF α s f' (g ≫ b) ⟨_, _, hg⟩ (𝟙 _) (by simp [w])
  dsimp at eq₁ eq₂
  simp only [Functor.map_comp, Functor.map_id] at eq₁ eq₂
  simp only [Category.assoc, eq₁, eq₂]

variable {α}

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `isLimitMultifork` -/
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.lift** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：lift : s.pt ⟶ R.obj (op X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `isLimitMultifork`
-/
def lift : s.pt ⟶ R.obj (op X) :=
  (hR (op X)).lift (Cone.mk _
    { app := fun j ↦ liftAux hF α s j.hom.unop
      naturality := fun j j' φ ↦ by
        simpa using liftAux_map' hF α s j'.hom.unop j.hom.unop (𝟙 _) φ.right.unop
          (Quiver.Hom.op_inj (by simpa using (StructuredArrow.w φ).symm)) })
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.fac'** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：fac' (j : StructuredArrow (op X) G.op) : lift hF hR s ≫ R.map j.hom ≫ α.ap
p j.right = liftAux hF α s j.hom.unop
参数：j : StructuredArrow (op X) G.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma fac' (j : StructuredArrow (op X) G.op) :
    lift hF hR s ≫ R.map j.hom ≫ α.app j.right = liftAux hF α s j.hom.unop := by
  apply IsLimit.fac

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.fac** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：fac (i : S.Arrow) : lift hF hR s ≫ R.map i.f.op = s.ι i
参数：i : S.Arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用引理 `CategoryTheory.RanIsSheafOfIsCocontinuous.fac'`：fac' (j : StructuredArro
w (op X) G.op) : lift hF hR s ≫ R.map j.hom ≫ α.app j.right = liftAux hF α s j.h
om.unop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.RanIsSheafOfIsCocontinuous.liftAux_map`：liftAux_map {Y : 
C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow) (h : G.obj W ⟶ i.Y) (w : 
h ≫ i.f = G.map g ≫ f) : liftAux hF α s f ≫…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fac (i : S.Arrow) : lift hF hR s ≫ R.map i.f.op = s.ι i := by
  apply (hR (op i.Y)).hom_ext
  intro j
  have eq := fac' hF hR s (StructuredArrow.mk (i.f.op ≫ j.hom))
  dsimp at eq ⊢
  simp only [Functor.map_comp, Category.assoc] at eq
  rw [Category.assoc, eq]
  simpa using liftAux_map hF α s (j.hom.unop ≫ i.f) (𝟙 _) i j.hom.unop (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hR hF in
variable (K) in
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：hom_ext {W : A} {f g : W ⟶ R.obj (op X)} (h : forall (i : S.Arrow), f ≫ R.
map i.f.op = g ≫ R.map i.f.op) : f = g
参数：op X；h : forall (i : S.Arrow), f ≫ R.map i.f.op = g ≫ R.map i.f.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma hom_ext {W : A} {f g : W ⟶ R.obj (op X)}
    (h : ∀ (i : S.Arrow), f ≫ R.map i.f.op = g ≫ R.map i.f.op) : f = g := by
  apply (hR (op X)).hom_ext
  intro j
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable j.hom.unop S.2)⟩
  intro ⟨W, i, hi⟩
  have eq := h (GrothendieckTopology.Cover.Arrow.mk _ (G.map i ≫ j.hom.unop) hi)
  dsimp at eq ⊢
  simp only [Category.assoc, ← NatTrans.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
    Functor.op_map, Quiver.Hom.unop_op]
  rw [reassoc_of% eq]

variable (S)

/-- Auxiliary definition for `ran_isSheaf_of_isCocontinuous` -/
/-
**CategoryTheory.RanIsSheafOfIsCocontinuous.isLimitMultifork** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.RanIsSheafOfIsCocontinuous`。
形式化陈述：isLimitMultifork : IsLimit (S.multifork R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.RanIsSheafOfIsCocontinuous.fac`：fac (i : S.Arrow) : lift 
hF hR s ≫ R.map i.f.op = s.ι i

--- 原说明 ---
Auxiliary definition for `ran_isSheaf_of_isCocontinuous`
-/
def isLimitMultifork : IsLimit (S.multifork R) :=
  Multifork.IsLimit.mk _ (lift hF hR) (fac hF hR)
    (fun s _ hm ↦ hom_ext K hF hR (fun i ↦ (hm i).trans (fac hF hR s i).symm))

end RanIsSheafOfIsCocontinuous

variable (K)
variable [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]

/-- If `G` is cocontinuous, then `G.op.ran` pushes sheaves to sheaves.

This is SGA 4 III 2.2. -/
@[stacks 00XK "Alternative reference. There, results are obtained under the additional assumption
that `C` and `D` have pullbacks."]
/-
**CategoryTheory.ran_isSheaf_of_isCocontinuous** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：ran_isSheaf_of_isCocontinuous (ℱ : Sheaf J A) : Presheaf.IsSheaf K (G.op.r
an.obj ℱ.obj)
参数：ℱ : Sheaf J A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_multifork`：isSheaf_iff_multifork : I
sSheaf J P ↔ forall (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P))
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem ran_isSheaf_of_isCocontinuous (ℱ : Sheaf J A) :
    Presheaf.IsSheaf K (G.op.ran.obj ℱ.obj) := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork ℱ.2
    (G.op.isPointwiseRightKanExtensionRanCounit ℱ.obj) S⟩

variable (A J)

/-- A cocontinuous functor induces a pushforward functor on categories of sheaves. -/
/-
**CategoryTheory.Functor.sheafPushforwardCocontinuous** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (G
 : CategoryTheory.Functor C D) →           (A : Type w) →             [inst_2 : 
CategoryTheory.Category.{w', w} A] →               (J : CategoryTheory.Grothendi
eckTopology C) →                 (K : CategoryTheory.GrothendieckTopology D) →  
                 [G.IsCocontinuous J K] →                     [∀ (F : CategoryTh
eory.Functor Cᵒᵖ A), G.op.HasPointwiseRightKanExtension F] →                    
   CategoryTheory.Functor (CategoryTheory.Sheaf J A) (CategoryTheory.Sheaf K A)
参数：G : CategoryTheory.Functor C D；A : Type w；J : CategoryTheory.GrothendieckTopo
logy C；K : CategoryTheory.GrothendieckTopology D；F : CategoryTheory.Functor Cᵒᵖ 
A；CategoryTheory.Sheaf J A；CategoryTheory.Sheaf K A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ran_isSheaf_of_isCocontinuous`：ran_isSheaf_of_isCocontinu
ous (ℱ : Sheaf J A) : Presheaf.IsSheaf K (G.op.ran.obj ℱ.obj)

--- 原说明 ---
A cocontinuous functor induces a pushforward functor on categories of sheaves.
-/
def Functor.sheafPushforwardCocontinuous : Sheaf J A ⥤ Sheaf K A :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ G.op.ran) (ran_isSheaf_of_isCocontinuous _ K)

/-- `G.sheafPushforwardCocontinuous A J K : Sheaf J A ⥤ Sheaf K A` is induced
by the right Kan extension functor `G.op.ran` on presheaves. -/
@[simps! hom inv]
/-
**CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (G
 : CategoryTheory.Functor C D) →           (A : Type w) →             [inst_2 : 
CategoryTheory.Category.{w', w} A] →               (J : CategoryTheory.Grothendi
eckTopology C) →                 (K : CategoryTheory.GrothendieckTopology D) →  
                 [inst_3 : G.IsCocontinuous J K] →                     [inst_4 :
 ∀ (F : CategoryTheory.Functor Cᵒᵖ A), G.op.HasPointwiseRightKanExtension F] →  
                     (G.sheafPushforwardCocontinuous A J K).comp (CategoryTheory
.sheafToPresheaf K A) ≅                         (CategoryTheory.sheafToPresheaf 
J A).comp G.op.ran
参数：G : CategoryTheory.Functor C D；A : Type w；J : CategoryTheory.GrothendieckTopo
logy C；K : CategoryTheory.GrothendieckTopology D；F : CategoryTheory.Functor Cᵒᵖ 
A；G.sheafPushforwardCocontinuous A J K；CategoryTheory.sheafToPresheaf K A；Catego
ryTheory.sheafToPresheaf J A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.sheafPushforwardCocontinuous A J K : Sheaf J A ⥤ Sheaf K A` is induced
by the right Kan extension functor `G.op.ran` on presheaves.
-/
def Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso :
    G.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ G.op.ran := Iso.refl _

/-

Given a cocontinuous functor `G`, the precomposition with `G.op` induces a functor
on presheaves with leads to a "pullback" functor `Sheaf K A ⥤ Sheaf J A` (TODO: formalize
this as `G.sheafPullbackCocontinuous A J K`) using the associated sheaf functor.
It is shown in SGA 4 III 2.3 that this pullback functor is
left adjoint to `G.sheafPushforwardCocontinuous A J K`. This adjunction may replace
`Functor.sheafAdjunctionCocontinuous` below, and then, it could be shown that if
`G` is also continuous, then we have an isomorphism
`G.sheafPullbackCocontinuous A J K ≅ G.sheafPushforwardContinuous A J K` (TODO).

-/

namespace Functor

variable [G.IsContinuous J K]

/--
Given a functor between sites that is continuous and cocontinuous,
the pushforward for the continuous functor `G` is left adjoint to
the pushforward for the cocontinuous functor `G`. -/
/-
**CategoryTheory.Functor.sheafAdjunctionCocontinuous** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：sheafAdjunctionCocontinuous : G.sheafPushforwardContinuous A J K ⊣ G.sheaf
PushforwardCocontinuous A J K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor between sites that is continuous and cocontinuous,
the pushforward for the continuous functor `G` is left adjoint to
the pushforward for the cocontinuous functor `G`.
-/
noncomputable def sheafAdjunctionCocontinuous :
    G.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardCocontinuous A J K :=
  (G.op.ranAdjunction A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm
/-
**CategoryTheory.Functor.sheafAdjunctionCocontinuous_unit_app_hom** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：sheafAdjunctionCocontinuous_unit_app_hom (F : Sheaf K A) : ((G.sheafAdjunc
tionCocontinuous A J K).unit.app F).hom = (G.op.ranAdjunction A).unit.app F.obj
参数：F : Sheaf K A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app`：map_restri
ctFullyFaithful_unit_app (X : C) : iC.map ((adj.restrictFullyFaithful hiC hiD co
mm1 comm2).unit.app X) = adj.unit.app (iC.obj X) ≫…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sheafAdjunctionCocontinuous_unit_app_hom (F : Sheaf K A) :
    ((G.sheafAdjunctionCocontinuous A J K).unit.app F).hom =
      (G.op.ranAdjunction A).unit.app F.obj := by
  apply ((G.op.ranAdjunction A).map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
  dsimp
  erw [Functor.map_id]
  change _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]

@[deprecated (since := "2026-03-05")]
alias sheafAdjunctionCocontinuous_unit_app_val :=
  sheafAdjunctionCocontinuous_unit_app_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.sheafAdjunctionCocontinuous_counit_app_hom** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：sheafAdjunctionCocontinuous_counit_app_hom (F : Sheaf J A) : ((G.sheafAdju
nctionCocontinuous A J K).counit.app F).hom = (G.op.ranAdjunction A).counit.app 
F.obj
参数：F : Sheaf J A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app`：map_rest
rictFullyFaithful_counit_app (X : D) : iD.map ((adj.restrictFullyFaithful hiC hi
D comm1 comm2).counit.app X) = comm1.inv.app (R.obj …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.ranAdjunction_counit`：ranAdjunction_counit : (L.r
anAdjunction H).counit = L.ranCounit
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sheafAdjunctionCocontinuous_counit_app_hom (F : Sheaf J A) :
    ((G.sheafAdjunctionCocontinuous A J K).counit.app F).hom =
      (G.op.ranAdjunction A).counit.app F.obj :=
  ((G.op.ranAdjunction A).map_restrictFullyFaithful_counit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
      (by cat_disch)

@[deprecated (since := "2026-03-05")]
alias sheafAdjunctionCocontinuous_counit_app_val :=
  sheafAdjunctionCocontinuous_counit_app_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：sheafAdjunctionCocontinuous_homEquiv_apply_hom {F : Sheaf K A} {H : Sheaf 
J A} (f : (G.sheafPushforwardContinuous A J K).obj F ⟶ H) : ((G.sheafAdjunctionC
ocontinuous A J K).homEquiv F H f).hom = (G.op.ranAdjunction A).homEquiv F.obj H
.obj f.hom
参数：f : (G.sheafPushforwardContinuous A J K).obj F ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用引理 `CategoryTheory.Adjunction.restrictFullyFaithful_homEquiv_apply`：restrict
FullyFaithful_homEquiv_apply {X : C} {Y : D} (f : L.obj X ⟶ Y) : (adj.restrictFu
llyFaithful hiC hiD comm1 comm2).homEquiv X Y f = hi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
-/
lemma sheafAdjunctionCocontinuous_homEquiv_apply_hom {F : Sheaf K A} {H : Sheaf J A}
    (f : (G.sheafPushforwardContinuous A J K).obj F ⟶ H) :
    ((G.sheafAdjunctionCocontinuous A J K).homEquiv F H f).hom =
      (G.op.ranAdjunction A).homEquiv F.obj H.obj f.hom :=
  ((sheafToPresheaf K A).congr_map
    (((G.op.ranAdjunction A).restrictFullyFaithful_homEquiv_apply
      (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
      (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
      (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm f))).trans (by
        dsimp
        erw [Functor.map_id, Category.comp_id, Category.id_comp,
          Adjunction.homEquiv_unit])

@[deprecated (since := "2026-03-05")]
alias sheafAdjunctionCocontinuous_homEquiv_apply_val :=
  sheafAdjunctionCocontinuous_homEquiv_apply_hom

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The natural isomorphism exhibiting compatibility between pushforward and sheafification. -/
/-
**CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pushforwardContinuousSheafificationCompatibility : (whiskeringLeft _ _ A).
obj G.op ⋙ presheafToSheaf J A ≅ presheafToSheaf K A ⋙ G.sheafPushforwardContinu
ous A J K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism exhibiting compatibility between pushforward and sheafif
ication.
-/
def pushforwardContinuousSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K :=
  ((G.op.ranAdjunction A).comp (sheafificationAdjunction J A)).leftAdjointUniq
    ((sheafificationAdjunction K A).comp (G.sheafAdjunctionCocontinuous A J K))

set_option backward.isDefEq.respectTransparency false in
/- Implementation: This is primarily used to prove the lemma
`pullbackSheafificationCompatibility_hom_app_hom`. -/
/-
**CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：toSheafify_pullbackSheafificationCompatibility (F : Dᵒᵖ ⥤ A) : toSheafify 
J (G.op ⋙ F) ≫ ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.a
pp F).hom = whiskerLeft _ (toSheafify K _)
参数：F : Dᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`：unit_leftAdjoint
Uniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
 adj1.unit.app x ≫ G.map ((leftAdjointUniq a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
· 使用引理 `CategoryTheory.Functor.sheafAdjunctionCocontinuous_unit_app_hom`：sheafAd
junctionCocontinuous_unit_app_hom (F : Sheaf K A) : ((G.sheafAdjunctionCocontinu
ous A J K).unit.app F).hom = (G.op.ranAdjunction A).u…

--- 原说明 ---
Implementation: This is primarily used to prove the lemma
`pullbackSheafificationCompatibility_hom_app_hom`.
-/
lemma toSheafify_pullbackSheafificationCompatibility (F : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ F) ≫
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).hom =
    whiskerLeft _ (toSheafify K _) := by
  let adj₁ := G.op.ranAdjunction A
  let adj₂ := sheafificationAdjunction J A
  let adj₃ := sheafificationAdjunction K A
  let adj₄ := G.sheafAdjunctionCocontinuous A J K
  change adj₂.unit.app (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).obj F) ≫
    (sheafToPresheaf J A).map (((adj₁.comp adj₂).leftAdjointUniq (adj₃.comp adj₄)).hom.app F) =
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map (adj₃.unit.app F)
  apply (adj₁.homEquiv _ _).injective
  have eq := (adj₁.comp adj₂).unit_leftAdjointUniq_hom_app (adj₃.comp adj₄) F
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, comp_map,
    Category.assoc] at eq
  rw [adj₁.homEquiv_unit, Functor.map_comp, eq]
  apply (adj₁.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, map_comp, Category.assoc,
    Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  congr 3
  exact G.sheafAdjunctionCocontinuous_unit_app_hom A J K ((presheafToSheaf K A).obj F)

@[simp]
/-
**CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility_hom_ap
p_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pushforwardContinuousSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A)
 : ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).hom = 
sheafifyLift J (whiskerLeft G.op <| toSheafify K F) ((presheafToSheaf K A ⋙ G.sh
eafPushforwardContinuous A J K).obj F).property
参数：F : Dᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.sheafifyLift_unique`：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} 
(η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : sheafify J P ⟶ Q) : toSheafify J P 
≫ γ = η -> γ = sheafifyL…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility`：t
oSheafify_pullbackSheafificationCompatibility (F : Dᵒᵖ ⥤ A) : toSheafify J (G.op
 ⋙ F) ≫ ((G.pushforwardContinuousSheafificationCompatibilit…
-/
lemma pushforwardContinuousSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A) :
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).hom =
    sheafifyLift J (whiskerLeft G.op <| toSheafify K F)
      ((presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K).obj F).property := by
  apply sheafifyLift_unique
  apply toSheafify_pullbackSheafificationCompatibility

@[deprecated (since := "2026-03-05")]
alias pushforwardContinuousSheafificationCompatibility_hom_app_val :=
  pushforwardContinuousSheafificationCompatibility_hom_app_hom

end Functor

end CategoryTheory

