/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!

# Coverings and sieves; from sheaves on sites and sheaves on spaces

In this file, we connect coverings in a topological space to sieves in the associated Grothendieck
topology, in preparation of connecting the sheaf condition on sites to the various sheaf conditions
on spaces.

We also specialize results about sheaves on sites to sheaves on spaces; we show that the inclusion
functor from a topological basis to `TopologicalSpace.Opens` is cover dense, that open maps
induce cover-preserving functors, and that open embeddings induce continuous functors.

-/

@[expose] public section


noncomputable section

open CategoryTheory TopologicalSpace Topology

universe w v u

namespace TopCat.Presheaf

variable {X : TopCat.{w}}

/-- Given a presieve `R` on `U`, we obtain a covering family of open sets in `X`, by taking as index
type the type of dependent pairs `(V, f)`, where `f : V ⟶ U` is in `R`.
-/
/-
**TopCat.Presheaf.coveringOfPresieve** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：coveringOfPresieve (U : Opens X) (R : Presieve U) : (Σ V, { f : V ⟶ U // R
 f }) -> Opens X
参数：U : Opens X；R : Presieve U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presieve `R` on `U`, we obtain a covering family of open sets in `X`, by
 taking as index
type the type of dependent pairs `(V, f)`, where `f : V ⟶ U` is in `R`.
-/
def coveringOfPresieve (U : Opens X) (R : Presieve U) : (Σ V, { f : V ⟶ U // R f }) → Opens X :=
  fun f => f.1

@[simp]
/-
**TopCat.Presheaf.coveringOfPresieve_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pre
sheaf`。
形式化陈述：coveringOfPresieve_apply (U : Opens X) (R : Presieve U) (f : Σ V, { f : V 
⟶ U // R f }) : coveringOfPresieve U R f = f.1
参数：U : Opens X；R : Presieve U；f : Σ V, { f : V ⟶ U // R f }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coveringOfPresieve_apply (U : Opens X) (R : Presieve U) (f : Σ V, { f : V ⟶ U // R f }) :
    coveringOfPresieve U R f = f.1 := rfl

namespace coveringOfPresieve

variable (U : Opens X) (R : Presieve U)

/-- If `R` is a presieve in the Grothendieck topology on `Opens X`, the covering family associated
to `R` really is _covering_, i.e. the union of all open sets equals `U`.
-/
/-
**TopCat.Presheaf.coveringOfPresieve.iSup_eq_of_mem_grothendieck** 是 Mathlib 中的一
个定理，位于命名空间 `TopCat.Presheaf.coveringOfPresieve`。
形式化陈述：iSup_eq_of_mem_grothendieck (hR : Sieve.generate R in Opens.grothendieckTo
pology X U) : iSup (coveringOfPresieve U R) = U
参数：hR : Sieve.generate R in Opens.grothendieckTopology X U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i

--- 原说明 ---
If `R` is a presieve in the Grothendieck topology on `Opens X`, the covering fam
ily associated
to `R` really is _covering_, i.e. the union of all open sets equals `U`.
-/
theorem iSup_eq_of_mem_grothendieck (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    iSup (coveringOfPresieve U R) = U := by
  apply le_antisymm
  · refine iSup_le ?_
    intro f
    exact f.2.1.le
  intro x hxU
  rw [Opens.mem_iSup]
  obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU
  exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩

end coveringOfPresieve

/-- Given a family of opens `U : ι → Opens X` and any open `Y : Opens X`, we obtain a presieve
on `Y` by declaring that a morphism `f : V ⟶ Y` is a member of the presieve if and only if
there exists an index `i : ι` such that `V = U i`.
-/
/-
**TopCat.Presheaf.presieveOfCoveringAux** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：presieveOfCoveringAux {ι : Type v} (U : ι -> Opens X) (Y : Opens X) : Pres
ieve Y
参数：U : ι -> Opens X；Y : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of opens `U : ι → Opens X` and any open `Y : Opens X`, we obtain 
a presieve
on `Y` by declaring that a morphism `f : V ⟶ Y` is a member of the presieve if a
nd only if
there exists an index `i : ι` such that `V = U i`.
-/
def presieveOfCoveringAux {ι : Type v} (U : ι → Opens X) (Y : Opens X) : Presieve Y :=
  fun V _ => ∃ i, V = U i

/-- Take `Y` to be `iSup U` and obtain a presieve over `iSup U`. -/
/-
**TopCat.Presheaf.presieveOfCovering** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：presieveOfCovering {ι : Type v} (U : ι -> Opens X) : Presieve (iSup U)
参数：U : ι -> Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take `Y` to be `iSup U` and obtain a presieve over `iSup U`.
-/
def presieveOfCovering {ι : Type v} (U : ι → Opens X) : Presieve (iSup U) :=
  presieveOfCoveringAux U (iSup U)

/-- Given a presieve `R` on `Y`, if we take its associated family of opens via `coveringOfPresieve`
(which may not cover `Y` if `R` is not covering), and take the presieve on `Y` associated to the
family of opens via `presieveOfCoveringAux`, then we get back the original presieve `R`. -/
@[simp]
/-
**TopCat.Presheaf.covering_presieve_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pr
esheaf`。
形式化陈述：covering_presieve_eq_self {Y : Opens X} (R : Presieve Y) : presieveOfCover
ingAux (coveringOfPresieve Y R) Y = R
参数：R : Presieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
Given a presieve `R` on `Y`, if we take its associated family of opens via `cove
ringOfPresieve`
(which may not cover `Y` if `R` is not covering), and take the presieve on `Y` a
ssociated to the
family of opens via `presieveOfCoveringAux`, then we get back the original presi
eve `R`.
-/
theorem covering_presieve_eq_self {Y : Opens X} (R : Presieve Y) :
    presieveOfCoveringAux (coveringOfPresieve Y R) Y = R := by
  funext Z
  ext f
  exact ⟨fun ⟨⟨_, f', h⟩, rfl⟩ => by rwa [Subsingleton.elim f f'], fun h => ⟨⟨Z, f, h⟩, rfl⟩⟩

namespace presieveOfCovering

variable {ι : Type v} (U : ι → Opens X)

/-- The sieve generated by `presieveOfCovering U` is a member of the Grothendieck topology.
-/
/-
**TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology** 是 Mathlib 中的一个定理
，位于命名空间 `TopCat.Presheaf.presieveOfCovering`。
形式化陈述：mem_grothendieckTopology : Sieve.generate (presieveOfCovering U) in Opens.
grothendieckTopology X (iSup U)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
The sieve generated by `presieveOfCovering U` is a member of the Grothendieck to
pology.
-/
theorem mem_grothendieckTopology :
    Sieve.generate (presieveOfCovering U) ∈ Opens.grothendieckTopology X (iSup U) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Opens.leSupr U i, ⟨U i, 𝟙 _, Opens.leSupr U i, ⟨i, rfl⟩, Category.id_comp _⟩, hxi⟩

/-- An index `i : ι` can be turned into a dependent pair `(V, f)`, where `V` is an open set and
`f : V ⟶ iSup U` is a member of `presieveOfCovering U f`.
-/
/-
**TopCat.Presheaf.presieveOfCovering.homOfIndex** 是 Mathlib 中的一个定义，位于命名空间 `TopCa
t.Presheaf.presieveOfCovering`。
形式化陈述：homOfIndex (i : ι) : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An index `i : ι` can be turned into a dependent pair `(V, f)`, where `V` is an o
pen set and
`f : V ⟶ iSup U` is a member of `presieveOfCovering U f`.
-/
def homOfIndex (i : ι) : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f } :=
  ⟨U i, Opens.leSupr U i, i, rfl⟩

/-- By using the axiom of choice, a dependent pair `(V, f)` where `f : V ⟶ iSup U` is a member of
`presieveOfCovering U f` can be turned into an index `i : ι`, such that `V = U i`.
-/
/-
**TopCat.Presheaf.presieveOfCovering.indexOfHom** 是 Mathlib 中的一个定义，位于命名空间 `TopCa
t.Presheaf.presieveOfCovering`。
形式化陈述：indexOfHom (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }) : ι
参数：f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By using the axiom of choice, a dependent pair `(V, f)` where `f : V ⟶ iSup U` i
s a member of
`presieveOfCovering U f` can be turned into an index `i : ι`, such that `V = U i
`.
-/
def indexOfHom (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }) : ι :=
  f.2.2.choose
/-
**TopCat.Presheaf.presieveOfCovering.indexOfHom_spec** 是 Mathlib 中的一个定理，位于命名空间 `
TopCat.Presheaf.presieveOfCovering`。
形式化陈述：indexOfHom_spec (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }) : 
f.1 = U (indexOfHom U f)
参数：f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem indexOfHom_spec (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }) :
    f.1 = U (indexOfHom U f) :=
  f.2.2.choose_spec

end presieveOfCovering

end TopCat.Presheaf

namespace TopCat.Opens

variable {X : TopCat.{w}} {ι : Type*}

/-
**TopCat.Opens.coverDense_iff_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Opens`。
形式化陈述：coverDense_iff_isBasis [Category* ι] (B : ι ⥤ Opens X) : B.IsCoverDense (O
pens.grothendieckTopology X) ↔ Opens.IsBasis (Set.range B.obj)
参数：B : ι ⥤ Opens X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `CategoryTheory.Functor.IsCoverDense.is_cover`：∀ {C : Type u_1} {inst : C
ategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D} {G : Categor…
-/
theorem coverDense_iff_isBasis [Category* ι] (B : ι ⥤ Opens X) :
    B.IsCoverDense (Opens.grothendieckTopology X) ↔ Opens.IsBasis (Set.range B.obj) := by
  rw [Opens.isBasis_iff_nbhd]
  constructor
  · intro hd U x hx; rcases hd.1 U x hx with ⟨V, f, ⟨i, f₁, f₂, _⟩, hV⟩
    exact ⟨B.obj i, ⟨i, rfl⟩, f₁.le hV, f₂.le⟩
  intro hb; constructor; intro U x hx; rcases hb hx with ⟨_, ⟨i, rfl⟩, hx, hi⟩
  exact ⟨B.obj i, ⟨⟨hi⟩⟩, ⟨⟨i, 𝟙 _, ⟨⟨hi⟩⟩, rfl⟩⟩, hx⟩
/-
**TopCat.Opens.coverDense_inducedFunctor** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Opens
`。
形式化陈述：coverDense_inducedFunctor {B : ι -> Opens X} (h : Opens.IsBasis (Set.range
 B)) : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X)
参数：h : Opens.IsBasis (Set.range B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.Opens.coverDense_iff_isBasis`：coverDense_iff_isBasis [Category* ι
] (B : ι ⥤ Opens X) : B.IsCoverDense (Opens.grothendieckTopology X) ↔ Opens.IsBa
sis (Set.range B.obj)
-/
theorem coverDense_inducedFunctor {B : ι → Opens X} (h : Opens.IsBasis (Set.range B)) :
    (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
  (coverDense_iff_isBasis _).2 h

end TopCat.Opens

section IsOpenEmbedding

open TopCat.Presheaf Opposite

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} {f : X ⟶ Y} {F : Y.Presheaf C}

/-
**Topology.IsOpenEmbedding.compatiblePreserving** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.compatiblePreserving (hf : IsOpenEmbedding f) : C
ompatiblePreserving (Opens.grothendieckTopology Y) hf.functor
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.mono_iff_injective`：mono_iff_injective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `CategoryTheory.compatiblePreservingOfDownwardsClosed`：compatiblePreservi
ngOfDownwardsClosed (F : C ⥤ D) [F.Full] [F.Faithful] (hF : forall {c : C} {d : 
D} (_ : d ⟶ F.obj c), Σ c', F.obj c' ≅ d) …
· 使用定理 `IsOpenMap.functor_faithful`：∀ {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap
 ⇑(CategoryTheory.ConcreteCategory.hom f)), hf.functor.Faithful
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
theorem Topology.IsOpenEmbedding.compatiblePreserving (hf : IsOpenEmbedding f) :
    CompatiblePreserving (Opens.grothendieckTopology Y) hf.functor := by
  have : Mono f := (TopCat.mono_iff_injective f).mpr hf.injective
  apply compatiblePreservingOfDownwardsClosed
  intro U V i
  refine ⟨(Opens.map f).obj V, eqToIso <| Opens.ext <| Set.image_preimage_eq_of_subset fun x h ↦ ?_⟩
  obtain ⟨_, _, rfl⟩ := i.le h
  exact ⟨_, rfl⟩
/-
**IsOpenMap.coverPreserving** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.coverPreserving (hf : IsOpenMap f) : CoverPreserving (Opens.grot
hendieckTopology X) (Opens.grothendieckTopology Y) hf.functor
参数：hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem IsOpenMap.coverPreserving (hf : IsOpenMap f) :
    CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) hf.functor := by
  constructor
  rintro U S hU _ ⟨x, hx, rfl⟩
  obtain ⟨V, i, hV, hxV⟩ := hU x hx
  exact ⟨_, hf.functor.map i, ⟨_, i, 𝟙 _, hV, rfl⟩, Set.mem_image_of_mem f hxV⟩
/-
**Topology.IsOpenEmbedding.functor_isContinuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.functor_isContinuous (h : IsOpenEmbedding f) : h.
functor.IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology 
Y)
参数：h : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isContinuous_of_coverPreserving`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Topology.IsOpenEmbedding.compatiblePreserving`：Topology.IsOpenEmbedding.
compatiblePreserving (hf : IsOpenEmbedding f) : CompatiblePreserving (Opens.grot
hendieckTopology Y) hf.functor
· 使用定理 `IsOpenMap.coverPreserving`：IsOpenMap.coverPreserving (hf : IsOpenMap f) 
: CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) 
hf.functor
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
-/
lemma Topology.IsOpenEmbedding.functor_isContinuous (h : IsOpenEmbedding f) :
    h.functor.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact h.compatiblePreserving
  · exact h.isOpenMap.coverPreserving
/-
**TopCat.Presheaf.isSheaf_of_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopCat.Presheaf.isSheaf_of_isOpenEmbedding (h : IsOpenEmbedding f) (hF : F
.IsSheaf) : IsSheaf (h.functor.op ⋙ F)
参数：h : IsOpenEmbedding f；hF : F.IsSheaf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.functor_isContinuous`：Topology.IsOpenEmbedding.
functor_isContinuous (h : IsOpenEmbedding f) : h.functor.IsContinuous (Opens.gro
thendieckTopology X) (Opens.grothen…
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf`：op_comp_isSheaf [Functor.IsConti
nuous F J K] (G : Sheaf K A) : Presheaf.IsSheaf J (F.op ⋙ G.obj)
-/
theorem TopCat.Presheaf.isSheaf_of_isOpenEmbedding (h : IsOpenEmbedding f) (hF : F.IsSheaf) :
    IsSheaf (h.functor.op ⋙ F) := by
  have := h.functor_isContinuous
  exact Functor.op_comp_isSheaf _ _ _ ⟨_, hF⟩

/-- The restriction functor of a sheaf to an open subspace. -/
@[simps!]
/-
**TopologicalSpace.Opens.sheafRestrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.Opens.sheafRestrict (U : Opens X) : Sheaf (Opens.grothend
ieckTopology X) C ⥤ Sheaf (Opens.grothendieckTopology U) C
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction functor of a sheaf to an open subspace.
-/
def TopologicalSpace.Opens.sheafRestrict (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) C ⥤ Sheaf (Opens.grothendieckTopology U) C :=
  haveI H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  haveI := H.functor_isContinuous
  H.isOpenMap.functor.sheafPushforwardContinuous C _ _

variable (f)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RepresentablyFlat (Opens.map f) := by
  constructor
  intro U
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
      exact ⟨⟨⟨PUnit.unit⟩, V.right ⊓ W.right, homOfLE <| le_inf V.hom.le W.hom.le⟩,
        StructuredArrow.homMk (homOfLE inf_le_left),
        StructuredArrow.homMk (homOfLE inf_le_right), trivial⟩
    · exact fun _ _ _ _ ↦ ⟨_, 𝟙 _, by simp [eq_iff_true_of_subsingleton]⟩
  · exact ⟨StructuredArrow.mk <| show U ⟶ (Opens.map f).obj ⊤ from homOfLE le_top⟩
/-
**compatiblePreserving_opens_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compatiblePreserving_opens_map : CompatiblePreserving (Opens.grothendieckT
opology X) (Opens.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.compatiblePreservingOfFlat`：compatiblePreservingOfFlat {C
 : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (K : GrothendieckT
opology D) (G : C ⥤ D) [Represe…
· 使用定理 `instRepresentablyFlatOpensCarrierMap`：∀ {X Y : TopCat} (f : X ⟶ Y), Cate
goryTheory.RepresentablyFlat (TopologicalSpace.Opens.map f)
-/
theorem compatiblePreserving_opens_map :
    CompatiblePreserving (Opens.grothendieckTopology X) (Opens.map f) :=
  compatiblePreservingOfFlat _ _
/-
**coverPreserving_opens_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coverPreserving_opens_map : CoverPreserving (Opens.grothendieckTopology Y)
 (Opens.grothendieckTopology X) (Opens.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem coverPreserving_opens_map : CoverPreserving (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) (Opens.map f) := by
  constructor
  intro U S hS x hx
  obtain ⟨V, i, hi, hxV⟩ := hS (f x) hx
  exact ⟨_, (Opens.map f).map i, ⟨_, _, 𝟙 _, hi, Subsingleton.elim _ _⟩, hxV⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Opens.map f).IsContinuous (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map f
  · exact coverPreserving_opens_map f

end IsOpenEmbedding

namespace TopCat.Sheaf

open TopCat Opposite

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} {ι : Type*} {B : ι → Opens X}
variable (F : X.Presheaf C) (F' : Sheaf C X)

/-- The empty component of a sheaf is terminal. -/
/-
**TopCat.Sheaf.isTerminalOfEmpty** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：isTerminalOfEmpty (F : Sheaf C X) : Limits.IsTerminal (F.obj.obj (op ⊥))
参数：F : Sheaf C X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty component of a sheaf is terminal.
-/
def isTerminalOfEmpty (F : Sheaf C X) : Limits.IsTerminal (F.obj.obj (op ⊥)) :=
  F.isTerminalOfBotCover ⊥ (fun _ h => h.elim)

/-- A variant of `isTerminalOfEmpty` that is easier to `apply`. -/
/-
**TopCat.Sheaf.isTerminalOfEqEmpty** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：isTerminalOfEqEmpty (F : X.Sheaf C) {U : Opens X} (h : U = ⊥) : Limits.IsT
erminal (F.obj.obj (op U))
参数：F : X.Sheaf C；h : U = ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `isTerminalOfEmpty` that is easier to `apply`.
-/
def isTerminalOfEqEmpty (F : X.Sheaf C) {U : Opens X} (h : U = ⊥) :
    Limits.IsTerminal (F.obj.obj (op U)) := by
  convert! F.isTerminalOfEmpty

/-- If a family `B` of open sets forms a basis of the topology on `X`, and if `F'`
is a sheaf on `X`, then a homomorphism between a presheaf `F` on `X` and `F'`
is equivalent to a homomorphism between their restrictions to the indexing type
`ι` of `B`, with the induced category structure on `ι`. -/
/-
**TopCat.Sheaf.restrictHomEquivHom** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：restrictHomEquivHom (h : Opens.IsBasis (Set.range B)) : ((inducedFunctor B
).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) ≃ (F ⟶ F'.1)
参数：h : Opens.IsBasis (Set.range B)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Opens.coverDense_inducedFunctor`：coverDense_inducedFunctor {B : ι
 -> Opens X} (h : Opens.IsBasis (Set.range B)) : (inducedFunctor B).IsCoverDense
 (Opens.grothendieckTopology…

--- 原说明 ---
If a family `B` of open sets forms a basis of the topology on `X`, and if `F'`
is a sheaf on `X`, then a homomorphism between a presheaf `F` on `X` and `F'`
is equivalent to a homomorphism between their restrictions to the indexing type
`ι` of `B`, with the induced category structure on `ι`.
-/
def restrictHomEquivHom (h : Opens.IsBasis (Set.range B)) :
    ((inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) ≃ (F ⟶ F'.1) :=
  @Functor.IsCoverDense.restrictHomEquivHom _ _ _ _ _ _ _ _
    (Opens.coverDense_inducedFunctor h) _ F F'

@[simp]
/-
**TopCat.Sheaf.extend_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：extend_hom_app (h : Opens.IsBasis (Set.range B)) (α : (inducedFunctor B).o
p ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) (i : ι) : (restrictHomEquivHom F F' h α).a
pp (op (B i)) = α.app (op i)
参数：h : Opens.IsBasis (Set.range B)；α : (inducedFunctor B).op ⋙ F ⟶ (inducedFunct
or B).op ⋙ F'.1；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem extend_hom_app (h : Opens.IsBasis (Set.range B))
    (α : (inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) (i : ι) :
    (restrictHomEquivHom F F' h α).app (op (B i)) = α.app (op i) := by
  nth_rw 2 [← (restrictHomEquivHom F F' h).left_inv α]
  rfl
/-
**TopCat.Sheaf.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：hom_ext (h : Opens.IsBasis (Set.range B)) {α β : F ⟶ F'.1} (he : forall i,
 α.app (op (B i)) = β.app (op (B i))) : α = β
参数：h : Opens.IsBasis (Set.range B)；he : forall i, α.app (op (B i)) = β.app (op (
B i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem hom_ext (h : Opens.IsBasis (Set.range B))
    {α β : F ⟶ F'.1} (he : ∀ i, α.app (op (B i)) = β.app (op (B i))) : α = β := by
  apply (restrictHomEquivHom F F' h).symm.injective
  ext i
  exact he i.unop
/-
**TopCat.Sheaf.isIso_iff_isIso_basis** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：isIso_iff_isIso_basis {F G : Sheaf C X} (h : Opens.IsBasis (Set.range B)) 
{φ : F ⟶ G} (hi : forall i, IsIso (φ.hom.app (op (B i)))) : IsIso φ
参数：h : Opens.IsBasis (Set.range B)；hi : forall i, IsIso (φ.hom.app (op (B i)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Opens.coverDense_inducedFunctor`：coverDense_inducedFunctor {B : ι
 -> Opens X} (h : Opens.IsBasis (Set.range B)) : (inducedFunctor B).IsCoverDense
 (Opens.grothendieckTopology…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`：iso_of_restrict
_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.hom)) : IsIs
o α
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.InducedCategory.full`：∀ {C : Type u₁} {D : Type u₂} [inst
 : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.inducedFunc
tor F).Full
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
-/
theorem isIso_iff_isIso_basis {F G : Sheaf C X} (h : Opens.IsBasis (Set.range B))
    {φ : F ⟶ G} (hi : ∀ i, IsIso (φ.hom.app (op (B i)))) :
    IsIso φ := by
  have : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
    Opens.coverDense_inducedFunctor h
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := inducedFunctor B) _ ?_
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ ↦ hi _

end TopCat.Sheaf

namespace TopologicalSpace.Opens

/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : Opens X ⥤ Opens Y) (G : Opens Y ⥤ Opens Z)
    [Functor.IsContinuous F (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)]
    [Functor.IsContinuous G (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)] :
    Functor.IsContinuous (F ⋙ G) (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology _) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology _) _

end TopologicalSpace.Opens

