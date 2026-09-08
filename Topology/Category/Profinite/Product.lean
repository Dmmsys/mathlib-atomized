/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.Basic

/-!
# Compact subsets of products as limits in `Profinite`

This file exhibits a compact subset `C` of a product `(i : ι) → X i` of totally disconnected
Hausdorff spaces as a cofiltered limit in `Profinite` indexed by `Finset ι`.

## Main definitions

- `Profinite.indexFunctor` is the functor `(Finset ι)ᵒᵖ ⥤ Profinite` indexing the limit. It maps
  `J` to the restriction of `C` to `J`
- `Profinite.indexCone` is a cone on `Profinite.indexFunctor` with cone point `C`

## Main results

- `Profinite.isIso_indexCone_lift` says that the natural map from the cone point of the explicit
  limit cone in `Profinite` on `indexFunctor` to the cone point of `indexCone` is an
  isomorphism
- `Profinite.asLimitindexConeIso` is the induced isomorphism of cones.
- `Profinite.indexCone_isLimit` says that `indexCone` is a limit cone.

-/

@[expose] public section

universe u

namespace Profinite

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] (C : Set ((i : ι) → X i))
    (J K : ι → Prop)

namespace IndexFunctor

open ContinuousMap

/-- The object part of the functor `indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite`. -/
/-
**Profinite.IndexFunctor.obj** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.IndexFunctor`。
形式化陈述：obj : Set ((i : {i : ι // J i}) -> X i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object part of the functor `indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite`.
-/
def obj : Set ((i : {i : ι // J i}) → X i) := ContinuousMap.precomp (Subtype.val (p := J)) '' C

/-- The projection maps in the limit cone `indexCone`. -/
/-
**Profinite.IndexFunctor.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.IndexFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection maps in the limit cone `indexCone`.
-/
def π_app : C(C, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

variable {J K}

/-- The morphism part of the functor `indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite`. -/
/-
**Profinite.IndexFunctor.map** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.IndexFunctor`。
形式化陈述：map (h : forall i, J i -> K i) : C(obj C K, obj C J)
参数：h : forall i, J i -> K i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism part of the functor `indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite`.
-/
def map (h : ∀ i, J i → K i) : C(obj C K, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx ↦ by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    exact ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩
/-
**Profinite.IndexFunctor.surjective_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.IndexF
unctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_π_app :
    Function.Surjective (π_app C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  exact ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩
/-
**Profinite.IndexFunctor.map_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.IndexFun
ctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_π_app (h : ∀ i, J i → K i) : map C h ∘ π_app C K = π_app C J := rfl

variable {C}
/-
**Profinite.IndexFunctor.eq_of_forall_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Inde
xFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_forall_π_app_eq (a b : C)
    (h : ∀ (J : Finset ι), π_app C (· ∈ J) a = π_app C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, ContinuousMap.precomp, ContinuousMap.coe_mk] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

end IndexFunctor

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
variable {C}

open CategoryTheory Limits Opposite IndexFunctor

/-- The functor from the poset of finsets of `ι` to  `Profinite`, indexing the limit. -/
noncomputable
/-
**Profinite.indexFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：indexFunctor (hC : IsCompact C) : (Finset ι)ᵒᵖ ⥤ Profinite.{u} where obj J
参数：hC : IsCompact C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def indexFunctor (hC : IsCompact C) : (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (obj C (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := ConcreteCategory.ofHom (map C (leOfHom h.unop))

/-- The limit cone on `indexFunctor` -/
noncomputable
/-
**Profinite.indexCone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：indexCone (hC : IsCompact C) : Cone (indexFunctor hC) where pt
参数：hC : IsCompact C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def indexCone (hC : IsCompact C) : Cone (indexFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J ↦ ConcreteCategory.ofHom (π_app C (· ∈ unop J)) }

variable (hC : IsCompact C)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.isIso_indexCone_lift** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：isIso_indexCone_lift : IsIso ((limitConeIsLimit.{u, u} (indexFunctor hC)).
lift (indexCone hC))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.isIso_of_bijective`：isIso_of_bijective {X Y : CompHausLike.
{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) : IsIso f
· 使用定理 `Profinite.IndexFunctor.eq_of_forall_π_app_eq`：eq_of_forall_π_app_eq (a b
 : C) (h : forall (J : Finset ι), π_app C (· in J) a = π_app C (· in J) b) : a =
 b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `instT1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), T1Space (X i)],   T1Space ((i : ι) → X i)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.IndexFunctor.map_comp_π_app`：map_comp_π_app (h : forall i, J i
 -> K i) : map C h ∘ π_app C K = π_app C J
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `Set.Nonempty.preimage`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.No
nempty → ∀ {f : α → β}, Function.Surjective f → (f ⁻¹' s).Nonempty
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Profinite.IndexFunctor.surjective_π_app`：surjective_π_app : Function.Sur
jective (π_app C J)
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
instance isIso_indexCone_lift :
    IsIso ((limitConeIsLimit.{u, u} (indexFunctor hC)).lift (indexCone hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_π_app_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone.{u, u} (indexFunctor hC)).pt => f.val (op J) at h
        exact h
      · rsuffices ⟨b, hb⟩ : ∃ (x : C), ∀ (J : Finset ι), π_app C (· ∈ J) x = a.val (op J)
        · use b
          apply Subtype.ext
          apply funext
          intro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((π_app C (· ∈ J)) ⁻¹' {s}) := by
          intro J s
          refine IsClosed.preimage (π_app C (· ∈ J)).continuous ?_
          exact T1Space.t1 s
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            π_app C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            π_app C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)} := by
          intro J K h x hx
          simp only [Set.mem_preimage] at hx ⊢
          rw [← map_comp_π_app C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), π_app C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
            (fun J : Finset ι => π_app C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_isDirected_le H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_π_app _))
            (fun J => (hc J (a.val (op J))).isCompact) fun J => hc J (a.val (op J))
        exact ⟨x, Set.mem_iInter.1 hx⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from `C` to the explicit limit as an isomorphism. -/
noncomputable
/-
**Profinite.isoindexConeLift** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：isoindexConeLift : @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace
]) _ _ ≅ (Profinite.limitCone.{u, u} (indexFunctor hC)).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isoindexConeLift :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone.{u, u} (indexFunctor hC)).pt :=
  asIso <| (Profinite.limitConeIsLimit.{u, u} _).lift (indexCone hC)

/-- The isomorphism of cones induced by `isoindexConeLift`. -/
noncomputable
/-
**Profinite.asLimitindexConeIso** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：asLimitindexConeIso : indexCone hC ≅ Profinite.limitCone.{u, u} _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def asLimitindexConeIso : indexCone hC ≅ Profinite.limitCone.{u, u} _ :=
  Limits.Cone.ext (isoindexConeLift hC) fun _ => rfl

/-- `indexCone` is a limit cone. -/
noncomputable
/-
**Profinite.indexCone_isLimit** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：indexCone_isLimit : CategoryTheory.Limits.IsLimit (indexCone hC)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def indexCone_isLimit : CategoryTheory.Limits.IsLimit (indexCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitindexConeIso hC).symm

end Profinite

