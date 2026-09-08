/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.GroupTheory.ResiduallyFinite
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Profinite completion of groups

We define the profinite completion of a group as the limit of its finite quotients,
and prove its universal property.
-/

@[expose] public section

namespace OpenNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open normal subgroup of a compact topological group has finite index. -/
@[to_additive
  /-- An open normal additive subgroup of a compact topological additive group has finite index. -/]
/-
**OpenNormalSubgroup.toFiniteIndexNormalSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Open
NormalSubgroup`。
形式化陈述：toFiniteIndexNormalSubgroup [CompactSpace G] [ContinuousMul G] (H : OpenNo
rmalSubgroup G) : FiniteIndexNormalSubgroup G
参数：H : OpenNormalSubgroup G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
-/
def toFiniteIndexNormalSubgroup [CompactSpace G] [ContinuousMul G]
    (H : OpenNormalSubgroup G) : FiniteIndexNormalSubgroup G :=
  letI : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  FiniteIndexNormalSubgroup.ofSubgroup H.toSubgroup

@[to_additive]
/-
**OpenNormalSubgroup.toFiniteIndexNormalSubgroup_mono** 是 Mathlib 中的一个定理，位于命名空间 
`OpenNormalSubgroup`。
形式化陈述：toFiniteIndexNormalSubgroup_mono [CompactSpace G] [ContinuousMul G] {H K :
 OpenNormalSubgroup G} (h : H <= K) : H.toFiniteIndexNormalSubgroup <= K.toFinit
eIndexNormalSubgroup
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFiniteIndexNormalSubgroup_mono [CompactSpace G] [ContinuousMul G]
    {H K : OpenNormalSubgroup G} (h : H ≤ K) :
    H.toFiniteIndexNormalSubgroup ≤ K.toFiniteIndexNormalSubgroup :=
  fun _ hx ↦ h hx

@[to_additive]
/-
**OpenNormalSubgroup.toFiniteIndexNormalSubgroup_injective** 是 Mathlib 中的一个定理，位于
命名空间 `OpenNormalSubgroup`。
形式化陈述：toFiniteIndexNormalSubgroup_injective [CompactSpace G] [ContinuousMul G] :
 Function.Injective (toFiniteIndexNormalSubgroup (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.toSubgroup_injective`：toSubgroup_injective : Function
.Injective (fun H => H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G -> Subgr
oup G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toFiniteIndexNormalSubgroup_injective [CompactSpace G] [ContinuousMul G] :
    Function.Injective (toFiniteIndexNormalSubgroup (G := G)) := by
  intro H K h
  apply toSubgroup_injective
  exact congrArg (fun L : FiniteIndexNormalSubgroup G ↦ (L : Subgroup G)) h

end OpenNormalSubgroup

namespace ProfiniteGrp

open CategoryTheory

universe u

namespace ProfiniteCompletion

variable (G : GrpCat.{u})

/-- The diagram of finite quotients indexed by finite-index normal subgroups of `G`. -/
@[to_additive /-- The diagram of finite quotients indexed by finite-index normal subgroups. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.finiteGrpDiagram** 是 Mathlib 中的一个定义，位于命名空间 `P
rofiniteGrp.ProfiniteCompletion`。
形式化陈述：finiteGrpDiagram : FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} where obj H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram of finite quotients indexed by finite-index normal subgroups of `G`.
-/
def finiteGrpDiagram : FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} where
  obj H := FiniteGrp.of <| G ⧸ H.toSubgroup
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- The finite-quotient diagram viewed in `ProfiniteGrp`. -/
@[to_additive /-- The finite-quotient diagram viewed in `ProfiniteAddGrp`. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.diagram** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteG
rp.ProfiniteCompletion`。
形式化陈述：diagram : FiniteIndexNormalSubgroup G ⥤ ProfiniteGrp.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite-quotient diagram viewed in `ProfiniteGrp`.
-/
def diagram : FiniteIndexNormalSubgroup G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram _ ⋙ forget₂ _ _

/-- The profinite completion of `G` as a projective limit. -/
@[to_additive /-- The profinite completion of `G` as a projective limit. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.completion** 是 Mathlib 中的一个定义，位于命名空间 `Profini
teGrp.ProfiniteCompletion`。
形式化陈述：completion : ProfiniteGrp.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The profinite completion of `G` as a projective limit.
-/
def completion : ProfiniteGrp.{u} := limit (diagram G)

/-- The canonical map from `G` to its profinite completion, as a function. -/
@[to_additive /-- The canonical map from `G` to its profinite completion, as a function. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.etaFn** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp
.ProfiniteCompletion`。
形式化陈述：etaFn (x : G) : completion G
参数：x : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `G` to its profinite completion, as a function.
-/
def etaFn (x : G) : completion G := ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

/-- The canonical morphism from `G` to its profinite completion. -/
@[to_additive /-- The canonical morphism from `G` to its profinite completion. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.eta** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp.P
rofiniteCompletion`。
形式化陈述：eta : G ⟶ GrpCat.of (completion G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from `G` to its profinite completion.
-/
def eta : G ⟶ GrpCat.of (completion G) := GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**ProfiniteGrp.ProfiniteCompletion.mono_eta_iff_residuallyFinite** 是 Mathlib 中的一
个定理，位于命名空间 `ProfiniteGrp.ProfiniteCompletion`。
形式化陈述：mono_eta_iff_residuallyFinite : Mono (eta G) ↔ Group.ResiduallyFinite G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GrpCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inject
ive f
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup`：residuallyF
inite_iff_forall_finiteIndexNormalSubgroup : ResiduallyFinite G ↔ forall g : G, 
(forall H : FiniteIndexNormalSubgroup G, g in H) …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_left`：∀ {a b c : Prop}, (a ↔ b) → (a → c ↔ b → c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `FiniteIndexNormalSubgroup.instNormal`：∀ {G : Type u_1} [inst : Group G] 
(H : FiniteIndexNormalSubgroup G), H.Normal
-/
theorem mono_eta_iff_residuallyFinite : Mono (eta G) ↔ Group.ResiduallyFinite G := by
  rw [GrpCat.mono_iff_injective, injective_iff_map_eq_one,
    Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  refine forall_congr' fun g ↦ imp_congr_left ?_
  rw [Subtype.ext_iff, funext_iff]
  exact forall_congr' fun H ↦ QuotientGroup.eq_one_iff g

@[to_additive]
/-
**ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite** 是 Math
lib 中的一个定理，位于命名空间 `ProfiniteGrp.ProfiniteCompletion`。
形式化陈述：etaFn_injective_iff_residuallyFinite : Function.Injective (etaFn G) ↔ Grou
p.ResiduallyFinite G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `GrpCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inject
ive f
· 使用定理 `ProfiniteGrp.ProfiniteCompletion.mono_eta_iff_residuallyFinite`：mono_eta
_iff_residuallyFinite : Mono (eta G) ↔ Group.ResiduallyFinite G
-/
theorem etaFn_injective_iff_residuallyFinite :
    Function.Injective (etaFn G) ↔ Group.ResiduallyFinite G :=
  (GrpCat.mono_iff_injective (eta G)).symm.trans (mono_eta_iff_residuallyFinite G)

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**ProfiniteGrp.ProfiniteCompletion.denseRange** 是 Mathlib 中的一个引理，位于命名空间 `Profini
teGrp.ProfiniteCompletion`。
形式化陈述：denseRange : DenseRange (etaFn G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dense_iff_inter_open`：dense_iff_inter_open : Dense s ↔ forall U, IsOpen 
U -> U.Nonempty -> (U inter s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_pi_iff`：isOpen_pi_iff {s : Set (forall a, A a)} : IsOpen s ↔ fora
ll f, f in s -> exists (I : Finset ι) (u : forall a, Set (A a)), (forall a, a in
 I …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normal_iInf_normal`：normal_iInf_normal {ι : Sort*} {a : ι -> Su
bgroup G} (norm : forall i : ι, (a i).Normal) : (iInf a).Normal
· 使用定理 `FiniteIndexNormalSubgroup.instNormal`：∀ {G : Type u_1} [inst : Group G] 
(H : FiniteIndexNormalSubgroup G), H.Normal
· 使用定理 `Subgroup.finiteIndex_iInf`：finiteIndex_iInf {ι : Type*} [Finite ι] {f : 
ι -> Subgroup G} (hf : forall i, (f i).FiniteIndex) : (⨅ i, f i).FiniteIndex
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FiniteIndexNormalSubgroup.instFiniteIndex`：∀ {G : Type u_1} [inst : Grou
p G] (H : FiniteIndexNormalSubgroup G), H.FiniteIndex
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma denseRange : DenseRange (etaFn G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => j.val
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : FiniteIndexNormalSubgroup G := { toSubgroup := M }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => (j.val.toSubgroup)) ⟨a, a_in_J⟩).hom
  rw [← (etaFn G origin).property M_to_Na]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right

variable {G}
variable {P : ProfiniteGrp.{u}}

/-- The preimage of an open normal subgroup under a morphism to a profinite group. -/
@[to_additive /-- The preimage of an open normal subgroup under a morphism to a profinite group. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.preimage** 是 Mathlib 中的一个定义，位于命名空间 `Profinite
Grp.ProfiniteCompletion`。
形式化陈述：preimage (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) : FiniteIndexNor
malSubgroup G
参数：f : G ⟶ GrpCat.of P；H : OpenNormalSubgroup P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of an open normal subgroup under a morphism to a profinite group.
-/
def preimage (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) : FiniteIndexNormalSubgroup G :=
  H.toFiniteIndexNormalSubgroup.comap f.hom

@[to_additive]
/-
**ProfiniteGrp.ProfiniteCompletion.preimage_le** 是 Mathlib 中的一个引理，位于命名空间 `Profin
iteGrp.ProfiniteCompletion`。
形式化陈述：preimage_le {f : G ⟶ GrpCat.of P} {H K : OpenNormalSubgroup P} (h : H <= K
) : preimage f H <= preimage f K
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteIndexNormalSubgroup.comap_mono`：comap_mono (f : G ->* H) {K L : Fi
niteIndexNormalSubgroup H} (h : K <= L) : comap f K <= comap f L
-/
lemma preimage_le {f : G ⟶ GrpCat.of P} {H K : OpenNormalSubgroup P}
    (h : H ≤ K) : preimage f H ≤ preimage f K :=
  FiniteIndexNormalSubgroup.comap_mono _ h

/-- The induced map on finite quotients coming from a morphism to `P`. -/
@[to_additive /-- The induced map on finite quotients coming from a morphism to `P`. -/]
/-
**ProfiniteGrp.ProfiniteCompletion.quotientMap** 是 Mathlib 中的一个定义，位于命名空间 `Profin
iteGrp.ProfiniteCompletion`。
形式化陈述：quotientMap (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) : FiniteGrp.o
f (G ⧸ (preimage f H).toSubgroup) ⟶ FiniteGrp.of (P ⧸ H.toSubgroup)
参数：f : G ⟶ GrpCat.of P；H : OpenNormalSubgroup P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map on finite quotients coming from a morphism to `P`.
-/
def quotientMap (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸ (preimage f H).toSubgroup) ⟶ FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ f.hom <| fun _ h => h

/-- The universal morphism from the profinite completion to `P`. -/
noncomputable
/-
**ProfiniteGrp.ProfiniteCompletion.lift** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp.
ProfiniteCompletion`。
形式化陈述：lift (f : G ⟶ GrpCat.of P) : completion G ⟶ P
参数：f : G ⟶ GrpCat.of P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lift (f : G ⟶ GrpCat.of P) : completion G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app _ ≫ (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      -- TODO: `dsimp` should handle this `change`; investigate missing simp lemmas in the
      -- `ProfiniteGrp` / `CompHausLike` API.
      change quotientMap f Y (x <| preimage f Y) =
        P.diagram.map g (quotientMap _ _ <| x <| preimage f X)
      have := hx <| preimage_le (f := f) g.le |>.hom
      obtain ⟨t, ht⟩ : ∃ g : G, QuotientGroup.mk g = x (preimage f X) :=
        QuotientGroup.mk_surjective (x (preimage f X))
      rw [← this, ← ht]
      have := P.cone.π.naturality g
      apply_fun fun q => q (f t) at this
      exact this
  }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**ProfiniteGrp.ProfiniteCompletion.lift_eta** 是 Mathlib 中的一个引理，位于命名空间 `Profinite
Grp.ProfiniteCompletion`。
形式化陈述：lift_eta (f : G ⟶ GrpCat.of P) : eta G ≫ (forget₂ _ _).map (lift f) = f
参数：f : G ⟶ GrpCat.of P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_right`：cancel_iso_hom_right {X Y Z : C
} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = f' ≫ g.hom ↔ f = f'
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `ProfiniteGrp.instIsTopologicalGroupCarrierToTopTotallyDisconnectedSpaceP
tProfiniteLimitConeCompForget₂ContinuousMonoidHomToProfiniteContinuousMap`：∀ {J 
: Type v} [inst : CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J 
ProfiniteGrp.{max v u}),   IsTopologicalGroup ↑(Profini…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma lift_eta (f : G ⟶ GrpCat.of P) : eta G ≫ (forget₂ _ _).map (lift f) = f := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc, ← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

@[to_additive]
/-
**ProfiniteGrp.ProfiniteCompletion.lift_unique** 是 Mathlib 中的一个引理，位于命名空间 `Profin
iteGrp.ProfiniteCompletion`。
形式化陈述：lift_unique (f g : completion G ⟶ P) (h : eta G ≫ (forget₂ _ _).map f = et
a G ≫ (forget₂ _ _).map g) : f = g
参数：f g : completion G ⟶ P；h : eta G ≫ (forget₂ _ _).map f = eta G ≫ (forget₂ _ _
).map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProfiniteGrp.hom_ext`：hom_ext {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf
 : f.hom = g.hom) : f = g
· 使用定理 `ContinuousMonoidHom.ext`：ext {f g : A ->ₜ* B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用引理 `ProfiniteGrp.ProfiniteCompletion.denseRange`：denseRange : DenseRange (et
aFn G)
· 使用定理 `ContinuousMonoidHom.continuous_toFun`：∀ {A : Type u_2} {B : Type u_3} [i
nst : Monoid A] [inst_1 : Monoid B] [inst_2 : TopologicalSpace A]   [inst_3 : To
pologicalSpace B] (self : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
lemma lift_unique (f g : completion G ⟶ P)
    (h : eta G ≫ (forget₂ _ _).map f = eta G ≫ (forget₂ _ _).map g) : f = g := by
  ext x
  apply congrFun
  refine (denseRange (G := G)).equalizer f.hom.continuous_toFun g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using! (ConcreteCategory.congr_hom h y)

end ProfiniteCompletion

/-- The profinite completion functor. -/
@[simps]
/-
**ProfiniteGrp.profiniteCompletion** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u} where obj G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The profinite completion functor.
-/
noncomputable def profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u} where
  obj G := ProfiniteCompletion.completion G
  map f := ProfiniteCompletion.lift <| f ≫ ProfiniteCompletion.eta _
  map_id G := by
    apply ProfiniteCompletion.lift_unique
    cat_disch
  map_comp f g := by
    apply ProfiniteCompletion.lift_unique
    cat_disch

namespace ProfiniteCompletion

/-- The hom-set equivalence exhibiting the adjunction. -/
noncomputable
/-
**ProfiniteGrp.ProfiniteCompletion.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Profinite
Grp.ProfiniteCompletion`。
形式化陈述：homEquiv (G : GrpCat.{u}) (P : ProfiniteGrp.{u}) : (completion G ⟶ P) ≃ (G
 ⟶ GrpCat.of P) where toFun f
参数：G : GrpCat.{u}；P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def homEquiv (G : GrpCat.{u}) (P : ProfiniteGrp.{u}) :
    (completion G ⟶ P) ≃ (G ⟶ GrpCat.of P) where
  toFun f := eta G ≫ (forget₂ _ _).map f
  invFun f := lift f
  left_inv f := by apply lift_unique; simp
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The profinite completion is left adjoint to the forgetful functor. -/
noncomputable
/-
**ProfiniteGrp.ProfiniteCompletion.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `Profini
teGrp.ProfiniteCompletion`。
形式化陈述：adjunction : profiniteCompletion ⊣ forget₂ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def adjunction : profiniteCompletion ⊣ forget₂ _ _ :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      apply lift_unique
      simp [homEquiv]
  }

end ProfiniteCompletion

end ProfiniteGrp

