/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei, Anatole Dedecker
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Strict Group Homomorphisms

In this file, we study homomorphisms of topological groups which are *strict* in the sense
of `Topology.IsStrictMap`.

We provide specialized variations of general facts about `IsStrictMap` for convenience.
But we also show that strict group homomorphisms enjoy some extra properties compared to general
strict maps. Namely, we provide:
* `isStrictMap_iff_isOpenQuotientMap_rangeRestrict`: `f` is a strict group homomorphism if
  and only if the `rangeRestrict` of `f` is an *open* quotient map. This ultimately relies
  on `MonoidHom.isOpenQuotientMap_of_isQuotientMap`.
* `isStrictMap_prodMap`: The product (in the sense of `MonoidHom.prodMap`) of strict group
  homomorphisms is strict. Note that this result is false for general maps; what makes things work
  in our context is that, unlike `IsQuotientMap`, `IsOpenQuotientMap` is stable under product.
-/

@[expose] public section

open Topology QuotientGroup

namespace MonoidHom

variable {G H G' H' : Type*} [Group G'] [Group H'] [Group G] [Group H] {f : G →* H} {g : G' →* H'}
  [TopologicalSpace G] [TopologicalSpace H]

/-- A group homomorphism is strict if and only if its `QuotientGroup.kerLift` is an embedding. -/
@[to_additive /-- An additive group homomorphism is strict if and only if its
`QuotientAddGroup.kerLift` is an embedding. -/]
/-
**MonoidHom.isStrictMap_iff_isEmbedding_kerLift** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
dHom`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {f : G
 →* H} [inst_2 : TopologicalSpace G]   [inst_3 : TopologicalSpace H], Topology.I
sStrictMap ⇑f ↔ Topology.IsEmbedding ⇑(QuotientGroup.kerLift f)
参数：QuotientGroup.kerLift f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Topology.IsQuotientMap.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst
_2 : TopologicalSpace Z] {f …
· 使用定理 `QuotientGroup.isQuotientMap_mk`：isQuotientMap_mk (N : Subgroup G) : IsQu
otientMap (mk : G -> G ⧸ N)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (kerLift f) := by
  -- Note: `G ⧸ MonoidHom.ker f` and `G ⧸ Setoid.ker f` are not definitionally equal, so
  -- using `Topology.isStrictMap_iff_isEmbedding_kerLift` is too painful here.
  simp_rw [isEmbedding_iff_isStrictMap_injective, kerLift_injective, and_true,
    (isQuotientMap_mk _).isStrictMap_iff]
  rfl

/-- A group homomorphism is strict if and only if the canonical isomorphism
`G ⧸ f.ker ≃ f.range` is a homeomorphism. -/
@[to_additive /-- An additive group homomorphism is strict if and only if the canonical isomorphism
`G ⧸ f.ker ≃ f.range` is a homeomorphism. -/]
/-
**MonoidHom.isStrictMap_iff_isHomeomorph_quotientKerEquivRange** 是 Mathlib 中的一个定
理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {f : G
 →* H} [inst_2 : TopologicalSpace G]   [inst_3 : TopologicalSpace H], Topology.I
sStrictMap ⇑f ↔ IsHomeomorph ⇑(QuotientGroup.quotientKerEquivRange f)
参数：QuotientGroup.quotientKerEquivRange f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Topology.IsQuotientMap.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst
_2 : TopologicalSpace Z] {f …
· 使用定理 `QuotientGroup.isQuotientMap_mk`：isQuotientMap_mk (N : Subgroup G) : IsQu
otientMap (mk : G -> G ⧸ N)
· 使用定理 `Topology.IsEmbedding.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2
 : TopologicalSpace Z] {f …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔ IsHomeomorph (quotientKerEquivRange f) := by
  -- Note: `G ⧸ MonoidHom.ker f` and `G ⧸ Setoid.ker f` are not definitionally equal, so
  -- using `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange` is too painful here.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    (isQuotientMap_mk _).isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl

/-- The isomorphism of topological groups `G ⧸ f.ker ≃ f.range` given by a strict group
homomorphism `f`. This is an avatar of the first isomorphism theorem. -/
@[to_additive /-- The isomorphism of topological additive groups `G ⧸ f.ker ≃ f.range` given by a
strict additive group homomorphism `f`. This is an avatar of the first isomorphism theorem. -/]
/-
**MonoidHom._root_.ContinuousMulEquiv.quotientKerEquivRange** 是 Mathlib 中的一个定义，位
于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def _root_.ContinuousMulEquiv.quotientKerEquivRange
    (hf : IsStrictMap f) : G ⧸ f.ker ≃ₜ* f.range where
  toMulEquiv := QuotientGroup.quotientKerEquivRange f
  __ := (f.isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

variable [IsTopologicalGroup G]

/-- A group homomorphism is strict if and only if its `rangeRestrict` is an open quotient map. -/
@[to_additive /-- An additive group homomorphism is strict if and only if its `rangeRestrict` is an
open quotient map. -/]
/-
**MonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict** 是 Mathlib 中的一个定理，位
于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {f : G
 →* H} [inst_2 : TopologicalSpace G]   [inst_3 : TopologicalSpace H] [IsTopologi
calGroup G], Topology.IsStrictMap ⇑f ↔ IsOpenQuotientMap ⇑f.rangeRestrict
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidHom.isOpenQuotientMap_iff_isQuotientMap`：MonoidHom.isOpenQuotientM
ap_iff_isQuotientMap {A : Type*} [Group A] [TopologicalSpace A] [ContinuousMul A
] {B : Type*} [Group B] [Topologica…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict :
    IsStrictMap f ↔ IsOpenQuotientMap f.rangeRestrict := by
  rw [isOpenQuotientMap_iff_isQuotientMap]
  rfl

variable [TopologicalSpace G'] [IsTopologicalGroup G'] [TopologicalSpace H']

/-- The product (in the sense of `MonoidHom.prodMap`) of group homomorphisms is strict if and only
if both homomorphisms are strict. -/
@[to_additive isStrictMap_prodMap_iff /-- The product (in the sense of `AddMonoidHom.prodMap`) of
additive group homomorphisms is strict if and only if both homomorphisms are strict. -/]
/-
**MonoidHom.isStrictMap_prodMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} {G' : Type u_3} {H' : Type u_4} [inst : Gr
oup G'] [inst_1 : Group H'] [inst_2 : Group G]   [inst_3 : Group H] {f : G →* H}
 {g : G' →* H'} [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace H]   [I
sTopologicalGroup G] [inst_7 : TopologicalSpace G'] [IsTopologicalGroup G'] [ins
t_9 : TopologicalSpace H'],   Topology.IsStrictMap ⇑(f.prodMap g) ↔ Topology.IsS
trictMap ⇑f ∧ Topology.IsStrictMap ⇑g
参数：f.prodMap g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidHom.range_prodMap`：range_prodMap {G' N' : Type*} [Group G'] [Group
 N'] (f : G ->* N) (g : G' ->* N') : (f.prodMap g).range = f.range.prod g.range
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.comp_isOpenQuotientMap_iff`：comp_isOpenQuotientMap_iff (e : Y
 ≃ₜ Z) {f : X -> Y} : IsOpenQuotientMap (e ∘ f) ↔ IsOpenQuotientMap f
· 使用定理 `MonoidHom.coe_prodMap`：coe_prodMap : ⇑(prodMap f g) = Prod.map f g
· 使用定理 `isOpenQuotientMap_prodMap_iff`：isOpenQuotientMap_prodMap_iff [Nonempty X
] [Nonempty Z] {f : X -> Y} {g : Z -> W} : IsOpenQuotientMap (Prod.map f g) ↔ Is
OpenQuotientMap f ∧…
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isStrictMap_prodMap_iff :
    IsStrictMap (f.prodMap g) ↔ IsStrictMap f ∧ IsStrictMap g := by
  simp_rw [MonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  let Φ : (f.prodMap g).range ≃ₜ f.range × g.range :=
    (Homeomorph.setCongr (by simp [Subgroup.coe_prod])).trans (Homeomorph.Set.prod _ _)
  have eq : Φ ∘ (f.prodMap g).rangeRestrict = f.rangeRestrict.prodMap g.rangeRestrict := rfl
  rw [← Φ.comp_isOpenQuotientMap_iff, eq, MonoidHom.coe_prodMap, isOpenQuotientMap_prodMap_iff]

/-- The product (in the sense of `MonoidHom.prodMap`) of strict group homomorphisms is strict. -/
@[to_additive isStrictMap_prodMap /-- The product (in the sense of `AddMonoidHom.prodMap`) of strict
additive group homomorphisms is strict. -/]
/-
**MonoidHom.isStrictMap_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} {G' : Type u_3} {H' : Type u_4} [inst : Gr
oup G'] [inst_1 : Group H'] [inst_2 : Group G]   [inst_3 : Group H] {f : G →* H}
 {g : G' →* H'} [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace H]   [I
sTopologicalGroup G] [inst_7 : TopologicalSpace G'] [IsTopologicalGroup G'] [ins
t_9 : TopologicalSpace H'],   Topology.IsStrictMap ⇑f → Topology.IsStrictMap ⇑g 
→ Topology.IsStrictMap ⇑(f.prodMap g)
参数：f.prodMap g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.isStrictMap_prodMap_iff`：∀ {G : Type u_1} {H : Type u_2} {G' :
 Type u_3} {H' : Type u_4} [inst : Group G'] [inst_1 : Group H'] [inst_2 : Group
 G]   [inst_3 : Group H…
-/
protected lemma isStrictMap_prodMap (hf : IsStrictMap f)
    (hg : IsStrictMap g) : IsStrictMap (f.prodMap g) :=
  MonoidHom.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩

-- TODO: Add the lemma `isStrictMap_piMap` once `MonoidHom.piMap` has been defined.

end MonoidHom

