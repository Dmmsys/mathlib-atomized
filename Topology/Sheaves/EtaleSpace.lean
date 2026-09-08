/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Etale space of a presheaf

Given a presheaf `F` on a topological space `X`,
its *etale space* is the space of pairs `(base, germ)`,
where `base` is a point of `X`, and `germ` is an element of the stalk of `F` at `base`.

This space is equipped with the following topology.
For each open set `U` and a section `s` of `F` over `U`,
the set of germs of `s` at points `x ∈ U` is an open set in the etale space.

## Main results

- `TopCat.Presheaf.EtaleSpace.eventually_nhds`. If `s` is a section of `F` over `U`
  with germ at `g.base` equal to `g.germ`,
  then a neighborhood of `g` consists of germs of `s` at points `x ∈ U`.

- `TopCat.Presheaf.EtaleSpace.isCoveringMap_base`.
  Let `F` be a presheaf with the following property.

  For each `x`, there exists an open neighborhood `U ∋ x` such that for each `y ∈ U`,
  the map `Presheaf.germ F U y hyU` from sections of `F` over `U` to the stalk at `y`
  is bijective.

  Then the projection from the etale space of `F` to the base is a covering map.
-/

public section

open Function Set CategoryTheory TopologicalSpace Opposite Filter
open scoped Topology

namespace TopCat.Presheaf

universe v u w
variable {X : TopCat.{v}} {C : Type u} [Category.{v} C] {CC : C → Type v} {FC : C → C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [Limits.HasColimits.{v} C]

/-- Etale space of a presheaf. -/
/-
**TopCat.Presheaf.EtaleSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopCat.Presheaf`。
形式化陈述：{X : TopCat} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {CC : C → Type v} →         {FC : C → C → Type w} →           [inst_
1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] →             [CategoryTheory.Co
ncreteCategory C FC] →               [CategoryTheory.Limits.HasColimits C] → Top
Cat.Presheaf C X → Type v
参数：X Y : C；FC X Y；CC X；CC Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Etale space of a presheaf.
-/
structure EtaleSpace (F : Presheaf C X) where
  /-- The base point. -/
  base : X
  /-- A germ at `base` (formally, an element of the stalk of `F` at `base`). -/
  germ : ToType (F.stalk base)

namespace EtaleSpace

/-
**TopCat.Presheaf.EtaleSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf.EtaleSp
ace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Presheaf C X) : TopologicalSpace F.EtaleSpace :=
  .generateFrom
    {{g | ∃ h, g.germ = F.germ U g.base h f} | (U : Opens X) (f : ToType (F.obj <| op U))}

variable {F : Presheaf C X}

/-- If `s` is a section of a presheaf `F` over `U` with germ at `g.base` equal to `g.germ`,
then a neighborhood of `g` consists of germs of `s` at points `x ∈ U`. -/
/-
**TopCat.Presheaf.EtaleSpace.eventually_nhds** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.P
resheaf.EtaleSpace`。
形式化陈述：∀ {X : TopCat} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {CC 
: C → Type v} {FC : C → C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC
 X) (CC Y)] [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : Category
Theory.Limits.HasColimits C] {F : TopCat.Presheaf C X} (g : F.EtaleSpace)   {U :
 TopologicalSpace.Opens ↑X} (h : g.base ∈ U) (s : CategoryTheory.ToType (F.obj (
Opposite.op U))),   (CategoryTheory.ConcreteCategory.hom (F.germ U g.base h)) s 
= g.germ →     ∀ᶠ (g' : F.EtaleSpace) in nhds g,       ∃ (hgU : g'.base ∈ U), g'
.germ = (CategoryTheory.ConcreteCategory.hom (F.germ U g'.base hgU)) s
参数：X Y : C；FC X Y；CC X；CC Y；g : F.EtaleSpace；h : g.base ∈ U；s : CategoryTheory.T
oType (F.obj (Opposite.op U))；CategoryTheory.ConcreteCategory.hom (F.germ U g.ba
se h)；g' : F.EtaleSpace；hgU : g'.base ∈ U；CategoryTheory.ConcreteCategory.hom (F
.germ U g'.base hgU)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_exists`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{p : ι → Prop} {f : Exists p → α},   ⨅ (x : Exists p), f x = ⨅ i, ⨅ (h : p i), f
 …
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s

--- 原说明 ---
If `s` is a section of a presheaf `F` over `U` with germ at `g.base` equal to `g
.germ`,
then a neighborhood of `g` consists of germs of `s` at points `x ∈ U`.
-/
protected theorem eventually_nhds (g : EtaleSpace F) {U : Opens X} (h : g.base ∈ U)
    (s : ToType (F.obj (op U))) (hs : F.germ U g.base h s = g.germ) :
    ∀ᶠ g' : EtaleSpace F in 𝓝 g, ∃ hgU : g'.base ∈ U, g'.germ = F.germ U g'.base hgU s := by
  simp only [nhds_generateFrom, Filter.Eventually, mem_ofPred_eq, iInf_and, iInf_exists]
  refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_iInf_of_mem U <| mem_iInf_of_mem s <|
    mem_iInf_of_mem rfl <| mem_principal_self _
  simp [*]

variable [Limits.PreservesFilteredColimits (forget C)]

variable (F) in
@[fun_prop]
/-
**TopCat.Presheaf.EtaleSpace.continuous_base** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.P
resheaf.EtaleSpace`。
形式化陈述：continuous_base : Continuous (base (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `TopologicalSpace.Opens.instCanLiftSetCoeIsOpen`：∀ {α : Type u_2} [inst :
 TopologicalSpace α], CanLift (Set α) (TopologicalSpace.Opens α) SetLike.coe IsO
pen
· 使用定理 `TopCat.Presheaf.exists_le_germ_eq`：exists_le_germ_eq (F : X.Presheaf C) 
{x : X} (t : ToType (stalk.{v, u} F x)) {V : Opens X} (hV : x in V) : exists U <
= V, exists (m : x in U…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `TopCat.Presheaf.EtaleSpace.eventually_nhds`：∀ {X : TopCat} {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {CC : C → Type v} {FC : C → C → Type w
}   [inst_1 : (X Y : C) → FunLik…
-/
theorem continuous_base : Continuous (base (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
  rintro U ⟨hxU, hUo⟩
  lift U to Opens X using hUo
  rcases F.exists_le_germ_eq x.germ hxU with ⟨V, hVU, hxV, f, hf⟩
  refine x.eventually_nhds hxV f hf |>.mono ?_
  aesop
/-
**TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间
 `TopCat.Presheaf.EtaleSpace`。
形式化陈述：exists_section_of_tendsto {α : Type*} {l : Filter α} {g : α -> F.EtaleSpac
e} {g₀ : F.EtaleSpace} (h : Tendsto g l (𝓝 g₀)) : exists (U : Opens X), g₀.base 
in U ∧ exists (f : ToType (F.obj (op U))), forallᶠ a in l, exists ha : (g a).bas
e in U, (g a).germ = F.germ U (g a).base ha f
参数：h : Tendsto g l (𝓝 g₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `TopCat.Presheaf.EtaleSpace.eventually_nhds`：∀ {X : TopCat} {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {CC : C → Type v} {FC : C → C → Type w
}   [inst_1 : (X Y : C) → FunLik…
-/
theorem exists_section_of_tendsto {α : Type*} {l : Filter α} {g : α → F.EtaleSpace}
    {g₀ : F.EtaleSpace} (h : Tendsto g l (𝓝 g₀)) :
    ∃ (U : Opens X), g₀.base ∈ U ∧ ∃ (f : ToType (F.obj (op U))),
      ∀ᶠ a in l, ∃ ha : (g a).base ∈ U, (g a).germ = F.germ U (g a).base ha f := by
  rcases F.exists_germ_eq g₀.germ with ⟨U, hU, s, hs⟩
  use U, hU, s
  exact h.eventually <| g₀.eventually_nhds hU s hs

/-- Let `F` be a `C`-valued presheaf on `X`.
Let `U` be an open set on `X` such that for each `x ∈ U`, the `germ` map is bijective, i.e.,
every germ can be extended to a unique section over `U`.

Then for each `x ∈ U`, the preimage of `U` under `EtaleSpace.base`
is homeomorphic to the product of `U` and the stalk of `F` at `x` with discrete topology.
-/
@[expose, simps apply_fst]
/-
**TopCat.Presheaf.EtaleSpace.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Preshe
af.EtaleSpace`。
形式化陈述：homeomorph (U : Opens X) (hF_bij : forall (x : X) (hx : x in U), Bijective
 (F.germ U x hx)) (x : X) (hx : x in U) : (base (F
参数：U : Opens X；hF_bij : forall (x : X) (hx : x in U), Bijective (F.germ U x hx)；
x : X；hx : x in U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F` be a `C`-valued presheaf on `X`.
Let `U` be an open set on `X` such that for each `x ∈ U`, the `germ` map is bije
ctive, i.e.,
every germ can be extended to a unique section over `U`.

Then for each `x ∈ U`, the preimage of `U` under `EtaleSpace.base`
is homeomorphic to the product of `U` and the stalk of `F` at `x` with discrete 
topology.
-/
noncomputable def homeomorph (U : Opens X)
    (hF_bij : ∀ (x : X) (hx : x ∈ U), Bijective (F.germ U x hx))
    (x : X) (hx : x ∈ U) :
    (base (F := F) ⁻¹' U) ≃ₜ U × WithDiscreteTopology (ToType (F.stalk x)) where
  toFun s := (⟨s.1.base, s.2⟩,
    .toTopology ⊥ <| F.germ U x hx <| surjInv (hF_bij s.1.base s.2).surjective s.1.germ)
  invFun
  | (⟨y, hy⟩, .toTopology _ g) => ⟨⟨y, F.germ U y hy <| surjInv (hF_bij x hx).surjective g⟩, hy⟩
  left_inv := by
    rintro ⟨⟨base, s⟩, hs⟩
    simp only
    congr 2
    rw [leftInverse_surjInv (hF_bij _ _), surjInv_eq (hF_bij _ _).surjective]
  right_inv := by
    rintro ⟨⟨y, hy⟩, ⟨g⟩⟩
    simp only
    congr
    rw [leftInverse_surjInv (hF_bij _ _), surjInv_eq (hF_bij _ _).surjective]
  continuous_toFun := by
    refine .prodMk (by fun_prop) ?_
    simp_rw [continuous_iff_continuousAt, ContinuousAt, nhds_discrete, tendsto_pure, nhds_subtype,
      eventually_comap]
    rintro ⟨g, hg⟩
    rcases hF_bij _ hg |>.surjective g.germ with ⟨f, hf⟩
    filter_upwards [g.eventually_nhds hg f hf]
    rintro _ ⟨hgU, hgf⟩ g' rfl
    congr 1
    rw [hgf, ← hf, leftInverse_surjInv (hF_bij _ _), leftInverse_surjInv (hF_bij _ _)]
  continuous_invFun := by
    simp_rw [continuous_iff_continuousAt, continuousAt_prod_of_discrete_right]
    rintro ⟨y, ⟨g⟩⟩
    simp only [ContinuousAt, nhds_subtype_eq_comap, tendsto_comap_iff, comp_def,
      nhds_generateFrom, tendsto_iInf, mem_ofPred_eq, tendsto_principal]
    rintro _ ⟨hmem, V, f, rfl⟩
    simp only [mem_ofPred_eq] at hmem
    rcases hmem with ⟨hyV, hgf⟩
    rcases F.germ_eq _ _ _ _ _ hgf with ⟨W, hyW, ιWU, ιWV, hW⟩
    filter_upwards [W.isOpen.preimage continuous_subtype_val |>.mem_nhds hyW] with z hz
    use ιWV.le hz
    rw [← F.germ_res_apply ιWU z hz, hW, F.germ_res_apply]

/-- Let `F` be a presheaf with the following property.

For each `x`, there exists an open neighborhood `U ∋ x` such that for each `y ∈ U`,
the map `Presheaf.germ F U y hyU` from sections of `F` over `U` to the stalk at `y`
is bijective.

Then the projection from the etale space of `F` to the base is a covering map. -/
/-
**TopCat.Presheaf.EtaleSpace.isCoveringMap_base** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t.Presheaf.EtaleSpace`。
形式化陈述：isCoveringMap_base (hF_bij : forall x, exists (U : Opens X), x in U ∧ fora
ll y (hyU : y in U), Bijective (F.germ U y hyU)) : IsCoveringMap (base (F
参数：hF_bij : forall x, exists (U : Opens X), x in U ∧ forall y (hyU : y in U), Bi
jective (F.germ U y hyU)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `instDiscreteTopologyWithDiscreteTopology`：∀ {α : Type u}, DiscreteTopolo
gy (WithDiscreteTopology α)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `TopCat.Presheaf.EtaleSpace.continuous_base`：continuous_base : Continuous
 (base (F
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.EtaleSpace.homeomorph_apply_fst`：∀ {X : TopCat} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {CC : C → Type v} {FC : C → C → T
ype w}   [inst_1 : (X Y : C) → FunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Let `F` be a presheaf with the following property.

For each `x`, there exists an open neighborhood `U ∋ x` such that for each `y ∈ 
U`,
the map `Presheaf.germ F U y hyU` from sections of `F` over `U` to the stalk at 
`y`
is bijective.

Then the projection from the etale space of `F` to the base is a covering map.
-/
theorem isCoveringMap_base
    (hF_bij : ∀ x, ∃ (U : Opens X), x ∈ U ∧ ∀ y (hyU : y ∈ U), Bijective (F.germ U y hyU)) :
    IsCoveringMap (base (F := F)) := by
  refine fun x ↦ .to_isEvenlyCovered_preimage (I := WithDiscreteTopology (ToType (F.stalk x))) ?_
  use inferInstance
  rcases hF_bij x with ⟨U, hxU, hU_bij⟩
  use U, hxU, U.isOpen, U.isOpen.preimage (continuous_base F), homeomorph U hU_bij x hxU
  simp

end EtaleSpace

end TopCat.Presheaf

