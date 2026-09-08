/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei, Anatole Dedecker
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Setoid.Basic

/-!
# Bourbaki Strict Maps

This file defines Bourbaki strict maps (`Topology.IsStrictMap`) and proves some of their
basic properties.

A map `f : X → Y` between topological spaces is called *strict* in the sense of Bourbaki
if the natural corestriction to its image (i.e., `Set.rangeFactorization f`) is a quotient map.
Equivalently, these are precisely the maps for which the first isomorphism
theorem yields a homeomorphism: the canonical bijection `X ⧸ ker f ≃ range f`
is a homeomorphism if and only if `f` is strict. This provides a natural
generalization of quotient maps to non-surjective maps.

Many important classes of maps are automatically continuous strict maps, including:
- continuous open maps (`IsOpenMap.isStrictMap`);
- continuous closed maps (`IsClosedMap.isStrictMap`).

## Equivalent characterizations

We provide several equivalent ways to characterize a strict map `f`:
* `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange`: `f` is strict if and only if
  the canonical bijection `Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism.
* `Topology.isStrictMap_iff_isEmbedding_kerLift`: `f` is strict if and only if
  the canonical injection `Quotient (Setoid.ker f) → Y` (`Setoid.kerLift f`) is an embedding.
-/

@[expose] public section

open Function Set Topology Setoid

namespace Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {g : Y → Z}

variable (f) in
/-- A map is a strict map in the sense of Bourbaki if the natural map to its image
is a quotient map. -/
/-
**Topology.IsStrictMap** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：IsStrictMap : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map is a strict map in the sense of Bourbaki if the natural map to its image
is a quotient map.
-/
def IsStrictMap : Prop :=
  IsQuotientMap (Set.rangeFactorization f)
/-
**Topology.isStrictMap_iff_isQuotientMap_rangeFactorization** 是 Mathlib 中的一个引理，位
于命名空间 `Topology`。
形式化陈述：isStrictMap_iff_isQuotientMap_rangeFactorization : IsStrictMap f ↔ IsQuoti
entMap (Set.rangeFactorization f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isStrictMap_iff_isQuotientMap_rangeFactorization :
    IsStrictMap f ↔ IsQuotientMap (Set.rangeFactorization f) :=
  Iff.rfl

/-- A map is a strict map if and only if the canonical bijection
`Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism. -/
/-
**Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange** 是 Mathlib 中的一个定理
，位于命名空间 `Topology`。
形式化陈述：isStrictMap_iff_isHomeomorph_quotientKerEquivRange : IsStrictMap f ↔ IsHom
eomorph (Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) -> Set.range f
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Topology.IsQuotientMap.of_comp_isQuotientMap`：∀ {X : Type u_1} {Y : Type
 u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst
_1 : TopologicalSpace Y] [inst_2 :…
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…

--- 原说明 ---
A map is a strict map if and only if the canonical bijection
`Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism.
-/
theorem isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔
      IsHomeomorph (Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) → Set.range f) := by
  simp only [IsStrictMap, isHomeomorph_iff_isQuotientMap_injective, Equiv.injective, and_true]
  exact ⟨fun h => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h,
         fun h ↦ h.comp isQuotientMap_quotient_mk'⟩

/-- The homeomorphism `Quotient (Setoid.ker f) ≃ₜ Set.range f` given by a strict map `f`.
This is the homeomorphism obtained from the first isomorphism theorem. -/
/-
**Topology._root_.Homeomorph.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `To
pology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism `Quotient (Setoid.ker f) ≃ₜ Set.range f` given by a strict map
 `f`.
This is the homeomorphism obtained from the first isomorphism theorem.
-/
noncomputable def _root_.Homeomorph.quotientKerEquivRange (hf : IsStrictMap f) :
    Quotient (Setoid.ker f) ≃ₜ Set.range f :=
  (isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.quotientKerEquivRange :=
  Homeomorph.quotientKerEquivRange

/-- A map is a strict map if and only if the canonical injection `Quotient (Setoid.ker f) → Y`
(`Setoid.kerLift f`) is an embedding. -/
/-
**Topology.isStrictMap_iff_isEmbedding_kerLift** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy`。
形式化陈述：isStrictMap_iff_isEmbedding_kerLift : IsStrictMap f ↔ IsEmbedding (Setoid.
kerLift f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolog
icalSpace Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)

--- 原说明 ---
A map is a strict map if and only if the canonical injection `Quotient (Setoid.k
er f) → Y`
(`Setoid.kerLift f`) is an embedding.
-/
theorem isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (Setoid.kerLift f) := by
  simp only [isStrictMap_iff_isHomeomorph_quotientKerEquivRange,
    isHomeomorph_iff_isEmbedding_surjective, Equiv.surjective, and_true]
  exact (IsEmbedding.of_comp_iff .subtypeVal).symm

/-- A strict map is continuous, since the range factorization is continuous. -/
/-
**Topology.IsStrictMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsStrictMa
p`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Topology.IsStrictMap f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_rangeFactorization_iff`：continuous_rangeFactorization_iff {f 
: X -> Y} : Continuous (rangeFactorization f) ↔ Continuous f
· 使用定理 `Topology.IsQuotientMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsQ
uotientMap f → Continuo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isStrictMap_iff_isQuotientMap_rangeFactorization`：isStrictMap_i
ff_isQuotientMap_rangeFactorization : IsStrictMap f ↔ IsQuotientMap (Set.rangeFa
ctorization f)

--- 原说明 ---
A strict map is continuous, since the range factorization is continuous.
-/
lemma IsStrictMap.continuous {f : X → Y} (hf : IsStrictMap f) : Continuous f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at hf
  exact continuous_rangeFactorization_iff.mp hf.continuous

/-- A open continuous map is a strict map. -/
/-
**Topology._root_.IsOpenMap.isStrictMap** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A open continuous map is a strict map.
-/
lemma _root_.IsOpenMap.isStrictMap (ho : IsOpenMap f) (h_cont : Continuous f) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (ho.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsOpenMap.isStrictMap :=
  IsOpenMap.isStrictMap

/-- A closed continuous map is a strict map. -/
/-
**Topology._root_.IsClosedMap.isStrictMap** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed continuous map is a strict map.
-/
lemma _root_.IsClosedMap.isStrictMap (hc : IsClosedMap f) (h_cont : Continuous f) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (hc.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsClosedMap.isStrictMap :=
  IsClosedMap.isStrictMap

/-- A homeomorphism is a strict map. -/
/-
**Topology._root_.IsHomeomorph.isStrictMap** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism is a strict map.
-/
lemma _root_.IsHomeomorph.isStrictMap (f_homeo : IsHomeomorph f) :
    IsStrictMap f :=
  f_homeo.isOpenMap.isStrictMap f_homeo.continuous

@[deprecated (since := "2026-07-10")] protected alias IsHomeomorph.isStrictMap :=
  IsHomeomorph.isStrictMap

/-- The identity is a strict map. -/
/-
**Topology.IsStrictMap.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsStrictMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], Topology.IsStrictMap id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorph.isStrictMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Topo
logy.IsStrictM…
· 使用定理 `IsHomeomorph.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsHomeomo
rph id

--- 原说明 ---
The identity is a strict map.
-/
lemma IsStrictMap.id : IsStrictMap (id : X → X) := IsHomeomorph.id.isStrictMap

/-- Assume that `f : X → Y` is a quotient map. Then `g : Y → Z` is strict
if and only if `g ∘ f` is strict. -/
/-
**Topology.IsQuotientMap.isStrictMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQ
uotientMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : X → Y} {g : 
Y → Z},   Topology.IsQuotientMap f → (Topology.IsStrictMap g ↔ Topology.IsStrict
Map (g ∘ f))
参数：Topology.IsStrictMap g ↔ Topology.IsStrictMap (g ∘ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsQuotientMap.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z :
 Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topol
ogicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h

--- 原说明 ---
Assume that `f : X → Y` is a quotient map. Then `g : Y → Z` is strict
if and only if `g ∘ f` is strict.
-/
lemma IsQuotientMap.isStrictMap_iff (f_quot : IsQuotientMap f) :
    IsStrictMap g ↔ IsStrictMap (g ∘ f) := by
  set Φ : range (g ∘ f) ≃ₜ range g := .setCongr <| f_quot.surjective.range_comp g
  have key : rangeFactorization g ∘ f = Φ ∘ rangeFactorization (g ∘ f) := rfl
  simp_rw [isStrictMap_iff_isQuotientMap_rangeFactorization, ← f_quot.of_comp_iff, key]
  exact ⟨fun H ↦ by simpa using! Φ.symm.isQuotientMap.comp H, fun H ↦ Φ.isQuotientMap.comp H⟩

/-- A quotient map is strict. See also `isQuotientMap_iff_isStrictMap_surjective`. -/
/-
**Topology.IsQuotientMap.isStrictMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuoti
entMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Topology.IsQuotientMap f → Topology.IsStrictMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsQuotientMap.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst
_2 : TopologicalSpace Z] {f …
· 使用定理 `Topology.IsStrictMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsStrictMap id

--- 原说明 ---
A quotient map is strict. See also `isQuotientMap_iff_isStrictMap_surjective`.
-/
lemma IsQuotientMap.isStrictMap (f_quot : IsQuotientMap f) :
    IsStrictMap f :=
  f_quot.isStrictMap_iff.mp .id

/-- Assume that `g : Y → Z` is an embedding. Then `f : X → Y` is strict
if and only if `g ∘ f` is strict. -/
/-
**Topology.IsEmbedding.isStrictMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmb
edding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : X → Y} {g : 
Y → Z},   Topology.IsEmbedding g → (Topology.IsStrictMap f ↔ Topology.IsStrictMa
p (g ∘ f))
参数：Topology.IsStrictMap f ↔ Topology.IsStrictMap (g ∘ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolog
icalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `Homeomorph.self_comp_symm`：self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id

--- 原说明 ---
Assume that `g : Y → Z` is an embedding. Then `f : X → Y` is strict
if and only if `g ∘ f` is strict.
-/
lemma IsEmbedding.isStrictMap_iff (g_emb : IsEmbedding g) :
    IsStrictMap f ↔ IsStrictMap (g ∘ f) := by
  set Φ : Quotient (Setoid.ker (g ∘ f)) ≃ₜ Quotient (Setoid.ker (f)) :=
    Homeomorph.Quotient.congrRight (fun _ _ ↦ by simp [g_emb.injective.eq_iff])
  have key : g ∘ kerLift f ∘ Φ = kerLift (g ∘ f) :=
    funext <| Quotient.ind fun _ ↦ rfl
  simp_rw [isStrictMap_iff_isEmbedding_kerLift, ← g_emb.of_comp_iff, ← key]
  exact ⟨fun H ↦ H.comp Φ.isEmbedding,
    fun H ↦ by simpa [comp_assoc] using H.comp Φ.symm.isEmbedding⟩

/-- An embedding is strict. See also `isEmbedding_iff_isStrictMap_injective`. -/
/-
**Topology.IsEmbedding.isStrictMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddi
ng`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Topology.IsEmbedding f → Topology.IsStrictMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsEmbedding.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2
 : TopologicalSpace Z] {f …
· 使用定理 `Topology.IsStrictMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsStrictMap id

--- 原说明 ---
An embedding is strict. See also `isEmbedding_iff_isStrictMap_injective`.
-/
lemma IsEmbedding.isStrictMap (f_emb : IsEmbedding f) :
    IsStrictMap f :=
  f_emb.isStrictMap_iff.mp .id

/-- Quotient maps are precisely surjective strict maps. -/
/-
**Topology.isQuotientMap_iff_isStrictMap_surjective** 是 Mathlib 中的一个引理，位于命名空间 `T
opology`。
形式化陈述：isQuotientMap_iff_isStrictMap_surjective : IsQuotientMap f ↔ IsStrictMap f
 ∧ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isStrictMap`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.Is
QuotientMap f → Topology…
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isStrictMap_iff_isQuotientMap_rangeFactorization`：isStrictMap_i
ff_isQuotientMap_rangeFactorization : IsStrictMap f ↔ IsQuotientMap (Set.rangeFa
ctorization f)

--- 原说明 ---
Quotient maps are precisely surjective strict maps.
-/
lemma isQuotientMap_iff_isStrictMap_surjective :
    IsQuotientMap f ↔ IsStrictMap f ∧ Surjective f := by
  refine ⟨fun H ↦ ⟨H.isStrictMap, H.surjective⟩, fun ⟨f_strict, f_surj⟩ ↦ ?_⟩
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at f_strict
  set Φ : range f ≃ₜ Y := .trans (.setCongr f_surj.range_eq) (Homeomorph.Set.univ Y)
  exact Φ.isQuotientMap.comp f_strict

/-- Embeddings are precisely injective strict maps. -/
/-
**Topology.isEmbedding_iff_isStrictMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `Topo
logy`。
形式化陈述：isEmbedding_iff_isStrictMap_injective : IsEmbedding f ↔ IsStrictMap f ∧ In
jective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isStrictMap`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsEm
bedding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.isStrictMap_iff_isEmbedding_kerLift`：isStrictMap_iff_isEmbeddin
g_kerLift : IsStrictMap f ↔ IsEmbedding (Setoid.kerLift f)
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
Embeddings are precisely injective strict maps.
-/
lemma isEmbedding_iff_isStrictMap_injective :
    IsEmbedding f ↔ IsStrictMap f ∧ Injective f := by
  refine ⟨fun H ↦ ⟨H.isStrictMap, H.injective⟩, fun ⟨f_strict, f_inj⟩ ↦ ?_⟩
  rw [isStrictMap_iff_isEmbedding_kerLift] at f_strict
  set Φ : Quotient (ker f) ≃ₜ X :=
    (Homeomorph.Quotient.congrRight <| by simp [f_inj.eq_iff]).trans Homeomorph.quotientBot
  exact f_strict.comp Φ.symm.isEmbedding

/-- Homeomorphisms are precisely bijective strict maps. -/
/-
**Topology.isHomeomorph_iff_isStrictMap_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology`。
形式化陈述：isHomeomorph_iff_isStrictMap_bijective : IsHomeomorph f ↔ IsStrictMap f ∧ 
Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Homeomorphisms are precisely bijective strict maps.
-/
lemma isHomeomorph_iff_isStrictMap_bijective :
    IsHomeomorph f ↔ IsStrictMap f ∧ Bijective f := by
  simp [isHomeomorph_iff_isEmbedding_surjective, isEmbedding_iff_isStrictMap_injective, Bijective,
    and_assoc]

/-- Strict maps are preserved when precomposing with a homeomorphism. -/
/-
**Topology._root_.Homeomorph.isStrictMap_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strict maps are preserved when precomposing with a homeomorphism.
-/
lemma _root_.Homeomorph.isStrictMap_comp_iff (e : X ≃ₜ Y) {f : Y → Z} :
    IsStrictMap (f ∘ e) ↔ IsStrictMap f :=
  e.isQuotientMap.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.isStrictMap_comp_iff :=
  Homeomorph.isStrictMap_comp_iff

/-- Strict maps are preserved when postcomposing with a homeomorphism. -/
/-
**Topology._root_.Homeomorph.comp_isStrictMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strict maps are preserved when postcomposing with a homeomorphism.
-/
lemma _root_.Homeomorph.comp_isStrictMap_iff (e : Y ≃ₜ Z) {f : X → Y} :
    IsStrictMap (e ∘ f) ↔ IsStrictMap f :=
  e.isEmbedding.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.comp_isStrictMap_iff :=
  Homeomorph.comp_isStrictMap_iff

end Topology

