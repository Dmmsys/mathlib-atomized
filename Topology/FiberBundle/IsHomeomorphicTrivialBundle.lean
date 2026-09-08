/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Constructions.SumProd

/-!
# Maps equivariantly-homeomorphic to projection in a product

This file contains the definition `IsHomeomorphicTrivialFiberBundle F p`, a Prop saying that a
map `p : Z → B` between topological spaces is a "trivial fiber bundle" in the sense that there
exists a homeomorphism `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.  This is an abstraction which
is occasionally convenient in showing that a map is open, a quotient map, etc.

This material was formerly linked to the main definition of fiber bundles, but after a series of
refactors, there is no longer a direct connection.
-/

@[expose] public section

open Topology

variable {B : Type*} (F : Type*) {Z : Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace Z]

/-- A trivial fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `Prod.fst`. -/
/-
**IsHomeomorphicTrivialFiberBundle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsHomeomorphicTrivialFiberBundle (proj : Z -> B) : Prop
参数：proj : Z -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trivial fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `
proj`
to `Prod.fst`.
-/
def IsHomeomorphicTrivialFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x

namespace IsHomeomorphicTrivialFiberBundle

variable {F} {proj : Z → B}

/-
**IsHomeomorphicTrivialFiberBundle.proj_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomor
phicTrivialFiberBundle`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace Z] {proj : Z → B}, I
sHomeomorphicTrivialFiberBundle F proj → ∃ e, proj = Prod.fst ∘ ⇑e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem proj_eq (h : IsHomeomorphicTrivialFiberBundle F proj) :
    ∃ e : Z ≃ₜ B × F, proj = Prod.fst ∘ e :=
  ⟨h.choose, (funext h.choose_spec).symm⟩

/-- The projection from a trivial fiber bundle to its base is surjective. -/
/-
**IsHomeomorphicTrivialFiberBundle.surjective_proj** 是 Mathlib 中的一个定理，位于命名空间 `Is
HomeomorphicTrivialFiberBundle`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace Z] {proj : Z → B} [N
onempty F],   IsHomeomorphicTrivialFiberBundle F proj → Function.Surjective proj
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.proj_eq`：∀ {B : Type u_1} {F : Type u_2
} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [in
st_2 : TopologicalSpace Z] {pr…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The projection from a trivial fiber bundle to its base is surjective.
-/
protected theorem surjective_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Function.Surjective proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact Prod.fst_surjective.comp e.surjective

/-- The projection from a trivial fiber bundle to its base is continuous. -/
/-
**IsHomeomorphicTrivialFiberBundle.continuous_proj** 是 Mathlib 中的一个定理，位于命名空间 `Is
HomeomorphicTrivialFiberBundle`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace Z] {proj : Z → B}, I
sHomeomorphicTrivialFiberBundle F proj → Continuous proj
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.proj_eq`：∀ {B : Type u_1} {F : Type u_2
} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [in
st_2 : TopologicalSpace Z] {pr…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The projection from a trivial fiber bundle to its base is continuous.
-/
protected theorem continuous_proj (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Continuous proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact continuous_fst.comp e.continuous

/-- The projection from a trivial fiber bundle to its base is open. -/
/-
**IsHomeomorphicTrivialFiberBundle.isOpenMap_proj** 是 Mathlib 中的一个定理，位于命名空间 `IsH
omeomorphicTrivialFiberBundle`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace Z] {proj : Z → B}, I
sHomeomorphicTrivialFiberBundle F proj → IsOpenMap proj
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.proj_eq`：∀ {B : Type u_1} {F : Type u_2
} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [in
st_2 : TopologicalSpace Z] {pr…
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `isOpenMap_fst`：isOpenMap_fst : IsOpenMap (@Prod.fst X Y)
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The projection from a trivial fiber bundle to its base is open.
-/
protected theorem isOpenMap_proj (h : IsHomeomorphicTrivialFiberBundle F proj) :
    IsOpenMap proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact isOpenMap_fst.comp e.isOpenMap

/-- The projection from a trivial fiber bundle to its base is open. -/
/-
**IsHomeomorphicTrivialFiberBundle.isQuotientMap_proj** 是 Mathlib 中的一个定理，位于命名空间 
`IsHomeomorphicTrivialFiberBundle`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace Z] {proj : Z → B} [N
onempty F],   IsHomeomorphicTrivialFiberBundle F proj → Topology.IsQuotientMap p
roj
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `IsHomeomorphicTrivialFiberBundle.isOpenMap_proj`：∀ {B : Type u_1} {F : T
ype u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : TopologicalSpace Z] {pr…
· 使用定理 `IsHomeomorphicTrivialFiberBundle.continuous_proj`：∀ {B : Type u_1} {F : 
Type u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace 
F]   [inst_2 : TopologicalSpace Z] {pr…
· 使用定理 `IsHomeomorphicTrivialFiberBundle.surjective_proj`：∀ {B : Type u_1} {F : 
Type u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace 
F]   [inst_2 : TopologicalSpace Z] {pr…

--- 原说明 ---
The projection from a trivial fiber bundle to its base is open.
-/
protected theorem isQuotientMap_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    IsQuotientMap proj :=
  h.isOpenMap_proj.isQuotientMap h.continuous_proj h.surjective_proj

end IsHomeomorphicTrivialFiberBundle

/-- The first projection in a product is a trivial fiber bundle. -/
/-
**isHomeomorphicTrivialFiberBundle_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isHomeomorphicTrivialFiberBundle_fst : IsHomeomorphicTrivialFiberBundle F 
(Prod.fst : B × F -> B)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection in a product is a trivial fiber bundle.
-/
theorem isHomeomorphicTrivialFiberBundle_fst :
    IsHomeomorphicTrivialFiberBundle F (Prod.fst : B × F → B) :=
  ⟨Homeomorph.refl _, fun _x => rfl⟩

/-- The second projection in a product is a trivial fiber bundle. -/
/-
**isHomeomorphicTrivialFiberBundle_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isHomeomorphicTrivialFiberBundle_snd : IsHomeomorphicTrivialFiberBundle F 
(Prod.snd : F × B -> B)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection in a product is a trivial fiber bundle.
-/
theorem isHomeomorphicTrivialFiberBundle_snd :
    IsHomeomorphicTrivialFiberBundle F (Prod.snd : F × B → B) :=
  ⟨Homeomorph.prodComm _ _, fun _x => rfl⟩
