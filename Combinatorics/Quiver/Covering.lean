/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.Common

/-!
# Covering

This file defines coverings of quivers as prefunctors that are bijective on the
so-called stars and costars at each vertex of the domain.

## Main definitions

* `Quiver.Star u` is the type of all arrows with source `u`;
* `Quiver.Costar u` is the type of all arrows with target `u`;
* `Prefunctor.star φ u` is the obvious function `star u → star (φ.obj u)`;
* `Prefunctor.costar φ u` is the obvious function `costar u → costar (φ.obj u)`;
* `Prefunctor.IsCovering φ` means that `φ.star u` and `φ.costar u` are bijections for all `u`;
* `Quiver.PathStar u` is the type of all paths with source `u`;
* `Prefunctor.pathStar u` is the obvious function `PathStar u → PathStar (φ.obj u)`.

## Main statements

* `Prefunctor.IsCovering.pathStar_bijective` states that if `φ` is a covering,
  then `φ.pathStar u` is a bijection for all `u`.
  In other words, every path in the codomain of `φ` lifts uniquely to its domain.

## TODO

Clean up the namespaces by renaming `Prefunctor` to `Quiver.Prefunctor`.

## Tags

Cover, covering, quiver, path, lift
-/

@[expose] public section


open Function Quiver

universe u v w

variable {U : Type _} [Quiver.{u} U] {V : Type _} [Quiver.{v} V] (φ : U ⥤q V) {W : Type _}
  [Quiver.{w} W] (ψ : V ⥤q W)

/-- The `Quiver.Star` at a vertex is the collection of arrows whose source is the vertex.
The type `Quiver.Star u` is defined to be `Σ (v : U), (u ⟶ v)`. -/
/-
**Quiver.Star** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Quiver.Star (u : U)
参数：u : U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Quiver.Star` at a vertex is the collection of arrows whose source is the ve
rtex.
The type `Quiver.Star u` is defined to be `Σ (v : U), (u ⟶ v)`.
-/
abbrev Quiver.Star (u : U) :=
  Σ v : U, u ⟶ v

/-- Constructor for `Quiver.Star`. Defined to be `Sigma.mk`. -/
/-
**Quiver.Star.mk** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Star`。
形式化陈述：{U : Type u_1} → [inst : Quiver U] → {u v : U} → (u ⟶ v) → Quiver.Star u
参数：u ⟶ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Quiver.Star`. Defined to be `Sigma.mk`.
-/
protected abbrev Quiver.Star.mk {u v : U} (f : u ⟶ v) : Quiver.Star u :=
  ⟨_, f⟩

/-- The `Quiver.Costar` at a vertex is the collection of arrows whose target is the vertex.
The type `Quiver.Costar v` is defined to be `Σ (u : U), (u ⟶ v)`. -/
/-
**Quiver.Costar** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Quiver.Costar (v : U)
参数：v : U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Quiver.Costar` at a vertex is the collection of arrows whose target is the 
vertex.
The type `Quiver.Costar v` is defined to be `Σ (u : U), (u ⟶ v)`.
-/
abbrev Quiver.Costar (v : U) :=
  Σ u : U, u ⟶ v

/-- Constructor for `Quiver.Costar`. Defined to be `Sigma.mk`. -/
/-
**Quiver.Costar.mk** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Costar`。
形式化陈述：{U : Type u_1} → [inst : Quiver U] → {u v : U} → (u ⟶ v) → Quiver.Costar v
参数：u ⟶ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Quiver.Costar`. Defined to be `Sigma.mk`.
-/
protected abbrev Quiver.Costar.mk {u v : U} (f : u ⟶ v) : Quiver.Costar v :=
  ⟨_, f⟩

/-- A prefunctor induces a map of `Quiver.Star` at every vertex. -/
@[simps]
/-
**Prefunctor.star** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Prefunctor.star (u : U) : Quiver.Star u -> Quiver.Star (φ.obj u)
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor induces a map of `Quiver.Star` at every vertex.
-/
def Prefunctor.star (u : U) : Quiver.Star u → Quiver.Star (φ.obj u) := fun F =>
  Quiver.Star.mk (φ.map F.2)

/-- A prefunctor induces a map of `Quiver.Costar` at every vertex. -/
@[simps]
/-
**Prefunctor.costar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Prefunctor.costar (u : U) : Quiver.Costar u -> Quiver.Costar (φ.obj u)
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor induces a map of `Quiver.Costar` at every vertex.
-/
def Prefunctor.costar (u : U) : Quiver.Costar u → Quiver.Costar (φ.obj u) := fun F =>
  Quiver.Costar.mk (φ.map F.2)

@[simp]
/-
**Prefunctor.star_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.star_apply {u v : U} (e : u ⟶ v) : φ.star u (Quiver.Star.mk e) 
= Quiver.Star.mk (φ.map e)
参数：e : u ⟶ v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prefunctor.star_apply {u v : U} (e : u ⟶ v) :
    φ.star u (Quiver.Star.mk e) = Quiver.Star.mk (φ.map e) :=
  rfl

@[simp]
/-
**Prefunctor.costar_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.costar_apply {u v : U} (e : u ⟶ v) : φ.costar v (Quiver.Costar.
mk e) = Quiver.Costar.mk (φ.map e)
参数：e : u ⟶ v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prefunctor.costar_apply {u v : U} (e : u ⟶ v) :
    φ.costar v (Quiver.Costar.mk e) = Quiver.Costar.mk (φ.map e) :=
  rfl
/-
**Prefunctor.star_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.star_comp (u : U) : (φ ⋙q ψ).star u = ψ.star (φ.obj u) ∘ φ.star
 u
参数：u : U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prefunctor.star_comp (u : U) : (φ ⋙q ψ).star u = ψ.star (φ.obj u) ∘ φ.star u :=
  rfl
/-
**Prefunctor.costar_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.costar_comp (u : U) : (φ ⋙q ψ).costar u = ψ.costar (φ.obj u) ∘ 
φ.costar u
参数：u : U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prefunctor.costar_comp (u : U) : (φ ⋙q ψ).costar u = ψ.costar (φ.obj u) ∘ φ.costar u :=
  rfl

/-- A prefunctor is a covering of quivers if it defines bijections on all stars and costars. -/
/-
**Prefunctor.IsCovering** 是 Mathlib 中的一个归纳类型，位于命名空间 `Prefunctor`。
形式化陈述：{U : Type u_1} → [inst : Quiver U] → {V : Type u_2} → [inst_1 : Quiver V] 
→ U ⥤q V → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor is a covering of quivers if it defines bijections on all stars and 
costars.
-/
protected structure Prefunctor.IsCovering : Prop where
  star_bijective : ∀ u, Bijective (φ.star u)
  costar_bijective : ∀ u, Bijective (φ.costar u)

@[simp]
/-
**Prefunctor.IsCovering.map_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.IsCovering.map_injective (hφ : φ.IsCovering) {u v : U} : Inject
ive fun f : u ⟶ v => φ.map f
参数：hφ : φ.IsCovering。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prefunctor.IsCovering.star_bijective`：∀ {U : Type u_1} [inst : Quiver U]
 {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), Fu
nction.Bijective (φ.star u…
-/
theorem Prefunctor.IsCovering.map_injective (hφ : φ.IsCovering) {u v : U} :
    Injective fun f : u ⟶ v => φ.map f := by
  rintro f g he
  have : φ.star u (Quiver.Star.mk f) = φ.star u (Quiver.Star.mk g) := by simpa using he
  simpa using (hφ.star_bijective u).left this
/-
**Prefunctor.IsCovering.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.IsCovering.comp (hφ : φ.IsCovering) (hψ : ψ.IsCovering) : (φ ⋙q
 ψ).IsCovering
参数：hφ : φ.IsCovering；hψ : ψ.IsCovering。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `Prefunctor.IsCovering.star_bijective`：∀ {U : Type u_1} [inst : Quiver U]
 {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), Fu
nction.Bijective (φ.star u…
· 使用定理 `Prefunctor.IsCovering.costar_bijective`：∀ {U : Type u_1} [inst : Quiver 
U] {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), 
Function.Bijective (φ.costar…
-/
theorem Prefunctor.IsCovering.comp (hφ : φ.IsCovering) (hψ : ψ.IsCovering) : (φ ⋙q ψ).IsCovering :=
  ⟨fun _ => (hψ.star_bijective _).comp (hφ.star_bijective _),
   fun _ => (hψ.costar_bijective _).comp (hφ.costar_bijective _)⟩
/-
**Prefunctor.IsCovering.of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.IsCovering.of_comp_right (hψ : ψ.IsCovering) (hφψ : (φ ⋙q ψ).Is
Covering) : φ.IsCovering
参数：hψ : ψ.IsCovering；hφψ : (φ ⋙q ψ).IsCovering。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Prefunctor.IsCovering.star_bijective`：∀ {U : Type u_1} [inst : Quiver U]
 {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), Fu
nction.Bijective (φ.star u…
· 使用定理 `Prefunctor.IsCovering.costar_bijective`：∀ {U : Type u_1} [inst : Quiver 
U] {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), 
Function.Bijective (φ.costar…
-/
theorem Prefunctor.IsCovering.of_comp_right (hψ : ψ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering) :
    φ.IsCovering :=
  ⟨fun _ => (Bijective.of_comp_iff' (hψ.star_bijective _) _).mp (hφψ.star_bijective _),
   fun _ => (Bijective.of_comp_iff' (hψ.costar_bijective _) _).mp (hφψ.costar_bijective _)⟩
/-
**Prefunctor.IsCovering.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.IsCovering.of_comp_left (hφ : φ.IsCovering) (hφψ : (φ ⋙q ψ).IsC
overing) (φsur : Surjective φ.obj) : ψ.IsCovering
参数：hφ : φ.IsCovering；hφψ : (φ ⋙q ψ).IsCovering；φsur : Surjective φ.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `Prefunctor.IsCovering.star_bijective`：∀ {U : Type u_1} [inst : Quiver U]
 {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), Fu
nction.Bijective (φ.star u…
· 使用定理 `Prefunctor.IsCovering.costar_bijective`：∀ {U : Type u_1} [inst : Quiver 
U] {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), 
Function.Bijective (φ.costar…
-/
theorem Prefunctor.IsCovering.of_comp_left (hφ : φ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering)
    (φsur : Surjective φ.obj) : ψ.IsCovering := by
  refine ⟨fun v => ?_, fun v => ?_⟩ <;> obtain ⟨u, rfl⟩ := φsur v
  exacts [(Bijective.of_comp_iff _ (hφ.star_bijective u)).mp (hφψ.star_bijective u),
    (Bijective.of_comp_iff _ (hφ.costar_bijective u)).mp (hφψ.costar_bijective u)]

/-- The star of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
star and the costar at `u` in the original quiver. -/
/-
**Quiver.symmetrifyStar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quiver.symmetrifyStar (u : U) : Quiver.Star (Symmetrify.of.obj u) ≃ Quiver
.Star u oplus Quiver.Costar u
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star of the symmetrification of a quiver at a vertex `u` is equivalent to th
e sum of the
star and the costar at `u` in the original quiver.
-/
def Quiver.symmetrifyStar (u : U) :
    Quiver.Star (Symmetrify.of.obj u) ≃ Quiver.Star u ⊕ Quiver.Costar u :=
  Equiv.sigmaSumDistrib _ _

/-- The costar of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
costar and the star at `u` in the original quiver. -/
/-
**Quiver.symmetrifyCostar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quiver.symmetrifyCostar (u : U) : Quiver.Costar (Symmetrify.of.obj u) ≃ Qu
iver.Costar u oplus Quiver.Star u
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The costar of the symmetrification of a quiver at a vertex `u` is equivalent to 
the sum of the
costar and the star at `u` in the original quiver.
-/
def Quiver.symmetrifyCostar (u : U) :
    Quiver.Costar (Symmetrify.of.obj u) ≃ Quiver.Costar u ⊕ Quiver.Star u :=
  Equiv.sigmaSumDistrib _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Prefunctor.symmetrifyStar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.symmetrifyStar (u : U) : φ.symmetrify.star u = (Quiver.symmetri
fyStar _).symm ∘ Sum.map (φ.star u) (φ.costar u) ∘ Quiver.symmetrifyStar u
参数：u : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.sigmaSumDistrib_apply`：∀ {ι : Type u_11} (α : ι → Type u_9) (β : ι
 → Type u_10) (p : (i : ι) × (α i ⊕ β i)),   (Equiv.sigmaSumDistrib α β) p = Sum
.map (Sigma.mk p.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prefunctor.symmetrify_map`：∀ {U : Type u_1} {V : Type u_2} [inst : Quive
r U] [inst_1 : Quiver V] (φ : U ⥤q V) {X Y : Quiver.Symmetrify U}   (a : (X ⟶ Y)
 ⊕ (Y ⟶ X)), φ.…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prefunctor.symmetrify_obj`：∀ {U : Type u_1} {V : Type u_2} [inst : Quive
r U] [inst_1 : Quiver V] (φ : U ⥤q V) (a : U), φ.symmetrify.obj a = φ.obj a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
theorem Prefunctor.symmetrifyStar (u : U) :
    φ.symmetrify.star u =
      (Quiver.symmetrifyStar _).symm ∘ Sum.map (φ.star u) (φ.costar u) ∘
        Quiver.symmetrifyStar u := by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyStar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyStar]`
    simp only [Quiver.symmetrifyStar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistrib_apply, Equiv.sigmaSumDistrib_apply] <;>
    simp

set_option backward.isDefEq.respectTransparency false in
/-
**Prefunctor.symmetrifyCostar** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [inst_1 : Quiver V] (φ :
 U ⥤q V) (u : U),   φ.symmetrify.costar u =     ⇑(Quiver.symmetrifyCostar (φ.obj
 u)).symm ∘ Sum.map (φ.costar u) (φ.star u) ∘ ⇑(Quiver.symmetrifyCostar u)
参数：φ : U ⥤q V；u : U；Quiver.symmetrifyCostar (φ.obj u)；φ.costar u；φ.star u；Quiver
.symmetrifyCostar u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.sigmaSumDistrib_apply`：∀ {ι : Type u_11} (α : ι → Type u_9) (β : ι
 → Type u_10) (p : (i : ι) × (α i ⊕ β i)),   (Equiv.sigmaSumDistrib α β) p = Sum
.map (Sigma.mk p.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prefunctor.symmetrify_map`：∀ {U : Type u_1} {V : Type u_2} [inst : Quive
r U] [inst_1 : Quiver V] (φ : U ⥤q V) {X Y : Quiver.Symmetrify U}   (a : (X ⟶ Y)
 ⊕ (Y ⟶ X)), φ.…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prefunctor.symmetrify_obj`：∀ {U : Type u_1} {V : Type u_2} [inst : Quive
r U] [inst_1 : Quiver V] (φ : U ⥤q V) (a : U), φ.symmetrify.obj a = φ.obj a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
protected theorem Prefunctor.symmetrifyCostar (u : U) :
    φ.symmetrify.costar u =
      (Quiver.symmetrifyCostar _).symm ∘
        Sum.map (φ.costar u) (φ.star u) ∘ Quiver.symmetrifyCostar u := by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyCostar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyCostar]`
    simp only [Quiver.symmetrifyCostar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistrib_apply, Equiv.sigmaSumDistrib_apply] <;>
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Prefunctor.IsCovering.symmetrify** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor.IsCover
ing`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [inst_1 : Quiver V] (φ :
 U ⥤q V),   φ.IsCovering → φ.symmetrify.IsCovering
参数：φ : U ⥤q V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prefunctor.symmetrifyStar`：Prefunctor.symmetrifyStar (u : U) : φ.symmetr
ify.star u = (Quiver.symmetrifyStar _).symm ∘ Sum.map (φ.star u) (φ.costar u) ∘ 
Quiver.symmetri…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Prefunctor.IsCovering.star_bijective`：∀ {U : Type u_1} [inst : Quiver U]
 {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), Fu
nction.Bijective (φ.star u…
· 使用定理 `Prefunctor.IsCovering.costar_bijective`：∀ {U : Type u_1} [inst : Quiver 
U] {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), 
Function.Bijective (φ.costar…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Prefunctor.symmetrifyCostar`：∀ {U : Type u_1} [inst : Quiver U] {V : Typ
e u_2} [inst_1 : Quiver V] (φ : U ⥤q V) (u : U),   φ.symmetrify.costar u =     ⇑
(Quiver.symmetrif…
-/
protected theorem Prefunctor.IsCovering.symmetrify (hφ : φ.IsCovering) :
    φ.symmetrify.IsCovering := by
  refine ⟨fun u => ?_, fun u => ?_⟩ <;>
  simp [φ.symmetrifyStar, φ.symmetrifyCostar, hφ.star_bijective u, hφ.costar_bijective u]

/-- The path star at a vertex `u` is the type of all paths starting at `u`.
The type `Quiver.PathStar u` is defined to be `Σ v : U, Path u v`. -/
/-
**Quiver.PathStar** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Quiver.PathStar (u : U)
参数：u : U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path star at a vertex `u` is the type of all paths starting at `u`.
The type `Quiver.PathStar u` is defined to be `Σ v : U, Path u v`.
-/
abbrev Quiver.PathStar (u : U) :=
  Σ v : U, Path u v

/-- Constructor for `Quiver.PathStar`. Defined to be `Sigma.mk`. -/
/-
**Quiver.PathStar.mk** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.PathStar`。
形式化陈述：{U : Type u_1} → [inst : Quiver U] → {u v : U} → Quiver.Path u v → Quiver.
PathStar u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Quiver.PathStar`. Defined to be `Sigma.mk`.
-/
protected abbrev Quiver.PathStar.mk {u v : U} (p : Path u v) : Quiver.PathStar u :=
  ⟨_, p⟩

/-- A prefunctor induces a map of path stars. -/
/-
**Prefunctor.pathStar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Prefunctor.pathStar (u : U) : Quiver.PathStar u -> Quiver.PathStar (φ.obj 
u)
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor induces a map of path stars.
-/
def Prefunctor.pathStar (u : U) : Quiver.PathStar u → Quiver.PathStar (φ.obj u) := fun p =>
  Quiver.PathStar.mk (φ.mapPath p.2)

@[simp]
/-
**Prefunctor.pathStar_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.pathStar_apply {u v : U} (p : Path u v) : φ.pathStar u (Quiver.
PathStar.mk p) = Quiver.PathStar.mk (φ.mapPath p)
参数：p : Path u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prefunctor.pathStar_apply {u v : U} (p : Path u v) :
    φ.pathStar u (Quiver.PathStar.mk p) = Quiver.PathStar.mk (φ.mapPath p) :=
  rfl
/-
**Prefunctor.pathStar_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.pathStar_injective (hφ : forall u, Injective (φ.star u)) (u : U
) : Injective (φ.pathStar u)
参数：hφ : forall u, Injective (φ.star u)；u : U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Quiver.Path.nil_ne_cons`：nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.n
il != p.cons e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.cast_cons`：∀ {U : Type u_1} [inst : Quiver U] {u v w u' w' :
 U} (p : Quiver.Path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w'),   Quiver.Path
.cast hu hw…
· 使用定理 `Quiver.Path.eq_cast_iff_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' 
v' : U} (hu : u = u') (hv : v = v') (p : Quiver.Path u v)   (p' : Quiver.Path u'
 v'), p' = Quiver…
· 使用引理 `Quiver.Path.cons_ne_nil`：cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons
 e != Path.nil
· 使用定理 `Quiver.Path.cast_eq_iff_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' 
v' : U} (hu : u = u') (hv : v = v') (p : Quiver.Path u v)   (p' : Quiver.Path u'
 v'), Quiver.Path…
· 使用引理 `Quiver.Path.obj_eq_of_cons_eq_cons`：obj_eq_of_cons_eq_cons {p : Path a b
} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c
· 使用定理 `Quiver.Path.cast_rfl_rfl`：∀ {U : Type u_1} [inst : Quiver U] {u v : U} (
p : Quiver.Path u v), Quiver.Path.cast ⋯ ⋯ p = p
· 使用引理 `Quiver.Path.heq_of_cons_eq_cons`：heq_of_cons_eq_cons {p : Path a b} {p' 
: Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p ≍ p'
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `Quiver.Hom.cast_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} 
(hu : u = u') (hv : v = v') (e : u ⟶ v), Quiver.Hom.cast hu hv e ≍ e
· 使用引理 `Quiver.Path.hom_heq_of_cons_eq_cons`：hom_heq_of_cons_eq_cons {p : Path a
 b} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e
'
-/
theorem Prefunctor.pathStar_injective (hφ : ∀ u, Injective (φ.star u)) (u : U) :
    Injective (φ.pathStar u) := by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v₁, p₁⟩
  induction p₁ with
  | nil =>
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro; rfl -- Porting note: goal not present in lean3.
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      exfalso
      obtain ⟨h, h'⟩ := h
      rw [← Path.eq_cast_iff_heq rfl h.symm, Path.cast_cons] at h'
      exact (Path.nil_ne_cons _ _) h'
  | cons p₁ e₁ ih =>
    rename_i x₁ y₁
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      exfalso
      obtain ⟨h, h'⟩ := h
      rw [← Path.cast_eq_iff_heq rfl h, Path.cast_cons] at h'
      exact (Path.cons_ne_nil _ _) h'
    · rename_i x₂
      intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      obtain ⟨hφy, h'⟩ := h
      rw [← Path.cast_eq_iff_heq rfl hφy, Path.cast_cons, Path.cast_rfl_rfl] at h'
      have hφx := Path.obj_eq_of_cons_eq_cons h'
      have hφp := Path.heq_of_cons_eq_cons h'
      have hφe := HEq.trans (Hom.cast_heq rfl hφy _).symm (Path.hom_heq_of_cons_eq_cons h')
      have h_path_star : φ.pathStar u ⟨x₁, p₁⟩ = φ.pathStar u ⟨x₂, p₂⟩ := by
        simp only [Prefunctor.pathStar_apply, Sigma.mk.inj_iff]; exact ⟨hφx, hφp⟩
      cases ih h_path_star
      have h_star : φ.star x₁ ⟨y₁, e₁⟩ = φ.star x₁ ⟨y₂, e₂⟩ := by
        simp only [Prefunctor.star_apply, Sigma.mk.inj_iff]; exact ⟨hφy, hφe⟩
      cases hφ x₁ h_star
      rfl
/-
**Prefunctor.pathStar_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.pathStar_surjective (hφ : forall u, Surjective (φ.star u)) (u :
 U) : Surjective (φ.pathStar u)
参数：hφ : forall u, Surjective (φ.star u)；u : U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem Prefunctor.pathStar_surjective (hφ : ∀ u, Surjective (φ.star u)) (u : U) :
    Surjective (φ.pathStar u) := by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v, p⟩
  induction p with
  | nil =>
    use ⟨u, Path.nil⟩
    simp only [Prefunctor.mapPath_nil]
  | cons p' ev ih =>
    obtain ⟨⟨u', q'⟩, h⟩ := ih
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨u'', eu⟩, k⟩ := hφ u' ⟨_, ev⟩
    simp only [star_apply, Sigma.mk.inj_iff] at k
    -- Porting note: was `obtain ⟨rfl, rfl⟩ := k`
    obtain ⟨rfl, k⟩ := k
    simp only [heq_eq_eq] at k
    subst k
    use ⟨_, q'.cons eu⟩
    simp only [Prefunctor.mapPath_cons]
/-
**Prefunctor.pathStar_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.pathStar_bijective (hφ : forall u, Bijective (φ.star u)) (u : U
) : Bijective (φ.pathStar u)
参数：hφ : forall u, Bijective (φ.star u)；u : U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.pathStar_injective`：Prefunctor.pathStar_injective (hφ : foral
l u, Injective (φ.star u)) (u : U) : Injective (φ.pathStar u)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prefunctor.pathStar_surjective`：Prefunctor.pathStar_surjective (hφ : for
all u, Surjective (φ.star u)) (u : U) : Surjective (φ.pathStar u)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Prefunctor.pathStar_bijective (hφ : ∀ u, Bijective (φ.star u)) (u : U) :
    Bijective (φ.pathStar u) :=
  ⟨φ.pathStar_injective (fun u => (hφ u).1) _, φ.pathStar_surjective (fun u => (hφ u).2) _⟩

namespace Prefunctor.IsCovering

variable {φ}

/-
**Prefunctor.IsCovering.pathStar_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor
.IsCovering`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [inst_1 : Quiver V] {φ :
 U ⥤q V},   φ.IsCovering → ∀ (u : U), Function.Bijective (φ.pathStar u)
参数：u : U；φ.pathStar u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.pathStar_bijective`：Prefunctor.pathStar_bijective (hφ : foral
l u, Bijective (φ.star u)) (u : U) : Bijective (φ.pathStar u)
· 使用定理 `Prefunctor.IsCovering.star_bijective`：∀ {U : Type u_1} [inst : Quiver U]
 {V : Type u_2} [inst_1 : Quiver V] {φ : U ⥤q V},   φ.IsCovering → ∀ (u : U), Fu
nction.Bijective (φ.star u…
-/
protected theorem pathStar_bijective (hφ : φ.IsCovering) (u : U) : Bijective (φ.pathStar u) :=
  φ.pathStar_bijective hφ.1 u

end Prefunctor.IsCovering

section HasInvolutiveReverse

variable [HasInvolutiveReverse U] [HasInvolutiveReverse V]

/-- In a quiver with involutive inverses, the star and costar at every vertex are equivalent.
This map is induced by `Quiver.reverse`. -/
@[simps]
/-
**Quiver.starEquivCostar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quiver.starEquivCostar (u : U) : Quiver.Star u ≃ Quiver.Costar u where toF
un e
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a quiver with involutive inverses, the star and costar at every vertex are eq
uivalent.
This map is induced by `Quiver.reverse`.
-/
def Quiver.starEquivCostar (u : U) : Quiver.Star u ≃ Quiver.Costar u where
  toFun e := ⟨e.1, reverse e.2⟩
  invFun e := ⟨e.1, reverse e.2⟩
  left_inv e := by simp
  right_inv e := by simp

@[simp]
/-
**Quiver.starEquivCostar_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.starEquivCostar_apply {u v : U} (e : u ⟶ v) : Quiver.starEquivCosta
r u (Quiver.Star.mk e) = Quiver.Costar.mk (reverse e)
参数：e : u ⟶ v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quiver.starEquivCostar_apply {u v : U} (e : u ⟶ v) :
    Quiver.starEquivCostar u (Quiver.Star.mk e) = Quiver.Costar.mk (reverse e) :=
  rfl

@[simp]
/-
**Quiver.starEquivCostar_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.starEquivCostar_symm_apply {u v : U} (e : u ⟶ v) : (Quiver.starEqui
vCostar v).symm (Quiver.Costar.mk e) = Quiver.Star.mk (reverse e)
参数：e : u ⟶ v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Quiver.starEquivCostar_symm_apply {u v : U} (e : u ⟶ v) :
    (Quiver.starEquivCostar v).symm (Quiver.Costar.mk e) = Quiver.Star.mk (reverse e) :=
  rfl

variable [Prefunctor.MapReverse φ]
/-
**Prefunctor.costar_conj_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.costar_conj_star (u : U) : φ.costar u = Quiver.starEquivCostar 
(φ.obj u) ∘ φ.star u ∘ (Quiver.starEquivCostar u).symm
参数：u : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prefunctor.map_reverse`：∀ {U : Type u_1} {V : Type u_2} [inst : Quiver U
] [inst_1 : Quiver V] [inst_2 : Quiver.HasReverse U]   [inst_3 : Quiver.HasRever
se V] (φ : U…
· 使用定理 `Quiver.reverse_reverse`：reverse_reverse [h : HasInvolutiveReverse V] {a 
b : V} (f : a ⟶ b) : reverse (reverse f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
-/
theorem Prefunctor.costar_conj_star (u : U) :
    φ.costar u = Quiver.starEquivCostar (φ.obj u) ∘ φ.star u ∘ (Quiver.starEquivCostar u).symm := by
  ext ⟨v, f⟩ <;> simp
/-
**Prefunctor.bijective_costar_iff_bijective_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.bijective_costar_iff_bijective_star (u : U) : Bijective (φ.cost
ar u) ↔ Bijective (φ.star u)
参数：u : U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prefunctor.costar_conj_star`：Prefunctor.costar_conj_star (u : U) : φ.cos
tar u = Quiver.starEquivCostar (φ.obj u) ∘ φ.star u ∘ (Quiver.starEquivCostar u)
.symm
· 使用定理 `EquivLike.comp_bijective`：comp_bijective (f : α -> β) (e : F) : Function
.Bijective (e ∘ f) ↔ Function.Bijective f
· 使用定理 `EquivLike.bijective_comp`：bijective_comp (e : E) (f : β -> γ) : Function
.Bijective (f ∘ e) ↔ Function.Bijective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Prefunctor.bijective_costar_iff_bijective_star (u : U) :
    Bijective (φ.costar u) ↔ Bijective (φ.star u) := by
  rw [Prefunctor.costar_conj_star φ, EquivLike.comp_bijective, EquivLike.bijective_comp]
/-
**Prefunctor.isCovering_of_bijective_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.isCovering_of_bijective_star (h : forall u, Bijective (φ.star u
)) : φ.IsCovering
参数：h : forall u, Bijective (φ.star u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prefunctor.bijective_costar_iff_bijective_star`：Prefunctor.bijective_cos
tar_iff_bijective_star (u : U) : Bijective (φ.costar u) ↔ Bijective (φ.star u)
-/
theorem Prefunctor.isCovering_of_bijective_star (h : ∀ u, Bijective (φ.star u)) : φ.IsCovering :=
  ⟨h, fun u => (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩
/-
**Prefunctor.isCovering_of_bijective_costar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prefunctor.isCovering_of_bijective_costar (h : forall u, Bijective (φ.cost
ar u)) : φ.IsCovering
参数：h : forall u, Bijective (φ.costar u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prefunctor.bijective_costar_iff_bijective_star`：Prefunctor.bijective_cos
tar_iff_bijective_star (u : U) : Bijective (φ.costar u) ↔ Bijective (φ.star u)
-/
theorem Prefunctor.isCovering_of_bijective_costar (h : ∀ u, Bijective (φ.costar u)) :
    φ.IsCovering :=
  ⟨fun u => (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

end HasInvolutiveReverse

