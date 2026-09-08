/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

The limit cone for `S : LightProfinite` is `S.asLimitCone`, the fact that it's a limit is
`S.asLimit`.

We also prove that the projection and transition maps in this limit are surjective.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits CompHausLike

namespace LightProfinite

universe u

variable (S : LightProfinite.{u})

/-- The functor `ℕᵒᵖ ⥤ FintypeCat` whose limit is isomorphic to `S`. -/
/-
**LightProfinite.fintypeDiagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：fintypeDiagram : Natᵒᵖ ⥤ FintypeCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ℕᵒᵖ ⥤ FintypeCat` whose limit is isomorphic to `S`.
-/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := S.toLightDiagram.diagram

/-- An abbreviation for `S.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
/-
**LightProfinite.diagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：diagram : Natᵒᵖ ⥤ LightProfinite
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `S.fintypeDiagram ⋙ FintypeCat.toProfinite`.
-/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/--
A cone over `S.diagram` whose cone point is isomorphic to `S`.
(Auxiliary definition, use `S.asLimitCone` instead.)
-/
/-
**LightProfinite.asLimitConeAux** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：asLimitConeAux : Cone S.diagram
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone over `S.diagram` whose cone point is isomorphic to `S`.
(Auxiliary definition, use `S.asLimitCone` instead.)
-/
def asLimitConeAux : Cone S.diagram :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

/-- An auxiliary isomorphism of cones used to prove that `S.asLimitConeAux` is a limit cone. -/
/-
**LightProfinite.isoMapCone** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.
cone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary isomorphism of cones used to prove that `S.asLimitConeAux` is a lim
it cone.
-/
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

/--
`S.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `S.asLimit` instead.)
-/
/-
**LightProfinite.asLimitAux** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：asLimitAux : IsLimit S.asLimitConeAux
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `S.asLimit` instead.)
-/
def asLimitAux : IsLimit S.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/-- A cone over `S.diagram` whose cone point is `S`. -/
/-
**LightProfinite.asLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：asLimitCone : Cone S.diagram where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone over `S.diagram` whose cone point is `S`.
-/
def asLimitCone : Cone S.diagram where
  pt := S
  π := {
    app := fun n ↦ (lightToProfiniteFullyFaithful.preimageIso <|
      (Cone.forget _).mapIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ ↦ by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }

set_option backward.isDefEq.respectTransparency false in
/-- `S.asLimitCone` is indeed a limit cone. -/
/-
**LightProfinite.asLimit** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：asLimit : IsLimit S.asLimitCone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S.asLimitCone` is indeed a limit cone.
-/
def asLimit : IsLimit S.asLimitCone := S.asLimitAux.ofIsoLimit <|
  Cone.ext (lightToProfiniteFullyFaithful.preimageIso <|
    (Cone.forget _).mapIso S.isoMapCone) (fun _ ↦ by rw [← @Iso.inv_comp_eq]; rfl)

/-- A bundled version of `S.asLimitCone` and `S.asLimit`. -/
/-
**LightProfinite.lim** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：lim : Limits.LimitCone S.diagram
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled version of `S.asLimitCone` and `S.asLimit`.
-/
def lim : Limits.LimitCone S.diagram := ⟨S.asLimitCone, S.asLimit⟩

/-- The projection from `S` to the `n`th component of `S.diagram`. -/
/-
**LightProfinite.proj** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：proj (n : Nat) : S ⟶ S.diagram.obj ⟨n⟩
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from `S` to the `n`th component of `S.diagram`.
-/
abbrev proj (n : ℕ) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩
/-
**LightProfinite.lightToProfinite_map_proj_eq** 是 Mathlib 中的一个引理，位于命名空间 `LightPr
ofinite`。
形式化陈述：lightToProfinite_map_proj_eq (n : Nat) : lightToProfinite.map (S.proj n) =
 (lightToProfinite.obj S).asLimitCone.π.app _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompHausLike.toCompHausLike_map`：∀ {P P' : TopCat → Prop} (h : ∀ (X : Co
mpHausLike P), P X.toTop → P' X.toTop) {X Y : CompHausLike P} (f : X ⟶ Y),   (Co
mpHausLike.toCompHaus…
· 使用引理 `CategoryTheory.liftedLimitMapsToOriginal_inv_map_π`：liftedLimitMapsToOri
ginal_inv_map_π {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t
 : IsLimit c) (j : J) : (liftedLimitMaps…
· 使用定理 `CategoryTheory.instCountableCategoryNat`：CategoryTheory.CountableCategor
y ℕ
-/
lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by
  simp only [toCompHausLike_map]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact liftedLimitMapsToOriginal_inv_map_π hc _
/-
**LightProfinite.proj_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LightProfinite`。
形式化陈述：proj_surjective (n : Nat) : Function.Surjective (S.proj n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightProfinite.lightToProfinite_map_proj_eq`：lightToProfinite_map_proj_e
q (n : Nat) : lightToProfinite.map (S.proj n) = (lightToProfinite.obj S).asLimit
Cone.π.app _
· 使用定理 `DiscreteQuotient.proj_surjective`：proj_surjective : Function.Surjective 
S.proj
-/
lemma proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

/-- An abbreviation for the `n`th component of `S.diagram`. -/
/-
**LightProfinite.component** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：component (n : Nat) : LightProfinite
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for the `n`th component of `S.diagram`.
-/
abbrev component (n : ℕ) : LightProfinite := S.diagram.obj ⟨n⟩

/-- The transition map from `S_{n+1}` to `S_n` in `S.diagram`. -/
/-
**LightProfinite.transitionMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：transitionMap (n : Nat) : S.component (n + 1) ⟶ S.component n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transition map from `S_{n+1}` to `S_n` in `S.diagram`.
-/
abbrev transitionMap (n : ℕ) : S.component (n + 1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

/-- The transition map from `S_m` to `S_n` in `S.diagram`, when `m ≤ n`. -/
/-
**LightProfinite.transitionMapLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：transitionMapLE {n m : Nat} (h : n <= m) : S.component m ⟶ S.component n
参数：h : n <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transition map from `S_m` to `S_n` in `S.diagram`, when `m ≤ n`.
-/
abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩
/-
**LightProfinite.proj_comp_transitionMap** 是 Mathlib 中的一个引理，位于命名空间 `LightProfini
te`。
形式化陈述：proj_comp_transitionMap (n : Nat) : S.proj (n + 1) ≫ S.diagram.map ⟨homOfL
E (Nat.le_succ _)⟩ = S.proj n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
lemma proj_comp_transitionMap (n : ℕ) :
    S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op
/-
**LightProfinite.proj_comp_transitionMap'** 是 Mathlib 中的一个引理，位于命名空间 `LightProfin
ite`。
形式化陈述：proj_comp_transitionMap' (n : Nat) : S.transitionMap n ∘ S.proj (n + 1) = 
S.proj n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LightProfinite.proj_comp_transitionMap`：proj_comp_transitionMap (n : Nat
) : S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n
-/
lemma proj_comp_transitionMap' (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl
/-
**LightProfinite.proj_comp_transitionMapLE** 是 Mathlib 中的一个引理，位于命名空间 `LightProfi
nite`。
形式化陈述：proj_comp_transitionMapLE {n m : Nat} (h : n <= m) : S.proj m ≫ S.diagram.
map ⟨homOfLE h⟩ = S.proj n
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
-/
lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.diagram.map ⟨homOfLE h⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE h).op
/-
**LightProfinite.proj_comp_transitionMapLE'** 是 Mathlib 中的一个引理，位于命名空间 `LightProf
inite`。
形式化陈述：proj_comp_transitionMapLE' {n m : Nat} (h : n <= m) : S.transitionMapLE h 
∘ S.proj m = S.proj n
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LightProfinite.proj_comp_transitionMapLE`：proj_comp_transitionMapLE {n m
 : Nat} (h : n <= m) : S.proj m ≫ S.diagram.map ⟨homOfLE h⟩ = S.proj n
-/
lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE h ∘ S.proj m = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl
/-
**LightProfinite.surjective_transitionMap** 是 Mathlib 中的一个引理，位于命名空间 `LightProfin
ite`。
形式化陈述：surjective_transitionMap (n : Nat) : Function.Surjective (S.transitionMap 
n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightProfinite.proj_comp_transitionMap'`：proj_comp_transitionMap' (n : N
at) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n
· 使用引理 `LightProfinite.proj_surjective`：proj_surjective (n : Nat) : Function.Sur
jective (S.proj n)
-/
lemma surjective_transitionMap (n : ℕ) : Function.Surjective (S.transitionMap n) := by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n
/-
**LightProfinite.surjective_transitionMapLE** 是 Mathlib 中的一个引理，位于命名空间 `LightProf
inite`。
形式化陈述：surjective_transitionMapLE {n m : Nat} (h : n <= m) : Function.Surjective 
(S.transitionMapLE h)
参数：h : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightProfinite.proj_comp_transitionMapLE'`：proj_comp_transitionMapLE' {n
 m : Nat} (h : n <= m) : S.transitionMapLE h ∘ S.proj m = S.proj n
· 使用引理 `LightProfinite.proj_surjective`：proj_surjective (n : Nat) : Function.Sur
jective (S.proj n)
-/
lemma surjective_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (S.transitionMapLE h) := by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n

end LightProfinite

