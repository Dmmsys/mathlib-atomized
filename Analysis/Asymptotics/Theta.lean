/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Asymptotic equivalence up to a constant

In this file we prove basic properties of the equivalence relation
given by `f =Θ[l] g ↔ f =O[l] g ∧ g =O[l] f`.
-/

public section


open Filter

open Topology

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']
variable {c c' c₁ c₂ : Real} {f : α -> E} {g : α -> F} {k : α -> G}
variable {f' : α -> E'} {g' : α -> F'} {k' : α -> G'}
variable {f'' : α -> E''} {g'' : α -> F''}
variable {l l' : Filter α}

@[refl]
/--
theorem `isTheta_refl` / 定理 `isTheta_refl`

English:
theorem isTheta_refl
  given: (f : α -> E) (l : Filter α)
  statement: f =Θ[l] f
  proof: ⟨isBigO_refl _ _, isBigO_refl _ _⟩

中文:
定理 isTheta_refl
  条件: (f : α -> E) (l : 滤子 α)
  结论: f =Θ[l] f
  证明: ⟨isBigO_refl _ _, isBigO_refl _ _⟩

Depends on / 依赖: isBigO_refl
-/
theorem isTheta_refl (f : α -> E) (l : Filter α) : f =Θ[l] f :=
  ⟨isBigO_refl _ _, isBigO_refl _ _⟩

/--
theorem `isTheta_rfl` / 定理 `isTheta_rfl`

English:
theorem isTheta_rfl
  statement: f =Θ[l] f
  proof: isTheta_refl _ _

@[symm]
nonrec theorem IsTheta.symm (h : f =Θ[l] g) : g =Θ[l] f :=
  h.symm

中文:
定理 isTheta_rfl
  结论: f =Θ[l] f
  证明: isTheta_refl _ _

@[symm]
nonrec theorem IsTheta.symm (h : f =Θ[l] g) : g =Θ[l] f :=
  h.symm

Depends on / 依赖: isTheta_refl
-/
theorem isTheta_rfl : f =Θ[l] f :=
  isTheta_refl _ _

@[symm]
nonrec theorem IsTheta.symm (h : f =Θ[l] g) : g =Θ[l] f :=
  h.symm

/--
theorem `isTheta_comm` / 定理 `isTheta_comm`

English:
theorem isTheta_comm
  statement: f =Θ[l] g ↔ g =Θ[l] f
  proof: ⟨fun h => h.symm, fun h => h.symm⟩

@[trans]

中文:
定理 isTheta_comm
  结论: f =Θ[l] g ↔ g =Θ[l] f
  证明: ⟨fun h => h.symm, fun h => h.symm⟩

@[trans]

Depends on / 依赖: h.symm
-/
theorem isTheta_comm : f =Θ[l] g ↔ g =Θ[l] f :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[trans]
/--
theorem `IsTheta.trans` / 定理 `IsTheta.trans`

English:
theorem IsTheta.trans
  given: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k)
  proof: ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

中文:
定理 IsTheta.trans
  条件: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k)
  证明: ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
-/
theorem IsTheta.trans {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k) :
    f =Θ[l] k :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsTheta l) (IsTheta l)
  body: ⟨IsTheta.trans⟩

@[trans]

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsTheta l) (IsTheta l)
  定义体: ⟨IsTheta.trans⟩

@[trans]

Depends on / 依赖: IsTheta
-/
instance : Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsTheta l) (IsTheta l) :=
  ⟨IsTheta.trans⟩

@[trans]
/--
theorem `IsBigO.trans_isTheta` / 定理 `IsBigO.trans_isTheta`

English:
theorem IsBigO.trans_isTheta
  statement: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =O[l] g)
  proof: h₁.trans h₂.1

中文:
定理 IsBigO.trans_isTheta
  结论: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =O[l] g)
  证明: h₁.trans h₂.1
-/
theorem IsBigO.trans_isTheta {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =O[l] g)
    (h₂ : g =Θ[l] k) : f =O[l] k :=
  h₁.trans h₂.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsBigO l) (IsTheta l) (IsBigO l)
  body: ⟨IsBigO.trans_isTheta⟩

@[trans]

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsBigO l) (IsTheta l) (IsBigO l)
  定义体: ⟨IsBigO.trans_isTheta⟩

@[trans]

Depends on / 依赖: IsBigO, IsTheta
-/
instance : Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsBigO l) (IsTheta l) (IsBigO l) :=
  ⟨IsBigO.trans_isTheta⟩

@[trans]
/--
theorem `IsTheta.trans_isBigO` / 定理 `IsTheta.trans_isBigO`

English:
theorem IsTheta.trans_isBigO
  statement: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g)
  proof: h₁.1.trans h₂

中文:
定理 IsTheta.trans_isBigO
  结论: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g)
  证明: h₁.1.trans h₂
-/
theorem IsTheta.trans_isBigO {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g)
    (h₂ : g =O[l] k) : f =O[l] k :=
  h₁.1.trans h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsBigO l) (IsBigO l)
  body: ⟨IsTheta.trans_isBigO⟩

@[trans]

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsBigO l) (IsBigO l)
  定义体: ⟨IsTheta.trans_isBigO⟩

@[trans]

Depends on / 依赖: IsBigO, IsTheta
-/
instance : Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsBigO l) (IsBigO l) :=
  ⟨IsTheta.trans_isBigO⟩

@[trans]
/--
theorem `IsLittleO.trans_isTheta` / 定理 `IsLittleO.trans_isTheta`

English:
theorem IsLittleO.trans_isTheta
  statement: {f : α -> E} {g : α -> F} {k : α -> G'} (h₁ : f =o[l] g)
  proof: h₁.trans_isBigO h₂.1

中文:
定理 IsLittleO.trans_isTheta
  结论: {f : α -> E} {g : α -> F} {k : α -> G'} (h₁ : f =o[l] g)
  证明: h₁.trans_isBigO h₂.1

Depends on / 依赖: trans_isBigO
-/
theorem IsLittleO.trans_isTheta {f : α -> E} {g : α -> F} {k : α -> G'} (h₁ : f =o[l] g)
    (h₂ : g =Θ[l] k) : f =o[l] k :=
  h₁.trans_isBigO h₂.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> F') (γ := α -> G') (IsLittleO l) (IsTheta l) (IsLittleO l)
  body: ⟨IsLittleO.trans_isTheta⟩

@[trans]

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> F') (γ := α -> G') (IsLittleO l) (IsTheta l) (IsLittleO l)
  定义体: ⟨IsLittleO.trans_isTheta⟩

@[trans]

Depends on / 依赖: IsLittleO, IsTheta
-/
instance : Trans (α := α -> E) (β := α -> F') (γ := α -> G') (IsLittleO l) (IsTheta l) (IsLittleO l) :=
  ⟨IsLittleO.trans_isTheta⟩

@[trans]
/--
theorem `IsTheta.trans_isLittleO` / 定理 `IsTheta.trans_isLittleO`

English:
theorem IsTheta.trans_isLittleO
  statement: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g)
  proof: h₁.1.trans_isLittleO h₂

中文:
定理 IsTheta.trans_isLittleO
  结论: {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g)
  证明: h₁.1.trans_isLittleO h₂

Depends on / 依赖: trans_isLittleO
-/
theorem IsTheta.trans_isLittleO {f : α -> E} {g : α -> F'} {k : α -> G} (h₁ : f =Θ[l] g)
    (h₂ : g =o[l] k) : f =o[l] k :=
  h₁.1.trans_isLittleO h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsLittleO l) (IsLittleO l)
  body: ⟨IsTheta.trans_isLittleO⟩

@[trans]

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsLittleO l) (IsLittleO l)
  定义体: ⟨IsTheta.trans_isLittleO⟩

@[trans]

Depends on / 依赖: IsLittleO, IsTheta
-/
instance : Trans (α := α -> E) (β := α -> F') (γ := α -> G) (IsTheta l) (IsLittleO l) (IsLittleO l) :=
  ⟨IsTheta.trans_isLittleO⟩

@[trans]
/--
theorem `IsTheta.trans_eventuallyEq` / 定理 `IsTheta.trans_eventuallyEq`

English:
theorem IsTheta.trans_eventuallyEq
  given: {f : α -> E} {g₁ g₂ : α -> F} (h : f =Θ[l] g₁) (hg : g₁ =ᶠ[l] g₂)
  proof: ⟨h.1.trans_eventuallyEq hg, hg.symm.trans_isBigO h.2⟩

中文:
定理 IsTheta.trans_eventuallyEq
  条件: {f : α -> E} {g₁ g₂ : α -> F} (h : f =Θ[l] g₁) (hg : g₁ =ᶠ[l] g₂)
  证明: ⟨h.1.trans_eventuallyEq hg, hg.symm.trans_isBigO h.2⟩

Depends on / 依赖: hg.symm.trans_isBigO, trans_eventuallyEq, trans_isBigO
-/
theorem IsTheta.trans_eventuallyEq {f : α -> E} {g₁ g₂ : α -> F} (h : f =Θ[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =Θ[l] g₂ :=
  ⟨h.1.trans_eventuallyEq hg, hg.symm.trans_isBigO h.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> F) (γ := α -> F) (IsTheta l) (EventuallyEq l) (IsTheta l)
  body: ⟨IsTheta.trans_eventuallyEq⟩

@[trans]

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> F) (γ := α -> F) (IsTheta l) (EventuallyEq l) (IsTheta l)
  定义体: ⟨IsTheta.trans_eventuallyEq⟩

@[trans]

Depends on / 依赖: EventuallyEq, IsTheta
-/
instance : Trans (α := α -> E) (β := α -> F) (γ := α -> F) (IsTheta l) (EventuallyEq l) (IsTheta l) :=
  ⟨IsTheta.trans_eventuallyEq⟩

@[trans]
/--
theorem `_root_.Filter.EventuallyEq.trans_isTheta` / 定理 `_root_.Filter.EventuallyEq.trans_isTheta`

English:
theorem _root_.Filter.EventuallyEq.trans_isTheta
  statement: {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
  proof: ⟨hf.trans_isBigO h.1, h.2.trans_eventuallyEq hf.symm⟩

中文:
定理 _root_.滤子.EventuallyEq.trans_isTheta
  结论: {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
  证明: ⟨hf.trans_isBigO h.1, h.2.trans_eventuallyEq hf.symm⟩

Depends on / 依赖: hf.symm, hf.trans_isBigO, trans_eventuallyEq, trans_isBigO
-/
theorem _root_.Filter.EventuallyEq.trans_isTheta {f₁ f₂ : α -> E} {g : α -> F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =Θ[l] g) : f₁ =Θ[l] g :=
  ⟨hf.trans_isBigO h.1, h.2.trans_eventuallyEq hf.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := α -> E) (β := α -> E) (γ := α -> F) (EventuallyEq l) (IsTheta l) (IsTheta l)
  body: ⟨EventuallyEq.trans_isTheta⟩

中文:
实例 :
  签名: Trans (α := α -> E) (β := α -> E) (γ := α -> F) (EventuallyEq l) (IsTheta l) (IsTheta l)
  定义体: ⟨EventuallyEq.trans_isTheta⟩

Depends on / 依赖: EventuallyEq, IsTheta
-/
instance : Trans (α := α -> E) (β := α -> E) (γ := α -> F) (EventuallyEq l) (IsTheta l) (IsTheta l) :=
  ⟨EventuallyEq.trans_isTheta⟩

/--
lemma `_root_.Filter.EventuallyEq.isTheta` / 引理 `_root_.Filter.EventuallyEq.isTheta`

English:
lemma _root_.Filter.EventuallyEq.isTheta
  given: {f g : α -> E} (h : f =ᶠ[l] g)
  statement: f =Θ[l] g
  proof: h.trans_isTheta isTheta_rfl

@[simp]

中文:
引理 _root_.滤子.EventuallyEq.isTheta
  条件: {f g : α -> E} (h : f =ᶠ[l] g)
  结论: f =Θ[l] g
  证明: h.trans_isTheta isTheta_rfl

@[simp]

Depends on / 依赖: h.trans_isTheta, isTheta_rfl, trans_isTheta
-/
lemma _root_.Filter.EventuallyEq.isTheta {f g : α -> E} (h : f =ᶠ[l] g) : f =Θ[l] g :=
  h.trans_isTheta isTheta_rfl

@[simp]
/--
theorem `isTheta_bot` / 定理 `isTheta_bot`

English:
theorem isTheta_bot
  statement: f =Θ[⊥] g
  proof: by simp [IsTheta]

@[simp]

中文:
定理 isTheta_bot
  结论: f =Θ[⊥] g
  证明: by simp [IsTheta]

@[simp]

Depends on / 依赖: IsTheta
-/
theorem isTheta_bot : f =Θ[⊥] g := by simp [IsTheta]

@[simp]
/--
theorem `isTheta_norm_left` / 定理 `isTheta_norm_left`

English:
theorem isTheta_norm_left
  statement: (fun x => ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g
  proof: by simp [IsTheta]

@[simp]

中文:
定理 isTheta_norm_left
  结论: (fun x => ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g
  证明: by simp [IsTheta]

@[simp]

Depends on / 依赖: IsTheta
-/
theorem isTheta_norm_left : (fun x => ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g := by simp [IsTheta]

@[simp]
/--
theorem `isTheta_norm_right` / 定理 `isTheta_norm_right`

English:
theorem isTheta_norm_right
  statement: (f =Θ[l] fun x => ‖g' x‖) ↔ f =Θ[l] g'
  proof: by simp [IsTheta]

alias ⟨IsTheta.of_norm_left, IsTheta.norm_left⟩ := isTheta_norm_left

alias ⟨IsTheta.of_norm_right, IsTheta.norm_right⟩ := isTheta_norm_right

中文:
定理 isTheta_norm_right
  结论: (f =Θ[l] fun x => ‖g' x‖) ↔ f =Θ[l] g'
  证明: by simp [IsTheta]

alias ⟨IsTheta.of_norm_left, IsTheta.norm_left⟩ := isTheta_norm_left

alias ⟨IsTheta.of_norm_right, IsTheta.norm_right⟩ := isTheta_norm_right

Depends on / 依赖: IsTheta
-/
theorem isTheta_norm_right : (f =Θ[l] fun x => ‖g' x‖) ↔ f =Θ[l] g' := by simp [IsTheta]

alias ⟨IsTheta.of_norm_left, IsTheta.norm_left⟩ := isTheta_norm_left

alias ⟨IsTheta.of_norm_right, IsTheta.norm_right⟩ := isTheta_norm_right

/--
theorem `IsTheta.of_norm_eventuallyEq_norm` / 定理 `IsTheta.of_norm_eventuallyEq_norm`

English:
theorem IsTheta.of_norm_eventuallyEq_norm
  given: (h : (fun x => ‖f x‖) =ᶠ[l] fun x => ‖g x‖)
  statement: f =Θ[l] g
  proof: ⟨.of_bound' h.le, .of_bound' h.symm.le⟩

中文:
定理 IsTheta.of_norm_eventuallyEq_norm
  条件: (h : (fun x => ‖f x‖) =ᶠ[l] fun x => ‖g x‖)
  结论: f =Θ[l] g
  证明: ⟨.of_bound' h.le, .of_bound' h.symm.le⟩

Depends on / 依赖: h.le, h.symm.le, of_bound
-/
theorem IsTheta.of_norm_eventuallyEq_norm (h : (fun x => ‖f x‖) =ᶠ[l] fun x => ‖g x‖) : f =Θ[l] g :=
  ⟨.of_bound' h.le, .of_bound' h.symm.le⟩

/--
theorem `IsTheta.of_norm_eventuallyEq` / 定理 `IsTheta.of_norm_eventuallyEq`

English:
theorem IsTheta.of_norm_eventuallyEq
  given: {g : α -> Real} (h : (fun x => ‖f' x‖) =ᶠ[l] g)
  statement: f' =Θ[l] g
  proof: of_norm_eventuallyEq_norm h.mono fun x hx => by simp only [← hx, norm_norm]

中文:
定理 IsTheta.of_norm_eventuallyEq
  条件: {g : α -> 实数} (h : (fun x => ‖f' x‖) =ᶠ[l] g)
  结论: f' =Θ[l] g
  证明: of_norm_eventuallyEq_norm h.mono fun x hx => by simp only [← hx, norm_norm]

Depends on / 依赖: h.mono, norm_norm, of_norm_eventuallyEq_norm
-/
theorem IsTheta.of_norm_eventuallyEq {g : α -> Real} (h : (fun x => ‖f' x‖) =ᶠ[l] g) : f' =Θ[l] g :=
of_norm_eventuallyEq_norm h.mono fun x hx => by simp only [← hx, norm_norm]

/--
theorem `IsTheta.isLittleO_congr_left` / 定理 `IsTheta.isLittleO_congr_left`

English:
theorem IsTheta.isLittleO_congr_left
  given: (h : f' =Θ[l] g')
  statement: f' =o[l] k ↔ g' =o[l] k
  proof: ⟨h.symm.trans_isLittleO, h.trans_isLittleO⟩

中文:
定理 IsTheta.isLittleO_congr_left
  条件: (h : f' =Θ[l] g')
  结论: f' =o[l] k ↔ g' =o[l] k
  证明: ⟨h.symm.trans_isLittleO, h.trans_isLittleO⟩

Depends on / 依赖: h.symm.trans_isLittleO, h.trans_isLittleO, trans_isLittleO
-/
theorem IsTheta.isLittleO_congr_left (h : f' =Θ[l] g') : f' =o[l] k ↔ g' =o[l] k :=
  ⟨h.symm.trans_isLittleO, h.trans_isLittleO⟩

/--
theorem `IsTheta.isLittleO_congr_right` / 定理 `IsTheta.isLittleO_congr_right`

English:
theorem IsTheta.isLittleO_congr_right
  given: (h : g' =Θ[l] k')
  statement: f =o[l] g' ↔ f =o[l] k'
  proof: ⟨fun H => H.trans_isTheta h, fun H => H.trans_isTheta h.symm⟩

中文:
定理 IsTheta.isLittleO_congr_right
  条件: (h : g' =Θ[l] k')
  结论: f =o[l] g' ↔ f =o[l] k'
  证明: ⟨fun H => H.trans_isTheta h, fun H => H.trans_isTheta h.symm⟩

Depends on / 依赖: H.trans_isTheta, h.symm, trans_isTheta
-/
theorem IsTheta.isLittleO_congr_right (h : g' =Θ[l] k') : f =o[l] g' ↔ f =o[l] k' :=
  ⟨fun H => H.trans_isTheta h, fun H => H.trans_isTheta h.symm⟩

/--
theorem `IsTheta.isBigO_congr_left` / 定理 `IsTheta.isBigO_congr_left`

English:
theorem IsTheta.isBigO_congr_left
  given: (h : f' =Θ[l] g')
  statement: f' =O[l] k ↔ g' =O[l] k
  proof: ⟨h.symm.trans_isBigO, h.trans_isBigO⟩

中文:
定理 IsTheta.isBigO_congr_left
  条件: (h : f' =Θ[l] g')
  结论: f' =O[l] k ↔ g' =O[l] k
  证明: ⟨h.symm.trans_isBigO, h.trans_isBigO⟩

Depends on / 依赖: h.symm.trans_isBigO, h.trans_isBigO, trans_isBigO
-/
theorem IsTheta.isBigO_congr_left (h : f' =Θ[l] g') : f' =O[l] k ↔ g' =O[l] k :=
  ⟨h.symm.trans_isBigO, h.trans_isBigO⟩

/--
theorem `IsTheta.isBigO_congr_right` / 定理 `IsTheta.isBigO_congr_right`

English:
theorem IsTheta.isBigO_congr_right
  given: (h : g' =Θ[l] k')
  statement: f =O[l] g' ↔ f =O[l] k'
  proof: ⟨fun H => H.trans_isTheta h, fun H => H.trans_isTheta h.symm⟩

中文:
定理 IsTheta.isBigO_congr_right
  条件: (h : g' =Θ[l] k')
  结论: f =O[l] g' ↔ f =O[l] k'
  证明: ⟨fun H => H.trans_isTheta h, fun H => H.trans_isTheta h.symm⟩

Depends on / 依赖: H.trans_isTheta, h.symm, trans_isTheta
-/
theorem IsTheta.isBigO_congr_right (h : g' =Θ[l] k') : f =O[l] g' ↔ f =O[l] k' :=
  ⟨fun H => H.trans_isTheta h, fun H => H.trans_isTheta h.symm⟩

/--
lemma `IsTheta.isTheta_congr_left` / 引理 `IsTheta.isTheta_congr_left`

English:
lemma IsTheta.isTheta_congr_left
  given: (h : f' =Θ[l] g')
  statement: f' =Θ[l] k ↔ g' =Θ[l] k
  proof: h.isBigO_congr_left.and h.isBigO_congr_right

中文:
引理 IsTheta.isTheta_congr_left
  条件: (h : f' =Θ[l] g')
  结论: f' =Θ[l] k ↔ g' =Θ[l] k
  证明: h.isBigO_congr_left.and h.isBigO_congr_right

Depends on / 依赖: h.isBigO_congr_left.and, h.isBigO_congr_right, isBigO_congr_left, isBigO_congr_right
-/
lemma IsTheta.isTheta_congr_left (h : f' =Θ[l] g') : f' =Θ[l] k ↔ g' =Θ[l] k :=
  h.isBigO_congr_left.and h.isBigO_congr_right

/--
lemma `IsTheta.isTheta_congr_right` / 引理 `IsTheta.isTheta_congr_right`

English:
lemma IsTheta.isTheta_congr_right
  given: (h : f' =Θ[l] g')
  statement: k =Θ[l] f' ↔ k =Θ[l] g'
  proof: h.isBigO_congr_right.and h.isBigO_congr_left

中文:
引理 IsTheta.isTheta_congr_right
  条件: (h : f' =Θ[l] g')
  结论: k =Θ[l] f' ↔ k =Θ[l] g'
  证明: h.isBigO_congr_right.and h.isBigO_congr_left

Depends on / 依赖: h.isBigO_congr_left, h.isBigO_congr_right.and, isBigO_congr_left, isBigO_congr_right
-/
lemma IsTheta.isTheta_congr_right (h : f' =Θ[l] g') : k =Θ[l] f' ↔ k =Θ[l] g' :=
  h.isBigO_congr_right.and h.isBigO_congr_left

/--
theorem `IsTheta.mono` / 定理 `IsTheta.mono`

English:
theorem IsTheta.mono
  given: (h : f =Θ[l] g) (hl : l' <= l)
  statement: f =Θ[l'] g
  proof: ⟨h.1.mono hl, h.2.mono hl⟩

中文:
定理 IsTheta.mono
  条件: (h : f =Θ[l] g) (hl : l' <= l)
  结论: f =Θ[l'] g
  证明: ⟨h.1.mono hl, h.2.mono hl⟩
-/
theorem IsTheta.mono (h : f =Θ[l] g) (hl : l' <= l) : f =Θ[l'] g :=
  ⟨h.1.mono hl, h.2.mono hl⟩

/--
theorem `IsTheta.sup` / 定理 `IsTheta.sup`

English:
theorem IsTheta.sup
  given: (h : f' =Θ[l] g') (h' : f' =Θ[l'] g')
  statement: f' =Θ[l ⊔ l'] g'
  proof: ⟨h.1.sup h'.1, h.2.sup h'.2⟩

@[simp]

中文:
定理 IsTheta.上确界
  条件: (h : f' =Θ[l] g') (h' : f' =Θ[l'] g')
  结论: f' =Θ[l ⊔ l'] g'
  证明: ⟨h.1.sup h'.1, h.2.sup h'.2⟩

@[simp]
-/
theorem IsTheta.sup (h : f' =Θ[l] g') (h' : f' =Θ[l'] g') : f' =Θ[l ⊔ l'] g' :=
  ⟨h.1.sup h'.1, h.2.sup h'.2⟩

@[simp]
/--
theorem `isTheta_sup` / 定理 `isTheta_sup`

English:
theorem isTheta_sup
  statement: f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g'
  proof: ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

中文:
定理 isTheta_sup
  结论: f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g'
  证明: ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

Depends on / 依赖: h.mono, le_sup_left, le_sup_right
-/
theorem isTheta_sup : f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

/--
theorem `IsTheta.eq_zero_iff` / 定理 `IsTheta.eq_zero_iff`

English:
theorem IsTheta.eq_zero_iff
  given: (h : f'' =Θ[l] g'')
  statement: forallᶠ x in l, f'' x = 0 ↔ g'' x = 0
  proof: h.1.eq_zero_imp.mp h.2.eq_zero_imp.mono fun _ => Iff.intro

中文:
定理 IsTheta.eq_zero_iff
  条件: (h : f'' =Θ[l] g'')
  结论: 对任意ᶠ x in l, f'' x = 0 ↔ g'' x = 0
  证明: h.1.eq_zero_imp.mp h.2.eq_zero_imp.mono fun _ => Iff.intro

Depends on / 依赖: Iff.intro, eq_zero_imp, eq_zero_imp.mono, eq_zero_imp.mp
-/
theorem IsTheta.eq_zero_iff (h : f'' =Θ[l] g'') : forallᶠ x in l, f'' x = 0 ↔ g'' x = 0 :=
h.1.eq_zero_imp.mp h.2.eq_zero_imp.mono fun _ => Iff.intro

/--
theorem `IsTheta.tendsto_zero_iff` / 定理 `IsTheta.tendsto_zero_iff`

English:
theorem IsTheta.tendsto_zero_iff
  given: (h : f'' =Θ[l] g'')
  proof: by
  simp only [← isLittleO_one_iff Real, h.isLittleO_congr_left]

中文:
定理 IsTheta.tendsto_zero_iff
  条件: (h : f'' =Θ[l] g'')
  证明: by
  simp only [← isLittleO_one_iff Real, h.isLittleO_congr_left]

Depends on / 依赖: h.isLittleO_congr_left, isLittleO_congr_left, isLittleO_one_iff
-/
theorem IsTheta.tendsto_zero_iff (h : f'' =Θ[l] g'') :
    Tendsto f'' l (𝓝 0) ↔ Tendsto g'' l (𝓝 0) := by
  simp only [← isLittleO_one_iff Real, h.isLittleO_congr_left]

/--
theorem `IsTheta.tendsto_norm_atTop_iff` / 定理 `IsTheta.tendsto_norm_atTop_iff`

English:
theorem IsTheta.tendsto_norm_atTop_iff
  given: (h : f' =Θ[l] g')
  proof: by
  simp only [Function.comp_def, ← isLittleO_const_left_of_ne (one_ne_zero' Real),
    h.isLittleO_congr_right]

中文:
定理 IsTheta.tendsto_norm_atTop_iff
  条件: (h : f' =Θ[l] g')
  证明: by
  simp only [Function.comp_def, ← isLittleO_const_left_of_ne (one_ne_zero' Real),
    h.isLittleO_congr_right]

Depends on / 依赖: Function, Function.comp_def, comp_def, h.isLittleO_congr_right, isLittleO_congr_right, isLittleO_const_left_of_ne, one_ne_zero
-/
theorem IsTheta.tendsto_norm_atTop_iff (h : f' =Θ[l] g') :
    Tendsto (norm ∘ f') l atTop ↔ Tendsto (norm ∘ g') l atTop := by
  simp only [Function.comp_def, ← isLittleO_const_left_of_ne (one_ne_zero' Real),
    h.isLittleO_congr_right]

/--
theorem `IsTheta.isBoundedUnder_le_iff` / 定理 `IsTheta.isBoundedUnder_le_iff`

English:
theorem IsTheta.isBoundedUnder_le_iff
  given: (h : f' =Θ[l] g')
  proof: by
  simp only [← isBigO_const_of_ne (one_ne_zero' Real), h.isBigO_congr_left]

中文:
定理 IsTheta.isBoundedUnder_le_iff
  条件: (h : f' =Θ[l] g')
  证明: by
  simp only [← isBigO_const_of_ne (one_ne_zero' Real), h.isBigO_congr_left]

Depends on / 依赖: h.isBigO_congr_left, isBigO_congr_left, isBigO_const_of_ne, one_ne_zero
-/
theorem IsTheta.isBoundedUnder_le_iff (h : f' =Θ[l] g') :
    IsBoundedUnder (· <= ·) l (norm ∘ f') ↔ IsBoundedUnder (· <= ·) l (norm ∘ g') := by
  simp only [← isBigO_const_of_ne (one_ne_zero' Real), h.isBigO_congr_left]

/--
theorem `IsTheta.smul` / 定理 `IsTheta.smul`

English:
theorem IsTheta.smul
  statement: [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {f₁ : α -> 𝕜} {f₂ : α -> 𝕜'} {g₁ : α -> E'}
  proof: ⟨hf.1.smul hg.1, hf.2.smul hg.2⟩

中文:
定理 IsTheta.smul
  结论: [赋范空间 𝕜 E'] [赋范空间 𝕜' F'] {f₁ : α -> 𝕜} {f₂ : α -> 𝕜'} {g₁ : α -> E'}
  证明: ⟨hf.1.smul hg.1, hf.2.smul hg.2⟩
-/
theorem IsTheta.smul [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {f₁ : α -> 𝕜} {f₂ : α -> 𝕜'} {g₁ : α -> E'}
    {g₂ : α -> F'} (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) :
    (fun x => f₁ x • g₁ x) =Θ[l] fun x => f₂ x • g₂ x :=
  ⟨hf.1.smul hg.1, hf.2.smul hg.2⟩

/--
theorem `IsTheta.mul` / 定理 `IsTheta.mul`

English:
theorem IsTheta.mul
  given: {f₁ f₂ : α -> 𝕜} {g₁ g₂ : α -> 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂)
  proof: h₁.smul h₂

中文:
定理 IsTheta.mul
  条件: {f₁ f₂ : α -> 𝕜} {g₁ g₂ : α -> 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂)
  证明: h₁.smul h₂
-/
theorem IsTheta.mul {f₁ f₂ : α -> 𝕜} {g₁ g₂ : α -> 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x => f₁ x * f₂ x) =Θ[l] fun x => g₁ x * g₂ x :=
  h₁.smul h₂

/--
theorem `IsTheta.listProd` / 定理 `IsTheta.listProd`

English:
theorem IsTheta.listProd
  statement: {ι : Type*} {L : List ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
  proof: ⟨.listProd fun i hi => (h i hi).isBigO, .listProd fun i hi => (h i hi).symm.isBigO⟩

中文:
定理 IsTheta.listProd
  结论: {ι : 类型} {L : 列表 ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
  证明: ⟨.listProd fun i hi => (h i hi).isBigO, .listProd fun i hi => (h i hi).symm.isBigO⟩

Depends on / 依赖: isBigO, listProd, symm.isBigO
-/
theorem IsTheta.listProd {ι : Type*} {L : List ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
    (h : forall i in L, f i =Θ[l] g i) :
    (fun x => (L.map (f · x)).prod) =Θ[l] (fun x => (L.map (g · x)).prod) :=
  ⟨.listProd fun i hi => (h i hi).isBigO, .listProd fun i hi => (h i hi).symm.isBigO⟩

/--
theorem `IsTheta.multisetProd` / 定理 `IsTheta.multisetProd`

English:
theorem IsTheta.multisetProd
  statement: {ι : Type*} {s : Multiset ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
  proof: ⟨.multisetProd fun i hi => (h i hi).isBigO, .multisetProd fun i hi => (h i hi).symm.isBigO⟩

中文:
定理 IsTheta.multisetProd
  结论: {ι : 类型} {s : Multiset ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
  证明: ⟨.multisetProd fun i hi => (h i hi).isBigO, .multisetProd fun i hi => (h i hi).symm.isBigO⟩

Depends on / 依赖: isBigO, multisetProd, symm.isBigO
-/
theorem IsTheta.multisetProd {ι : Type*} {s : Multiset ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
    (h : forall i in s, f i =Θ[l] g i) :
    (fun x => (s.map (f · x)).prod) =Θ[l] (fun x => (s.map (g · x)).prod) :=
  ⟨.multisetProd fun i hi => (h i hi).isBigO, .multisetProd fun i hi => (h i hi).symm.isBigO⟩

/--
theorem `IsTheta.finsetProd` / 定理 `IsTheta.finsetProd`

English:
theorem IsTheta.finsetProd
  statement: {ι : Type*} {s : Finset ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
  proof: ⟨.finsetProd fun i hi => (h i hi).isBigO, .finsetProd fun i hi => (h i hi).symm.isBigO⟩

中文:
定理 IsTheta.finsetProd
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
  证明: ⟨.finsetProd fun i hi => (h i hi).isBigO, .finsetProd fun i hi => (h i hi).symm.isBigO⟩

Depends on / 依赖: finsetProd, isBigO, symm.isBigO
-/
theorem IsTheta.finsetProd {ι : Type*} {s : Finset ι} {f : ι -> α -> 𝕜} {g : ι -> α -> 𝕜'}
    (h : forall i in s, f i =Θ[l] g i) : (∏ i in s, f i ·) =Θ[l] (∏ i in s, g i ·) :=
  ⟨.finsetProd fun i hi => (h i hi).isBigO, .finsetProd fun i hi => (h i hi).symm.isBigO⟩

/--
theorem `IsTheta.inv` / 定理 `IsTheta.inv`

English:
theorem IsTheta.inv
  given: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g)
  proof: ⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩

@[simp]

中文:
定理 IsTheta.inv
  条件: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g)
  证明: ⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩

@[simp]

Depends on / 依赖: eq_zero_imp, inv_rev
-/
theorem IsTheta.inv {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) :
    (fun x => (f x)⁻¹) =Θ[l] fun x => (g x)⁻¹ :=
  ⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩

@[simp]
/--
theorem `isTheta_inv` / 定理 `isTheta_inv`

English:
theorem isTheta_inv
  given: {f : α -> 𝕜} {g : α -> 𝕜'}
  proof: ⟨fun h => by simpa only [inv_inv] using h.inv, IsTheta.inv⟩

中文:
定理 isTheta_inv
  条件: {f : α -> 𝕜} {g : α -> 𝕜'}
  证明: ⟨fun h => by simpa only [inv_inv] using h.inv, IsTheta.inv⟩

Depends on / 依赖: IsTheta, IsTheta.inv, h.inv, inv_inv
-/
theorem isTheta_inv {f : α -> 𝕜} {g : α -> 𝕜'} :
    ((fun x => (f x)⁻¹) =Θ[l] fun x => (g x)⁻¹) ↔ f =Θ[l] g :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, IsTheta.inv⟩

/--
theorem `IsTheta.div` / 定理 `IsTheta.div`

English:
theorem IsTheta.div
  given: {f₁ f₂ : α -> 𝕜} {g₁ g₂ : α -> 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂)
  proof: by
  simpa only [div_eq_mul_inv] using h₁.mul h₂.inv

中文:
定理 IsTheta.div
  条件: {f₁ f₂ : α -> 𝕜} {g₁ g₂ : α -> 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂)
  证明: by
  simpa only [div_eq_mul_inv] using h₁.mul h₂.inv

Depends on / 依赖: div_eq_mul_inv
-/
theorem IsTheta.div {f₁ f₂ : α -> 𝕜} {g₁ g₂ : α -> 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x => f₁ x / f₂ x) =Θ[l] fun x => g₁ x / g₂ x := by
  simpa only [div_eq_mul_inv] using h₁.mul h₂.inv

/--
theorem `IsTheta.pow` / 定理 `IsTheta.pow`

English:
theorem IsTheta.pow
  given: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) (n : Nat)
  proof: ⟨h.1.pow n, h.2.pow n⟩

中文:
定理 IsTheta.pow
  条件: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) (n : 自然数)
  证明: ⟨h.1.pow n, h.2.pow n⟩
-/
theorem IsTheta.pow {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) (n : Nat) :
    (fun x => f x ^ n) =Θ[l] fun x => g x ^ n :=
  ⟨h.1.pow n, h.2.pow n⟩

/--
theorem `IsTheta.zpow` / 定理 `IsTheta.zpow`

English:
theorem IsTheta.zpow
  given: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) (n : Int)
  proof: by
  cases n
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow _
  · simpa only [zpow_negSucc] using (h.pow _).inv

中文:
定理 IsTheta.zpow
  条件: {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) (n : 整数)
  证明: by
  cases n
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow _
  · simpa only [zpow_negSucc] using (h.pow _).inv

Depends on / 依赖: Int.ofNat_eq_natCast, h.pow, ofNat_eq_natCast, zpow_natCast, zpow_negSucc
-/
theorem IsTheta.zpow {f : α -> 𝕜} {g : α -> 𝕜'} (h : f =Θ[l] g) (n : Int) :
    (fun x => f x ^ n) =Θ[l] fun x => g x ^ n := by
  cases n
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow _
  · simpa only [zpow_negSucc] using (h.pow _).inv

/--
theorem `isTheta_const_const` / 定理 `isTheta_const_const`

English:
theorem isTheta_const_const
  given: {c₁ : E''} {c₂ : F''} (h₁ : c₁ != 0) (h₂ : c₂ != 0)
  proof: ⟨isBigO_const_const _ h₂ _, isBigO_const_const _ h₁ _⟩

@[simp]

中文:
定理 isTheta_const_const
  条件: {c₁ : E''} {c₂ : F''} (h₁ : c₁ != 0) (h₂ : c₂ != 0)
  证明: ⟨isBigO_const_const _ h₂ _, isBigO_const_const _ h₁ _⟩

@[simp]

Depends on / 依赖: isBigO_const_const
-/
theorem isTheta_const_const {c₁ : E''} {c₂ : F''} (h₁ : c₁ != 0) (h₂ : c₂ != 0) :
    (fun _ : α => c₁) =Θ[l] fun _ => c₂ :=
  ⟨isBigO_const_const _ h₂ _, isBigO_const_const _ h₁ _⟩

@[simp]
/--
theorem `isTheta_const_const_iff` / 定理 `isTheta_const_const_iff`

English:
theorem isTheta_const_const_iff
  given: [NeBot l] {c₁ : E''} {c₂ : F''}
  proof: by
  simpa only [IsTheta, isBigO_const_const_iff, ← iff_def] using Iff.comm

@[simp]

中文:
定理 isTheta_const_const_iff
  条件: [NeBot l] {c₁ : E''} {c₂ : F''}
  证明: by
  simpa only [IsTheta, isBigO_const_const_iff, ← iff_def] using Iff.comm

@[simp]

Depends on / 依赖: Iff.comm, IsTheta, iff_def, isBigO_const_const_iff
-/
theorem isTheta_const_const_iff [NeBot l] {c₁ : E''} {c₂ : F''} :
    ((fun _ : α => c₁) =Θ[l] fun _ => c₂) ↔ (c₁ = 0 ↔ c₂ = 0) := by
  simpa only [IsTheta, isBigO_const_const_iff, ← iff_def] using Iff.comm

@[simp]
/--
theorem `isTheta_zero_left` / 定理 `isTheta_zero_left`

English:
theorem isTheta_zero_left
  statement: (fun _ => (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0
  proof: by
  simp only [IsTheta, isBigO_zero, isBigO_zero_right_iff, true_and]

@[simp]

中文:
定理 isTheta_zero_left
  结论: (fun _ => (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0
  证明: by
  simp only [IsTheta, isBigO_zero, isBigO_zero_right_iff, true_and]

@[simp]

Depends on / 依赖: IsTheta, isBigO_zero, isBigO_zero_right_iff, true_and
-/
theorem isTheta_zero_left : (fun _ => (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0 := by
  simp only [IsTheta, isBigO_zero, isBigO_zero_right_iff, true_and]

@[simp]
/--
theorem `isTheta_zero_right` / 定理 `isTheta_zero_right`

English:
theorem isTheta_zero_right
  statement: (f'' =Θ[l] fun _ => (0 : F')) ↔ f'' =ᶠ[l] 0
  proof: isTheta_comm.trans isTheta_zero_left

中文:
定理 isTheta_zero_right
  结论: (f'' =Θ[l] fun _ => (0 : F')) ↔ f'' =ᶠ[l] 0
  证明: isTheta_comm.trans isTheta_zero_left

Depends on / 依赖: isTheta_comm, isTheta_comm.trans, isTheta_zero_left
-/
theorem isTheta_zero_right : (f'' =Θ[l] fun _ => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  isTheta_comm.trans isTheta_zero_left

/--
theorem `isTheta_const_smul_left` / 定理 `isTheta_const_smul_left`

English:
theorem isTheta_const_smul_left
  given: [NormedSpace 𝕜 E'] {c : 𝕜} (hc : c != 0)
  proof: and_congr (isBigO_const_smul_left hc) (isBigO_const_smul_right hc)

alias ⟨IsTheta.of_const_smul_left, IsTheta.const_smul_left⟩ := isTheta_const_smul_left

中文:
定理 isTheta_const_smul_left
  条件: [赋范空间 𝕜 E'] {c : 𝕜} (hc : c != 0)
  证明: and_congr (isBigO_const_smul_left hc) (isBigO_const_smul_right hc)

alias ⟨IsTheta.of_const_smul_left, IsTheta.const_smul_left⟩ := isTheta_const_smul_left

Depends on / 依赖: and_congr, isBigO_const_smul_left, isBigO_const_smul_right
-/
theorem isTheta_const_smul_left [NormedSpace 𝕜 E'] {c : 𝕜} (hc : c != 0) :
    (fun x => c • f' x) =Θ[l] g ↔ f' =Θ[l] g :=
  and_congr (isBigO_const_smul_left hc) (isBigO_const_smul_right hc)

alias ⟨IsTheta.of_const_smul_left, IsTheta.const_smul_left⟩ := isTheta_const_smul_left

/--
theorem `isTheta_const_smul_right` / 定理 `isTheta_const_smul_right`

English:
theorem isTheta_const_smul_right
  given: [NormedSpace 𝕜 F'] {c : 𝕜} (hc : c != 0)
  proof: and_congr (isBigO_const_smul_right hc) (isBigO_const_smul_left hc)

alias ⟨IsTheta.of_const_smul_right, IsTheta.const_smul_right⟩ := isTheta_const_smul_right

中文:
定理 isTheta_const_smul_right
  条件: [赋范空间 𝕜 F'] {c : 𝕜} (hc : c != 0)
  证明: and_congr (isBigO_const_smul_right hc) (isBigO_const_smul_left hc)

alias ⟨IsTheta.of_const_smul_right, IsTheta.const_smul_right⟩ := isTheta_const_smul_right

Depends on / 依赖: and_congr, isBigO_const_smul_left, isBigO_const_smul_right
-/
theorem isTheta_const_smul_right [NormedSpace 𝕜 F'] {c : 𝕜} (hc : c != 0) :
    (f =Θ[l] fun x => c • g' x) ↔ f =Θ[l] g' :=
  and_congr (isBigO_const_smul_right hc) (isBigO_const_smul_left hc)

alias ⟨IsTheta.of_const_smul_right, IsTheta.const_smul_right⟩ := isTheta_const_smul_right

/--
theorem `isTheta_const_mul_left` / 定理 `isTheta_const_mul_left`

English:
theorem isTheta_const_mul_left
  given: {c : 𝕜} {f : α -> 𝕜} (hc : c != 0)
  proof: by
  simpa only [← smul_eq_mul] using isTheta_const_smul_left hc

alias ⟨IsTheta.of_const_mul_left, IsTheta.const_mul_left⟩ := isTheta_const_mul_left

中文:
定理 isTheta_const_mul_left
  条件: {c : 𝕜} {f : α -> 𝕜} (hc : c != 0)
  证明: by
  simpa only [← smul_eq_mul] using isTheta_const_smul_left hc

alias ⟨IsTheta.of_const_mul_left, IsTheta.const_mul_left⟩ := isTheta_const_mul_left

Depends on / 依赖: isTheta_const_smul_left, smul_eq_mul
-/
theorem isTheta_const_mul_left {c : 𝕜} {f : α -> 𝕜} (hc : c != 0) :
    (fun x => c * f x) =Θ[l] g ↔ f =Θ[l] g := by
  simpa only [← smul_eq_mul] using isTheta_const_smul_left hc

alias ⟨IsTheta.of_const_mul_left, IsTheta.const_mul_left⟩ := isTheta_const_mul_left

/--
theorem `isTheta_const_mul_right` / 定理 `isTheta_const_mul_right`

English:
theorem isTheta_const_mul_right
  given: {c : 𝕜} {g : α -> 𝕜} (hc : c != 0)
  proof: by
  simpa only [← smul_eq_mul] using isTheta_const_smul_right hc

alias ⟨IsTheta.of_const_mul_right, IsTheta.const_mul_right⟩ := isTheta_const_mul_right

中文:
定理 isTheta_const_mul_right
  条件: {c : 𝕜} {g : α -> 𝕜} (hc : c != 0)
  证明: by
  simpa only [← smul_eq_mul] using isTheta_const_smul_right hc

alias ⟨IsTheta.of_const_mul_right, IsTheta.const_mul_right⟩ := isTheta_const_mul_right

Depends on / 依赖: isTheta_const_smul_right, smul_eq_mul
-/
theorem isTheta_const_mul_right {c : 𝕜} {g : α -> 𝕜} (hc : c != 0) :
    (f =Θ[l] fun x => c * g x) ↔ f =Θ[l] g := by
  simpa only [← smul_eq_mul] using isTheta_const_smul_right hc

alias ⟨IsTheta.of_const_mul_right, IsTheta.const_mul_right⟩ := isTheta_const_mul_right

/--
theorem `IsLittleO.right_isTheta_add` / 定理 `IsLittleO.right_isTheta_add`

English:
theorem IsLittleO.right_isTheta_add
  given: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  proof: ⟨h.right_isBigO_add, h.add_isBigO (isBigO_refl _ _)⟩

中文:
定理 IsLittleO.right_isTheta_add
  条件: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  证明: ⟨h.right_isBigO_add, h.add_isBigO (isBigO_refl _ _)⟩

Depends on / 依赖: add_isBigO, h.add_isBigO, h.right_isBigO_add, isBigO_refl, right_isBigO_add
-/
theorem IsLittleO.right_isTheta_add {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂) :
    f₂ =Θ[l] (f₁ + f₂) :=
  ⟨h.right_isBigO_add, h.add_isBigO (isBigO_refl _ _)⟩

/--
theorem `IsLittleO.right_isTheta_add'` / 定理 `IsLittleO.right_isTheta_add'`

English:
theorem IsLittleO.right_isTheta_add'
  given: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  proof: add_comm f₁ f₂ ▸ h.right_isTheta_add

中文:
定理 IsLittleO.right_isTheta_add'
  条件: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  证明: add_comm f₁ f₂ ▸ h.right_isTheta_add

Depends on / 依赖: add_comm, h.right_isTheta_add, right_isTheta_add
-/
theorem IsLittleO.right_isTheta_add' {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂) :
    f₂ =Θ[l] (f₂ + f₁) :=
  add_comm f₁ f₂ ▸ h.right_isTheta_add

/--
lemma `IsTheta.add_isLittleO` / 引理 `IsTheta.add_isLittleO`

English:
lemma IsTheta.add_isLittleO
  statement: {f₁ f₂ : α -> E'} {g : α -> F}
  proof: (ho.trans_isTheta hΘ.symm).right_isTheta_add'.symm.trans hΘ

中文:
引理 IsTheta.add_isLittleO
  结论: {f₁ f₂ : α -> E'} {g : α -> F}
  证明: (ho.trans_isTheta hΘ.symm).right_isTheta_add'.symm.trans hΘ

Depends on / 依赖: ho.trans_isTheta, right_isTheta_add, symm.trans, trans_isTheta
-/
lemma IsTheta.add_isLittleO {f₁ f₂ : α -> E'} {g : α -> F}
    (hΘ : f₁ =Θ[l] g) (ho : f₂ =o[l] g) : (f₁ + f₂) =Θ[l] g :=
  (ho.trans_isTheta hΘ.symm).right_isTheta_add'.symm.trans hΘ

/--
lemma `IsLittleO.add_isTheta` / 引理 `IsLittleO.add_isTheta`

English:
lemma IsLittleO.add_isTheta
  statement: {f₁ f₂ : α -> E'} {g : α -> F}
  proof: add_comm f₁ f₂ ▸ hΘ.add_isLittleO ho

中文:
引理 IsLittleO.add_isTheta
  结论: {f₁ f₂ : α -> E'} {g : α -> F}
  证明: add_comm f₁ f₂ ▸ hΘ.add_isLittleO ho

Depends on / 依赖: add_comm, add_isLittleO
-/
lemma IsLittleO.add_isTheta {f₁ f₂ : α -> E'} {g : α -> F}
    (ho : f₁ =o[l] g) (hΘ : f₂ =Θ[l] g) : (f₁ + f₂) =Θ[l] g :=
  add_comm f₁ f₂ ▸ hΘ.add_isLittleO ho

/--
theorem `isTheta_of_div_tendsto_nhds_ne_zero` / 定理 `isTheta_of_div_tendsto_nhds_ne_zero`

English:
theorem isTheta_of_div_tendsto_nhds_ne_zero
  statement: {c : 𝕜} {f g : α -> 𝕜}
  proof: by
  refine ⟨isBigO_of_div_tendsto_nhds_of_ne_zero h hc,
    isBigO_of_div_tendsto_nhds_of_ne_zero ?_ (inv_ne_zero hc)⟩
  convert! h.inv₀ hc using 1
  ext
  simp

中文:
定理 isTheta_of_div_tendsto_nhds_ne_zero
  结论: {c : 𝕜} {f g : α -> 𝕜}
  证明: by
  refine ⟨isBigO_of_div_tendsto_nhds_of_ne_zero h hc,
    isBigO_of_div_tendsto_nhds_of_ne_zero ?_ (inv_ne_zero hc)⟩
  convert! h.inv₀ hc using 1
  ext
  simp

Depends on / 依赖: convert, h.inv, inv_ne_zero, isBigO_of_div_tendsto_nhds_of_ne_zero
-/
theorem isTheta_of_div_tendsto_nhds_ne_zero {c : 𝕜} {f g : α -> 𝕜}
    (h : Tendsto (fun x => g x / f x) l (𝓝 c)) (hc : c != 0) :
    f =Θ[l] g := by
  refine ⟨isBigO_of_div_tendsto_nhds_of_ne_zero h hc,
    isBigO_of_div_tendsto_nhds_of_ne_zero ?_ (inv_ne_zero hc)⟩
  convert! h.inv₀ hc using 1
  ext
  simp

section

variable {f : α × β -> E} {g : α × β -> F} {l' : Filter β}

/--
theorem `IsTheta.fiberwise_right` / 定理 `IsTheta.fiberwise_right`

English:
theorem IsTheta.fiberwise_right
  proof: by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.fiberwise_right, h₂.fiberwise_right⟩

中文:
定理 IsTheta.fiberwise_right
  证明: by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.fiberwise_right, h₂.fiberwise_right⟩
-/
protected theorem IsTheta.fiberwise_right :
    f =Θ[l ×ˢ l'] g -> forallᶠ x in l, (f ⟨x, ·⟩) =Θ[l'] (g ⟨x, ·⟩) := by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.fiberwise_right, h₂.fiberwise_right⟩

/--
theorem `IsTheta.fiberwise_left` / 定理 `IsTheta.fiberwise_left`

English:
theorem IsTheta.fiberwise_left
  proof: by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.fiberwise_left, h₂.fiberwise_left⟩

中文:
定理 IsTheta.fiberwise_left
  证明: by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.fiberwise_left, h₂.fiberwise_left⟩
-/
protected theorem IsTheta.fiberwise_left :
    f =Θ[l ×ˢ l'] g -> forallᶠ y in l', (f ⟨·, y⟩) =Θ[l] (g ⟨·, y⟩) := by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.fiberwise_left, h₂.fiberwise_left⟩

end

section

variable (l' : Filter β)

/--
theorem `IsTheta.comp_fst` / 定理 `IsTheta.comp_fst`

English:
theorem IsTheta.comp_fst
  statement: f =Θ[l] g -> (f ∘ Prod.fst) =Θ[l ×ˢ l'] (g ∘ Prod.fst)
  proof: by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.comp_fst l', h₂.comp_fst l'⟩

中文:
定理 IsTheta.comp_fst
  结论: f =Θ[l] g -> (f ∘ 积类型.fst) =Θ[l ×ˢ l'] (g ∘ 积类型.fst)
  证明: by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.comp_fst l', h₂.comp_fst l'⟩
-/
protected theorem IsTheta.comp_fst : f =Θ[l] g -> (f ∘ Prod.fst) =Θ[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.comp_fst l', h₂.comp_fst l'⟩

/--
theorem `IsTheta.comp_snd` / 定理 `IsTheta.comp_snd`

English:
theorem IsTheta.comp_snd
  statement: f =Θ[l] g -> (f ∘ Prod.snd) =Θ[l' ×ˢ l] (g ∘ Prod.snd)
  proof: by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.comp_snd l', h₂.comp_snd l'⟩

中文:
定理 IsTheta.comp_snd
  结论: f =Θ[l] g -> (f ∘ 积类型.snd) =Θ[l' ×ˢ l] (g ∘ 积类型.snd)
  证明: by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.comp_snd l', h₂.comp_snd l'⟩
-/
protected theorem IsTheta.comp_snd : f =Θ[l] g -> (f ∘ Prod.snd) =Θ[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.comp_snd l', h₂.comp_snd l'⟩

end

end Asymptotics

namespace ContinuousOn

variable {α E F : Type*} [NormedAddGroup E] [SeminormedAddGroup F] [TopologicalSpace α]
  {s : Set α} {f : α -> E} {c : F}

/--
theorem `isTheta_principal` / 定理 `isTheta_principal`

English:
theorem isTheta_principal
  proof: ⟨hf.isBigO_principal hs hc, hf.isBigO_rev_principal hs hC c⟩

中文:
定理 isTheta_principal
  证明: ⟨hf.isBigO_principal hs hc, hf.isBigO_rev_principal hs hC c⟩
-/
protected theorem isTheta_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hc : ‖c‖ != 0) (hC : forall i in s, f i != 0) :
    f =Θ[𝓟 s] fun _ => c :=
  ⟨hf.isBigO_principal hs hc, hf.isBigO_rev_principal hs hC c⟩

end ContinuousOn
