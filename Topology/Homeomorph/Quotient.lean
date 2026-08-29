/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms between quotient spaces
-/

@[expose] public section

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Quot

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {rX : X -> X -> Prop} {rY : Y -> Y -> Prop} (e : X ≃ₜ Y)
  body: _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_map (fun x y => by simp [eq]) e.continuous
  continuous_invFun := continuous_quot_map (fun x y => by simp [eq]) e.symm.continuous

中文:
定义 congr
  签名: {rX : X -> X -> 命题} {rY : Y -> Y -> 命题} (e : X ≃ₜ Y)
  定义体: _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_map (fun x y => by simp [eq]) e.continuous
  continuous_invFun := continuous_quot_map (fun x y => by simp [eq]) e.symm.continuous
-/
protected def congr {rX : X -> X -> Prop} {rY : Y -> Y -> Prop} (e : X ≃ₜ Y)
    (eq : forall x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) : Quot rX ≃ₜ Quot rY where
  toEquiv := _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_map (fun x y => by simp [eq]) e.continuous
  continuous_invFun := continuous_quot_map (fun x y => by simp [eq]) e.symm.continuous

/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: {r r' : X -> X -> Prop} (eq : forall x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂)
  body: Quot.congr (Homeomorph.refl X) eq

中文:
定义 congrRight
  签名: {r r' : X -> X -> 命题} (eq : 对任意 x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂)
  定义体: Quot.congr (Homeomorph.refl X) eq
-/
protected def congrRight {r r' : X -> X -> Prop} (eq : forall x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) :
    Quot r ≃ₜ Quot r' := Quot.congr (Homeomorph.refl X) eq

/--
Definition of `congrLeft` / `congrLeft` 的定义

English:
definition congrLeft
  signature: {r : X -> X -> Prop} (e : X ≃ₜ Y)
  body: Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

中文:
定义 congrLeft
  签名: {r : X -> X -> 命题} (e : X ≃ₜ Y)
  定义体: Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]
-/
protected def congrLeft {r : X -> X -> Prop} (e : X ≃ₜ Y) :
    Quot r ≃ₜ Quot fun y₁ y₂ => r (e.symm y₁) (e.symm y₂) :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
  body: Quot.congr e eq

中文:
定义 congr
  签名: {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
  定义体: Quot.congr e eq
-/
protected def congr {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
    (eq : forall x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) :
    Quotient rX ≃ₜ Quotient rY := Quot.congr e eq

/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: {r r' : Setoid X}
  body: Quot.congrRight eq

中文:
定义 congrRight
  签名: {r r' : Setoid X}
  定义体: Quot.congrRight eq
-/
protected def congrRight {r r' : Setoid X}
    (eq : forall x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) : Quotient r ≃ₜ Quotient r' :=
  Quot.congrRight eq

end Quotient

/--
Definition of `quotientBot` / `quotientBot` 的定义

English:
definition quotientBot
  signature: :
  body: Setoid.quotientBotEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

中文:
定义 quotientBot
  签名: :
  定义体: Setoid.quotientBotEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

Depends on / 依赖: Setoid, Setoid.quotientBotEquiv, quotientBotEquiv
-/
def quotientBot :
    Quotient (⊥ : Setoid X) ≃ₜ X where
  toEquiv := Setoid.quotientBotEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

end Homeomorph
