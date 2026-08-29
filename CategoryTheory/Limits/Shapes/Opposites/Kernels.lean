/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in `C` and `Cᵒᵖ`

We construct kernels and cokernels in the opposite categories.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `CokernelCofork.IsColimit.ofπOp` / `CokernelCofork.IsColimit.ofπOp` 的定义

English:
definition CokernelCofork.IsColimit.ofπOp
  signature: {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
  body: KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimi

中文:
定义 CokernelCofork.IsColimit.ofπOp
  签名: {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
  定义体: KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimi

Depends on / 依赖: Cofork, Cofork.IsColimit, Cofork.IsColimit.hom_ext, CokernelCofork, CokernelCofork.of, IsColimit, IsLimit, KernelFork, KernelFork.IsLimit.of, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, h.desc, hom_ext, op_inj, unop_inj, unop_op, x.unop
-/
def CokernelCofork.IsColimit.ofπOp {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.op (show p.op ≫ f.op = 0 by rw [← op_comp, w, op_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimit.π_desc] using! Quiver.Hom.op_inj hb)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `CokernelCofork.IsColimit.ofπUnop` / `CokernelCofork.IsColimit.ofπUnop` 的定义

English:
definition CokernelCofork.IsColimit.ofπUnop
  signature: {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
  body: KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.

中文:
定义 CokernelCofork.IsColimit.ofπUnop
  签名: {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
  定义体: KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.

Depends on / 依赖: Cofork, Cofork.IsColimit, Cofork.IsColimit.hom_ext, CokernelCofork, CokernelCofork.of, IsColimit, IsLimit, KernelFork, KernelFork.IsLimit.of, Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, h.desc, hom_ext, op_inj, op_unop, unop_inj, x.op
-/
def CokernelCofork.IsColimit.ofπUnop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.unop (show p.unop ≫ f.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.π_desc] using! Quiver.Hom.unop_inj hb)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `KernelFork.IsLimit.ofιOp` / `KernelFork.IsLimit.ofιOp` 的定义

English:
definition KernelFork.IsLimit.ofιOp
  signature: {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
  body: CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] 

中文:
定义 KernelFork.IsLimit.ofιOp
  签名: {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
  定义体: CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] 

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.of, Fork.IsLimit.hom_ext, Fork.IsLimit.lift_, IsColimit, IsLimit, KernelFork, KernelFork.of, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, h.lift, hom_ext, op_inj, unop_inj, unop_op, x.unop
-/
def KernelFork.IsLimit.ofιOp {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.op
      (show f.op ≫ i.op = 0 by rw [← op_comp, w, op_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] using! Quiver.Hom.op_inj hb)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `KernelFork.IsLimit.ofιUnop` / `KernelFork.IsLimit.ofιUnop` 的定义

English:
definition KernelFork.IsLimit.ofιUnop
  signature: {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
  body: CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] us

中文:
定义 KernelFork.IsLimit.ofιUnop
  签名: {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
  定义体: CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] us

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.of, Fork.IsLimit.hom_ext, Fork.IsLimit.lift_, IsColimit, IsLimit, KernelFork, KernelFork.of, Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, h.lift, hom_ext, op_inj, op_unop, unop_inj, x.op
-/
def KernelFork.IsLimit.ofιUnop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.unop
      (show f.unop ≫ i.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] using! Quiver.Hom.unop_inj hb)))

end HasZeroMorphisms

end CategoryTheory.Limits
