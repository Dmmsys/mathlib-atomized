/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Asymptotics.Defs
/-!
# Asymptotic statements about the operator norm

This file contains lemmas about how operator norm on continuous linear maps interacts with `IsBigO`.

-/

public section

open Asymptotics


variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₃ : 𝕜₂ ->+* 𝕜₃}

namespace ContinuousLinearMap

variable [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) (l : Filter E)

/--
theorem `isBigOWith_id` / 定理 `isBigOWith_id`

English:
theorem isBigOWith_id
  statement: IsBigOWith ‖f‖ l f fun x => x
  proof: isBigOWith_of_le' _ f.le_opNorm

中文:
定理 isBigOWith_id
  结论: IsBigOWith ‖f‖ l f fun x => x
  证明: isBigOWith_of_le' _ f.le_opNorm

Depends on / 依赖: f.le_opNorm, isBigOWith_of_le, le_opNorm
-/
theorem isBigOWith_id : IsBigOWith ‖f‖ l f fun x => x :=
  isBigOWith_of_le' _ f.le_opNorm

/--
theorem `isBigO_id` / 定理 `isBigO_id`

English:
theorem isBigO_id
  statement: f =O[l] fun x => x
  proof: (f.isBigOWith_id l).isBigO

中文:
定理 isBigO_id
  结论: f =O[l] fun x => x
  证明: (f.isBigOWith_id l).isBigO

Depends on / 依赖: f.isBigOWith_id, isBigO, isBigOWith_id
-/
theorem isBigO_id : f =O[l] fun x => x :=
  (f.isBigOWith_id l).isBigO

/--
theorem `isBigOWith_comp` / 定理 `isBigOWith_comp`

English:
theorem isBigOWith_comp
  statement: [RingHomIsometric σ₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F)
  proof: (g.isBigOWith_id ⊤).comp_tendsto le_top

中文:
定理 isBigOWith_comp
  结论: [RingHomIsometric σ₂₃] {α : 类型} (g : F ->SL[σ₂₃] G) (f : α -> F)
  证明: (g.isBigOWith_id ⊤).comp_tendsto le_top

Depends on / 依赖: comp_tendsto, g.isBigOWith_id, isBigOWith_id, le_top
-/
theorem isBigOWith_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F)
    (l : Filter α) : IsBigOWith ‖g‖ l (fun x' => g (f x')) f :=
  (g.isBigOWith_id ⊤).comp_tendsto le_top

/--
theorem `isBigO_comp` / 定理 `isBigO_comp`

English:
theorem isBigO_comp
  statement: [RingHomIsometric σ₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F)
  proof: (g.isBigOWith_comp f l).isBigO

中文:
定理 isBigO_comp
  结论: [RingHomIsometric σ₂₃] {α : 类型} (g : F ->SL[σ₂₃] G) (f : α -> F)
  证明: (g.isBigOWith_comp f l).isBigO

Depends on / 依赖: g.isBigOWith_comp, isBigO, isBigOWith_comp
-/
theorem isBigO_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F)
    (l : Filter α) : (fun x' => g (f x')) =O[l] f :=
  (g.isBigOWith_comp f l).isBigO

/--
theorem `isBigOWith_sub` / 定理 `isBigOWith_sub`

English:
theorem isBigOWith_sub
  given: (x : E)
  proof: f.isBigOWith_comp _ l

中文:
定理 isBigOWith_sub
  条件: (x : E)
  证明: f.isBigOWith_comp _ l

Depends on / 依赖: f.isBigOWith_comp, isBigOWith_comp
-/
theorem isBigOWith_sub (x : E) :
    IsBigOWith ‖f‖ l (fun x' => f (x' - x)) fun x' => x' - x :=
  f.isBigOWith_comp _ l

/--
theorem `isBigO_sub` / 定理 `isBigO_sub`

English:
theorem isBigO_sub
  given: (x : E)
  proof: f.isBigO_comp _ l

中文:
定理 isBigO_sub
  条件: (x : E)
  证明: f.isBigO_comp _ l

Depends on / 依赖: f.isBigO_comp, isBigO_comp
-/
theorem isBigO_sub (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  f.isBigO_comp _ l

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (e : E ≃SL[σ₁₂] F)

section

variable [RingHomIsometric σ₁₂]

/--
theorem `isBigO_comp` / 定理 `isBigO_comp`

English:
theorem isBigO_comp
  given: {α : Type*} (f : α -> E) (l : Filter α)
  statement: (fun x' => e (f x')) =O[l] f
  proof: (e : E ->SL[σ₁₂] F).isBigO_comp f l

中文:
定理 isBigO_comp
  条件: {α : 类型} (f : α -> E) (l : Filter α)
  结论: (fun x' => e (f x')) =O[l] f
  证明: (e : E ->SL[σ₁₂] F).isBigO_comp f l

Depends on / 依赖: isBigO_comp
-/
theorem isBigO_comp {α : Type*} (f : α -> E) (l : Filter α) : (fun x' => e (f x')) =O[l] f :=
  (e : E ->SL[σ₁₂] F).isBigO_comp f l

/--
theorem `isBigO_sub` / 定理 `isBigO_sub`

English:
theorem isBigO_sub
  given: (l : Filter E) (x : E)
  statement: (fun x' => e (x' - x)) =O[l] fun x' => x' - x
  proof: (e : E ->SL[σ₁₂] F).isBigO_sub l x

中文:
定理 isBigO_sub
  条件: (l : Filter E) (x : E)
  结论: (fun x' => e (x' - x)) =O[l] fun x' => x' - x
  证明: (e : E ->SL[σ₁₂] F).isBigO_sub l x

Depends on / 依赖: isBigO_sub
-/
theorem isBigO_sub (l : Filter E) (x : E) : (fun x' => e (x' - x)) =O[l] fun x' => x' - x :=
  (e : E ->SL[σ₁₂] F).isBigO_sub l x

end

section

variable [RingHomIsometric σ₂₁]

/--
theorem `isBigO_comp_rev` / 定理 `isBigO_comp_rev`

English:
theorem isBigO_comp_rev
  given: {α : Type*} (f : α -> E) (l : Filter α)
  statement: f =O[l] fun x' => e (f x')
  proof: (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _

中文:
定理 isBigO_comp_rev
  条件: {α : 类型} (f : α -> E) (l : Filter α)
  结论: f =O[l] fun x' => e (f x')
  证明: (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _

Depends on / 依赖: congr_left, e.symm.isBigO_comp, e.symm_apply_apply, isBigO_comp, symm_apply_apply
-/
theorem isBigO_comp_rev {α : Type*} (f : α -> E) (l : Filter α) : f =O[l] fun x' => e (f x') :=
  (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _

/--
theorem `isBigO_sub_rev` / 定理 `isBigO_sub_rev`

English:
theorem isBigO_sub_rev
  given: (l : Filter E) (x : E)
  statement: (fun x' => x' - x) =O[l] fun x' => e (x' - x)
  proof: e.isBigO_comp_rev _ _

中文:
定理 isBigO_sub_rev
  条件: (l : Filter E) (x : E)
  结论: (fun x' => x' - x) =O[l] fun x' => e (x' - x)
  证明: e.isBigO_comp_rev _ _

Depends on / 依赖: e.isBigO_comp_rev, isBigO_comp_rev
-/
theorem isBigO_sub_rev (l : Filter E) (x : E) : (fun x' => x' - x) =O[l] fun x' => e (x' - x) :=
  e.isBigO_comp_rev _ _

end

end ContinuousLinearEquiv
