/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic

import Mathlib.Tactic.Attr.Register

/-!
# Tactic to reassociate comultiplication in a coalgebra

`coassoc_simps` is a simp set useful to prove tautologies on coalgebras.

The general algorithm it follows is to push the associators `TensorProduct.assoc` and
commutators `TensorProduct.comm` inwards (to the right) until they cancel against
co-multiplications.

The simp set makes the following choice of normal form
* It regards `TensorProduct.map`, `TensorProduct.assoc`, `TensorProduct.comm` as the primitive
  constructions and rewrites everything else such as `lTensor`, `leftComm` using them.
* It rewrites both sides into a right associated composition of linear maps.
  In particular `LinearMap.comp_assoc` and `LinearEquiv.coe_trans` are tagged.
* It rewrites `(f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)` into `(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁)`.

## Notes

- It is not confluent with `(ε ⊗ₘ id) ∘ₗ δ = λ⁻¹`.
  It is often useful to `trans` (or `calc`) with a term containing
  `(ε ⊗ₘ _) ∘ₗ δ` or `(_ ⊗ₘ ε) ∘ₗ δ`,
  and use one of `map_counit_comp_comul_left` `map_counit_comp_comul_right`
  `map_counit_comp_comul_left_assoc` `map_counit_comp_comul_right_assoc` to continue.

- Some lemmas (e.g. `lid_comp_map : λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id)`) loops when tagged as simp,
  so we wrap it inside a rudimentary simproc that only fires when `g ≠ id`.
-/

@[expose] public section

open TensorProduct

open LinearMap (id)
open Coalgebra

open Qq
namespace CoassocSimps

variable {R A M N P M' N' P' Q Q' M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "fun" => (TensorProduct.lid R _).toLinearMap
local notation3 "fun⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation3 "ρ" => (TensorProduct.rid R _).toLinearMap
local notation3 "ρ⁻¹" => (TensorProduct.rid R _).symm.toLinearMap
local notation3 "β" => (TensorProduct.comm R _ _).toLinearMap
local infix:90 " otimesₘ " => TensorProduct.map
local notation3 "δ" => comul (R := R)
local notation3 "ε" => counit (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id
  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.trans_symm
  LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  LinearEquiv.comp_symm LinearEquiv.symm_comp LinearEquiv.symm_symm
  LinearEquiv.coe_lTensor LinearEquiv.symm_lTensor
  LinearEquiv.coe_rTensor LinearEquiv.symm_rTensor
  IsCocomm.comm_comp_comul TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq TensorProduct.AlgebraTensorModule.rightComm_eq
  TensorProduct.tensorTensorTensorComm TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
  TensorProduct.AlgebraTensorModule.congr_eq LinearEquiv.comp_symm_assoc
  LinearEquiv.symm_comp_assoc TensorProduct.rightComm_def TensorProduct.leftComm_def
  TensorProduct.comm_symm TensorProduct.comm_comp_comm TensorProduct.comm_comp_comm_assoc

attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq
  TensorProduct.map_map_comp_assoc_symm_eq

@[coassoc_simps]
/--
lemma `TensorProduct.map_comp_assoc` / 引理 `TensorProduct.map_comp_assoc`

English:
lemma TensorProduct.map_comp_assoc
  proof: by
  rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_comp]

@[coassoc_simps← ]

中文:
引理 张量积.map_comp_assoc
  证明: by
  rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_comp]

@[coassoc_simps← ]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, TensorProduct, TensorProduct.map_comp, comp_assoc, map_comp
-/
lemma TensorProduct.map_comp_assoc
    (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (f' : M' ->ₗ[R] N') (g' : N' ->ₗ[R] P') (φ : M₁ ->ₗ[R] M otimes[R] M') :
    map g g' ∘ₗ map f f' ∘ₗ φ = map (g ∘ₗ f) (g' ∘ₗ f') ∘ₛₗ φ := by
  rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_comp]

@[coassoc_simps← ]
/--
lemma `TensorProduct.map_map_comp_assoc_eq_assoc` / 引理 `TensorProduct.map_map_comp_assoc_eq_assoc`

English:
lemma TensorProduct.map_map_comp_assoc_eq_assoc
  proof: by
  rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]

中文:
引理 张量积.map_map_comp_assoc_eq_assoc
  证明: by
  rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, TensorProduct, TensorProduct.map_map_comp_assoc_eq, comp_assoc, map_map_comp_assoc_eq
-/
lemma TensorProduct.map_map_comp_assoc_eq_assoc
    (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f : M ->ₗ[R] M₁ otimes[R] M₂ otimes[R] M₃) :
    f₁ otimesₘ (f₂ otimesₘ f₃) ∘ₗ α ∘ₗ f = α ∘ₗ ((f₁ otimesₘ f₂) otimesₘ f₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]
/--
lemma `TensorProduct.map_map_comp_assoc_symm_eq_assoc` / 引理 `TensorProduct.map_map_comp_assoc_symm_eq_assoc`

English:
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
  proof: by
  rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]

中文:
引理 张量积.map_map_comp_assoc_symm_eq_assoc
  证明: by
  rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, TensorProduct, TensorProduct.map_map_comp_assoc_symm_eq, comp_assoc, map_map_comp_assoc_symm_eq
-/
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
    (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f : M ->ₗ[R] M₁ otimes[R] (M₂ otimes[R] M₃)) :
    (f₁ otimesₘ f₂) otimesₘ f₃ ∘ₗ α⁻¹ ∘ₗ f = α⁻¹ ∘ₗ (f₁ otimesₘ (f₂ otimesₘ f₃)) ∘ₗ f := by
  rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]
/--
lemma `assoc_comp_map_map_comp` / 引理 `assoc_comp_map_map_comp`

English:
lemma assoc_comp_map_map_comp
  proof: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]

中文:
引理 assoc_comp_map_map_comp
  证明: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, map_map_comp_assoc_eq
-/
lemma assoc_comp_map_map_comp
    (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) :
    α ∘ₗ (((f₁ otimesₘ f₂) ∘ₗ f₁₂) otimesₘ f₃) = (f₁ otimesₘ (f₂ otimesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id) := by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]
/--
lemma `assoc_comp_map_map_comp_assoc` / 引理 `assoc_comp_map_map_comp_assoc`

English:
lemma assoc_comp_map_map_comp_assoc
  proof: by
  simp only [← LinearMap.comp_assoc, assoc_comp_map_map_comp]

中文:
引理 assoc_comp_map_map_comp_assoc
  证明: by
  simp only [← LinearMap.comp_assoc, assoc_comp_map_map_comp]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_comp_map_map_comp, comp_assoc
-/
lemma assoc_comp_map_map_comp_assoc
    (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂)
    (f : M ->ₗ[R] M otimes[R] M₃) :
    α ∘ₗ (((f₁ otimesₘ f₂) ∘ₗ f₁₂) otimesₘ f₃) ∘ₗ f =
      (f₁ otimesₘ (f₂ otimesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_comp_map_map_comp]

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₃ ≠ id`.
/--
lemma `assoc_comp_map` / 引理 `assoc_comp_map`

English:
lemma assoc_comp_map
  given: (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂)
  proof: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_eq]
  simp only [coassoc_simps]

中文:
引理 assoc_comp_map
  条件: (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂)
  证明: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_eq]
  simp only [coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc, map_map_comp_assoc_eq
-/
lemma assoc_comp_map (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) :
    α ∘ₗ (f₁₂ otimesₘ f₃) = (id otimesₘ (id otimesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id) := by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_eq]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_comp_map` that only fires when `f₃ ≠ id`. -/
simproc_decl assoc_comp_map_simproc
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (_ otimesₘ _)) := .ofQ fun _ t e => do
  let_expr LinearMap R _ _ _ _ T₁ T₂ _ _ _ _ ← t
    | return .continue
  let_expr TensorProduct _ instR M M₃ instM instM₃ instRM instRM₃ ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₁ T₃ instM₁ _ instRM₁ _ ← T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₂ N₃ instM₂ instN₃ instRM₂ instRN₃ ← T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₃).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₃ : Q(Type u₆) := N₃
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₃) := instN₃
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₃) := instRN₃
  have e : Q($M otimes[$R] $M₃ ->ₗ[$R] $M₁ otimes[$R] ($M₂ otimes[$R] $N₃)) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$M₁» «$M₂» «$N₃»).toLinearMap ∘ₗ ($f₁₂ otimesₘ $f₃)) =>
  match_expr f₃ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q((id otimesₘ (id otimesₘ $f₃)) ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
    ∘ₗ ($f₁₂ otimesₘ id)) (some q(assoc_comp_map ..))

attribute [coassoc_simps] assoc_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₃ ≠ id`.
/--
lemma `assoc_comp_map_assoc` / 引理 `assoc_comp_map_assoc`

English:
lemma assoc_comp_map_assoc
  statement: (f₃ : M₃ ->ₗ[R] N₃)
  proof: by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

中文:
引理 assoc_comp_map_assoc
  结论: (f₃ : M₃ ->ₗ[R] N₃)
  证明: by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc
-/
lemma assoc_comp_map_assoc (f₃ : M₃ ->ₗ[R] N₃)
    (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) (f : P ->ₗ[R] M otimes[R] M₃) :
    α ∘ₗ (f₁₂ otimesₘ f₃) ∘ₗ f = (id otimesₘ (id otimesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id) ∘ₗ f := by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_comp_map_assoc` that only fires when `f₃ ≠ id`. -/
simproc_decl assoc_comp_map_assoc_simproc
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (_ otimesₘ _) ∘ₗ _) := .ofQ fun _ _ e => do
  let_expr LinearMap.comp R _ _ P _ T₂ _ _ _ instP _ _ instRP _ _ _ _ _ _ _ e' ← e
    | return .continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ← e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M M₃ instM instM₃ instRM instRM₃ ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₁ T₃ instM₁ _ instRM₁ _ ← T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₂ N₃ instM₂ instN₃ instRM₂ instRN₃ ← T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₃).sortLevel! | return .continue
  let .succ u₇ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₃ : Q(Type u₆) := N₃
  have P : Q(Type u₇) := P
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₃) := instN₃
  have : Q(AddCommMonoid $P) := instP
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₃) := instRN₃
  have : Q(Module $R $P) := instRP
  have e : Q($P ->ₗ[$R] $M₁ otimes[$R] ($M₂ otimes[$R] $N₃)) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$M₁» «$M₂» «$N₃»).toLinearMap ∘ₗ
      ($f₁₂ otimesₘ $f₃) ∘ₗ ($f : _ ->ₗ[_] «$M» otimes «$M₃»)) =>
  match_expr f₃ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q((id otimesₘ (id otimesₘ $f₃)) ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
∘ₗ ($f₁₂ otimesₘ id) ∘ₗ f) (some q(assoc_comp_map_assoc ..))

attribute [coassoc_simps] assoc_comp_map_assoc_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₁ ≠ id`.
/--
lemma `assoc_symm_comp_map` / 引理 `assoc_symm_comp_map`

English:
lemma assoc_symm_comp_map
  proof: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

中文:
引理 assoc_symm_comp_map
  证明: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc, map_map_comp_assoc_symm_eq
-/
lemma assoc_symm_comp_map
    (f₁ : M₁ ->ₗ[R] N₁) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) :
    α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) = ((f₁ otimesₘ .id) otimesₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id otimesₘ f₂₃) := by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_symm_comp_map` that only fires when `f₁ ≠ id`. -/
simproc_decl assoc_symm_comp_map_simproc
    ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (_ otimesₘ _)) := .ofQ fun _ t e => do
  let_expr LinearMap R _ _ _ _ T₁ T₂ _ _ _ _ ← t
    | return .continue
  let_expr TensorProduct _ instR M₁ M instM₁ instM instRM₁ instRM ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ T₃ M₃ _ instM₃ _ instRM₃ ← T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ N₁ M₂ instN₁ instM₂ instRN₁ instRM₂ ← T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₁).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₁ : Q(Type u₆) := N₁
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₁) := instN₁
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₁) := instRN₁
  have e : Q($M₁ otimes[$R] $M ->ₗ[$R] $N₁ otimes[$R] $M₂ otimes[$R] $M₃) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$N₁» «$M₂» «$M₃»).symm.toLinearMap ∘ₗ ($f₁ otimesₘ $f₂₃)) =>
  match_expr f₁ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q((($f₁ otimesₘ id) otimesₘ id) ∘ₗ
    (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (id otimesₘ $f₂₃))
      (some q(assoc_symm_comp_map ..))

attribute [coassoc_simps] assoc_symm_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₁ ≠ id`.
/--
lemma `assoc_symm_comp_map_assoc` / 引理 `assoc_symm_comp_map_assoc`

English:
lemma assoc_symm_comp_map_assoc
  statement: (f₁ : M₁ ->ₗ[R] N₁)
  proof: by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

中文:
引理 assoc_symm_comp_map_assoc
  结论: (f₁ : M₁ ->ₗ[R] N₁)
  证明: by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc
-/
lemma assoc_symm_comp_map_assoc (f₁ : M₁ ->ₗ[R] N₁)
    (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) (f : P ->ₗ[R] M₁ otimes[R] M) :
    α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) ∘ₗ f = ((f₁ otimesₘ .id) otimesₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id otimesₘ f₂₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_symm_comp_map_assoc` that only fires when `f₁ ≠ id`. -/
simproc_decl assoc_symm_comp_map_assoc_simproc
    ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (_ otimesₘ _) ∘ₗ _) := .ofQ fun _ _ e => do
  let_expr LinearMap.comp R _ _ P _ T₂ _ _ _ instP _ _ instRP _ _ _ _ _ _ _ e' ← e
    | return .continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ← e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M₁ M instM₁ instM instRM₁ instRM ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ T₃ M₃ _ instM₃ _ instRM₃ ← T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ N₁ M₂ instN₁ instM₂ instRN₁ instRM₂ ← T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₁).sortLevel! | return .continue
  let .succ u₇ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₁ : Q(Type u₆) := N₁
  have P : Q(Type u₇) := P
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₁) := instN₁
  have : Q(AddCommMonoid $P) := instP
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₁) := instRN₁
  have : Q(Module $R $P) := instRP
  have e : Q($P ->ₗ[$R] $N₁ otimes[$R] $M₂ otimes[$R] $M₃) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$N₁» «$M₂» «$M₃»).symm.toLinearMap ∘ₗ
      ($f₁ otimesₘ $f₂₃) ∘ₗ ($f : _ ->ₗ[_] «$M₁» otimes «$M»)) =>
  match_expr f₁ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q((($f₁ otimesₘ id) otimesₘ id) ∘ₗ
(TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (id otimesₘ $f₂₃) ∘ₗ f)
      (some q(assoc_symm_comp_map_assoc ..))

attribute [coassoc_simps] assoc_symm_comp_map_assoc_simproc

@[coassoc_simps]
/--
lemma `assoc_symm_comp_map_map_comp` / 引理 `assoc_symm_comp_map_map_comp`

English:
lemma assoc_symm_comp_map_map_comp
  proof: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]

中文:
引理 assoc_symm_comp_map_map_comp
  证明: by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, map_map_comp_assoc_symm_eq
-/
lemma assoc_symm_comp_map_map_comp
    (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) :
    α⁻¹ ∘ₗ (f₁ otimesₘ (f₂ otimesₘ f₃ ∘ₗ f₂₃)) = ((f₁ otimesₘ f₂) otimesₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id otimesₘ f₂₃) := by
  rw [← LinearMap.comp_assoc]; rw [map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]
/--
lemma `assoc_symm_comp_map_map_comp_assoc` / 引理 `assoc_symm_comp_map_map_comp_assoc`

English:
lemma assoc_symm_comp_map_map_comp_assoc
  proof: by
  simp only [← LinearMap.comp_assoc, assoc_symm_comp_map_map_comp]

@[coassoc_simps]

中文:
引理 assoc_symm_comp_map_map_comp_assoc
  证明: by
  simp only [← LinearMap.comp_assoc, assoc_symm_comp_map_map_comp]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_symm_comp_map_map_comp, comp_assoc
-/
lemma assoc_symm_comp_map_map_comp_assoc
    (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃)
    (f : N ->ₗ[R] M₁ otimes[R] M) :
    α⁻¹ ∘ₗ (f₁ otimesₘ (f₂ otimesₘ f₃ ∘ₗ f₂₃)) ∘ₗ f = ((f₁ otimesₘ f₂) otimesₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id otimesₘ f₂₃) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_symm_comp_map_map_comp]

@[coassoc_simps]
/--
lemma `assoc_symm_comp_lid_symm` / 引理 `assoc_symm_comp_lid_symm`

English:
lemma assoc_symm_comp_lid_symm
  proof: rfl

@[coassoc_simps]

中文:
引理 assoc_symm_comp_lid_symm
  证明: rfl

@[coassoc_simps]
-/
lemma assoc_symm_comp_lid_symm :
    (α⁻¹ ∘ₗ fun⁻¹ : M otimes[R] N ->ₗ[R] _) = fun⁻¹ otimesₘ id := rfl

@[coassoc_simps]
/--
lemma `assoc_symm_comp_lid_symm_assoc` / 引理 `assoc_symm_comp_lid_symm_assoc`

English:
lemma assoc_symm_comp_lid_symm_assoc
  given: (f : P ->ₗ[R] M otimes[R] N)
  proof: rfl

@[coassoc_simps]

中文:
引理 assoc_symm_comp_lid_symm_assoc
  条件: (f : P ->ₗ[R] M otimes[R] N)
  证明: rfl

@[coassoc_simps]
-/
lemma assoc_symm_comp_lid_symm_assoc (f : P ->ₗ[R] M otimes[R] N) :
    α⁻¹ ∘ₗ fun⁻¹ ∘ₗ f = fun⁻¹ otimesₘ id ∘ₗ f := rfl

@[coassoc_simps]
/--
lemma `assoc_symm_comp_map_lid_symm` / 引理 `assoc_symm_comp_map_lid_symm`

English:
lemma assoc_symm_comp_map_lid_symm
  given: (f : M ->ₗ[R] M')
  proof: by
  ext; rfl

@[coassoc_simps]

中文:
引理 assoc_symm_comp_map_lid_symm
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext; rfl

@[coassoc_simps]
-/
lemma assoc_symm_comp_map_lid_symm (f : M ->ₗ[R] M') :
    α⁻¹ ∘ₗ f otimesₘ fun⁻¹ = (f otimesₘ id ∘ₗ ρ⁻¹) otimesₘ id (M := N) := by
  ext; rfl

@[coassoc_simps]
/--
lemma `assoc_symm_comp_map_lid_symm_assoc` / 引理 `assoc_symm_comp_map_lid_symm_assoc`

English:
lemma assoc_symm_comp_map_lid_symm_assoc
  given: (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]

中文:
引理 assoc_symm_comp_map_lid_symm_assoc
  条件: (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_symm_comp_map_lid_symm, comp_assoc, simp_rw
-/
lemma assoc_symm_comp_map_lid_symm_assoc (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otimes[R] N) :
    α⁻¹ ∘ₗ f otimesₘ fun⁻¹ ∘ₗ g = (f otimesₘ id ∘ₗ ρ⁻¹) otimesₘ id ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]
/--
lemma `assoc_symm_comp_map_rid_symm` / 引理 `assoc_symm_comp_map_rid_symm`

English:
lemma assoc_symm_comp_map_rid_symm
  given: (f : M ->ₗ[R] M')
  proof: by
  ext; rfl

@[coassoc_simps]

中文:
引理 assoc_symm_comp_map_rid_symm
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext; rfl

@[coassoc_simps]

Depends on / 依赖: ofLinearWellFoundedLT
-/
lemma assoc_symm_comp_map_rid_symm (f : M ->ₗ[R] M') :
    α⁻¹ ∘ₗ f otimesₘ ρ⁻¹ = (f otimesₘ id (M := N)) otimesₘ id ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
/--
lemma `assoc_symm_comp_map_rid_symm_assoc` / 引理 `assoc_symm_comp_map_rid_symm_assoc`

English:
lemma assoc_symm_comp_map_rid_symm_assoc
  given: (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]

中文:
引理 assoc_symm_comp_map_rid_symm_assoc
  条件: (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_symm_comp_map_rid_symm, comp_assoc, simp_rw
-/
lemma assoc_symm_comp_map_rid_symm_assoc (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otimes[R] N) :
    α⁻¹ ∘ₗ f otimesₘ ρ⁻¹ ∘ₗ g = (f otimesₘ id) otimesₘ id ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]
/--
lemma `assoc_comp_rid_symm` / 引理 `assoc_comp_rid_symm`

English:
lemma assoc_comp_rid_symm
  proof: by ext; rfl

@[coassoc_simps]

中文:
引理 assoc_comp_rid_symm
  证明: by ext; rfl

@[coassoc_simps]
-/
lemma assoc_comp_rid_symm :
    (α ∘ₗ ρ⁻¹ : M otimes[R] N ->ₗ[R] _) = id otimesₘ ρ⁻¹ := by ext; rfl

@[coassoc_simps]
/--
lemma `assoc_comp_rid_symm_assoc` / 引理 `assoc_comp_rid_symm_assoc`

English:
lemma assoc_comp_rid_symm_assoc
  given: (f : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]

中文:
引理 assoc_comp_rid_symm_assoc
  条件: (f : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_comp_rid_symm, comp_assoc, simp_rw
-/
lemma assoc_comp_rid_symm_assoc (f : P ->ₗ[R] M otimes[R] N) :
    α ∘ₗ ρ⁻¹ ∘ₗ f = id otimesₘ ρ⁻¹ ∘ₗ f := by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]
/--
lemma `assoc_comp_map_lid_symm` / 引理 `assoc_comp_map_lid_symm`

English:
lemma assoc_comp_map_lid_symm
  given: (f : N ->ₗ[R] N')
  proof: by
  ext; rfl

@[coassoc_simps]

中文:
引理 assoc_comp_map_lid_symm
  条件: (f : N ->ₗ[R] N')
  证明: by
  ext; rfl

@[coassoc_simps]
-/
lemma assoc_comp_map_lid_symm (f : N ->ₗ[R] N') :
    α ∘ₗ fun⁻¹ otimesₘ f = (id otimesₘ (id (M := M) otimesₘ f)) ∘ₗ fun⁻¹ := by
  ext; rfl

@[coassoc_simps]
/--
lemma `assoc_comp_map_lid_symm_assoc` / 引理 `assoc_comp_map_lid_symm_assoc`

English:
lemma assoc_comp_map_lid_symm_assoc
  given: (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]

中文:
引理 assoc_comp_map_lid_symm_assoc
  条件: (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_comp_map_lid_symm, comp_assoc, simp_rw
-/
lemma assoc_comp_map_lid_symm_assoc (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] N) :
    α ∘ₗ fun⁻¹ otimesₘ f ∘ₗ g = (id otimesₘ (id otimesₘ f)) ∘ₗ fun⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]
/--
lemma `assoc_comp_map_rid_symm` / 引理 `assoc_comp_map_rid_symm`

English:
lemma assoc_comp_map_rid_symm
  given: (f : N ->ₗ[R] N')
  proof: by
  ext; rfl

@[coassoc_simps]

中文:
引理 assoc_comp_map_rid_symm
  条件: (f : N ->ₗ[R] N')
  证明: by
  ext; rfl

@[coassoc_simps]
-/
lemma assoc_comp_map_rid_symm (f : N ->ₗ[R] N') :
    α ∘ₗ ρ⁻¹ otimesₘ f = id (M := M) otimesₘ ((id otimesₘ f) ∘ₗ fun⁻¹) := by
  ext; rfl

@[coassoc_simps]
/--
lemma `assoc_comp_map_rid_symm_assoc` / 引理 `assoc_comp_map_rid_symm_assoc`

English:
lemma assoc_comp_map_rid_symm_assoc
  given: (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

中文:
引理 assoc_comp_map_rid_symm_assoc
  条件: (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, assoc_comp_map_rid_symm, comp_assoc, simp_rw
-/
lemma assoc_comp_map_rid_symm_assoc (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] N) :
    α ∘ₗ ρ⁻¹ otimesₘ f ∘ₗ g = id otimesₘ ((id otimesₘ f) ∘ₗ fun⁻¹) ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `g ≠ id`.
/--
lemma `lid_comp_map` / 引理 `lid_comp_map`

English:
lemma lid_comp_map
  given: (f : M ->ₗ[R] R) (g : N ->ₗ[R] M')
  proof: by
  ext; simp

中文:
引理 lid_comp_map
  条件: (f : M ->ₗ[R] R) (g : N ->ₗ[R] M')
  证明: by
  ext; simp
-/
lemma lid_comp_map (f : M ->ₗ[R] R) (g : N ->ₗ[R] M') :
    fun ∘ₗ (f otimesₘ g) = g ∘ₗ fun ∘ₗ (f otimesₘ id) := by
  ext; simp

/-- Simproc version of `lid_comp_map` that only fires when `g ≠ id`. -/
simproc_decl lid_comp_map_simproc
    ((TensorProduct.lid _ _).toLinearMap ∘ₗ (_ otimesₘ _)) := .ofQ fun _ t e => do
  let_expr LinearMap R _ _ _ _ T₁ M' _ instM' _ instRM' ← t
    | return .continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N : Q(Type u₄) := N
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N) := instN
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N) := instRN
  have e : Q($M otimes[$R] $N ->ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.lid «$R» «$M'»).toLinearMap ∘ₗ ($f otimesₘ $g)) =>
  match_expr g with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q($g ∘ₗ (TensorProduct.lid $R _).toLinearMap ∘ₗ ($f otimesₘ .id))
    (some q(lid_comp_map ..))

attribute [coassoc_simps] lid_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `g ≠ id`.
/--
lemma `lid_comp_map_assoc` / 引理 `lid_comp_map_assoc`

English:
lemma lid_comp_map_assoc
  given: (f : M ->ₗ[R] R) (g : N ->ₗ[R] M') (h : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp only [← LinearMap.comp_assoc, lid_comp_map _ g]

中文:
引理 lid_comp_map_assoc
  条件: (f : M ->ₗ[R] R) (g : N ->ₗ[R] M') (h : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp only [← LinearMap.comp_assoc, lid_comp_map _ g]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, lid_comp_map
-/
lemma lid_comp_map_assoc (f : M ->ₗ[R] R) (g : N ->ₗ[R] M') (h : P ->ₗ[R] M otimes[R] N) :
    fun ∘ₗ (f otimesₘ g) ∘ₗ h = g ∘ₗ fun ∘ₗ (f otimesₘ id) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, lid_comp_map _ g]

/-- Simproc version of `lid_comp_map_assoc` that only fires when `g ≠ id`. -/
simproc_decl lid_comp_map_assoc_simproc
    ((TensorProduct.lid _ _).toLinearMap ∘ₗ (_ otimesₘ _) ∘ₗ _) := .ofQ fun _ _ e => do
  let_expr LinearMap.comp R _ _ P _ M' _ _ _ instP _ instM' instRP _ instRM' _ _ _ _ _ e' ← e
    | return .continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ← e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N : Q(Type u₄) := N
  have P : Q(Type u₅) := P
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N) := instN
  have : Q(AddCommMonoid $P) := instP
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N) := instRN
  have : Q(Module $R $P) := instRP
  have e : Q($P ->ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.lid «$R» «$M'»).toLinearMap ∘ₗ ($f otimesₘ $g) ∘ₗ
      ($h : «$P» ->ₗ[«$R»] «$M» otimes[«$R»] «$N»)) =>
  match_expr g with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q($g ∘ₗ (TensorProduct.lid $R _).toLinearMap ∘ₗ ($f otimesₘ .id) ∘ₗ $h)
    (some q(lid_comp_map_assoc ..))

attribute [coassoc_simps] lid_comp_map_assoc_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f ≠ id`.
/--
lemma `rid_comp_map` / 引理 `rid_comp_map`

English:
lemma rid_comp_map
  given: (f : M ->ₗ[R] M') (g : N ->ₗ[R] R)
  proof: by
  ext; simp

中文:
引理 rid_comp_map
  条件: (f : M ->ₗ[R] M') (g : N ->ₗ[R] R)
  证明: by
  ext; simp
-/
lemma rid_comp_map (f : M ->ₗ[R] M') (g : N ->ₗ[R] R) :
    ρ ∘ₗ (f otimesₘ g) = f ∘ₗ ρ ∘ₗ (.id otimesₘ g) := by
  ext; simp

/-- Simproc version of `rid_comp_map` that only fires when `g ≠ id`. -/
simproc_decl rid_comp_map_simproc
    ((TensorProduct.rid _ _).toLinearMap ∘ₗ (_ otimesₘ _)) := .ofQ fun _ t e => do
  let_expr LinearMap R _ _ _ _ T₁ M' _ instM' _ instRM' ← t
    | return .continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N : Q(Type u₄) := N
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N) := instN
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N) := instRN
  have e : Q($M otimes[$R] $N ->ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.rid «$R» «$M'»).toLinearMap ∘ₗ ($f otimesₘ $g)) =>
  match_expr f with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q($f ∘ₗ (TensorProduct.rid $R _).toLinearMap ∘ₗ (.id otimesₘ $g))
    (some q(rid_comp_map ..))

attribute [coassoc_simps] rid_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f ≠ id`.
/--
lemma `rid_comp_map_assoc` / 引理 `rid_comp_map_assoc`

English:
lemma rid_comp_map_assoc
  given: (f : M ->ₗ[R] M') (g : N ->ₗ[R] R) (h : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp only [← LinearMap.comp_assoc, rid_comp_map f]

中文:
引理 rid_comp_map_assoc
  条件: (f : M ->ₗ[R] M') (g : N ->ₗ[R] R) (h : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp only [← LinearMap.comp_assoc, rid_comp_map f]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, rid_comp_map
-/
lemma rid_comp_map_assoc (f : M ->ₗ[R] M') (g : N ->ₗ[R] R) (h : P ->ₗ[R] M otimes[R] N) :
    ρ ∘ₗ (f otimesₘ g) ∘ₗ h = f ∘ₗ ρ ∘ₗ (.id otimesₘ g) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, rid_comp_map f]

/-- Simproc version of `rid_comp_map_assoc` that only fires when `f ≠ id`. -/
simproc_decl rid_comp_map_assoc_simproc
    ((TensorProduct.rid _ _).toLinearMap ∘ₗ (_ otimesₘ _) ∘ₗ _) := .ofQ fun _ _ e => do
  let_expr LinearMap.comp R _ _ P _ M' _ _ _ instP _ instM' instRP _ instRM' _ _ _ _ _ e' ← e
    | return Lean.Meta.Simp.StepQ.continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ← e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R : Q(Type u₁) := R
  have M : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N : Q(Type u₄) := N
  have P : Q(Type u₅) := P
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N) := instN
  have : Q(AddCommMonoid $P) := instP
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N) := instRN
  have : Q(Module $R $P) := instRP
  have e : Q($P ->ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.rid «$R» «$M'»).toLinearMap ∘ₗ ($f otimesₘ $g) ∘ₗ
      ($h : «$P» ->ₗ[«$R»] «$M» otimes[«$R»] «$N»)) =>
  match_expr f with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
return .visit (e := e) .mk q($f ∘ₗ (TensorProduct.rid $R _).toLinearMap ∘ₗ (.id otimesₘ $g) ∘ₗ $h)
    (some q(rid_comp_map_assoc ..))

attribute [coassoc_simps] rid_comp_map_assoc_simproc

@[coassoc_simps]
/--
lemma `lid_symm_comp` / 引理 `lid_symm_comp`

English:
lemma lid_symm_comp
  given: (f : M ->ₗ[R] M')
  proof: by
  ext; rfl

@[coassoc_simps]

中文:
引理 lid_symm_comp
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext; rfl

@[coassoc_simps]
-/
lemma lid_symm_comp (f : M ->ₗ[R] M') :
    fun⁻¹ ∘ₗ f = (id otimesₘ f) ∘ₗ fun⁻¹ := by
  ext; rfl

@[coassoc_simps]
/--
lemma `rid_symm_comp` / 引理 `rid_symm_comp`

English:
lemma rid_symm_comp
  given: (f : M ->ₗ[R] M')
  proof: by
  ext; rfl

@[coassoc_simps]

中文:
引理 rid_symm_comp
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext; rfl

@[coassoc_simps]
-/
lemma rid_symm_comp (f : M ->ₗ[R] M') :
    ρ⁻¹ ∘ₗ f = (f otimesₘ id) ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
/--
lemma `symm_comp_lid_symm` / 引理 `symm_comp_lid_symm`

English:
lemma symm_comp_lid_symm
  proof: rfl

@[coassoc_simps]

中文:
引理 symm_comp_lid_symm
  证明: rfl

@[coassoc_simps]
-/
lemma symm_comp_lid_symm :
    (β ∘ₗ fun⁻¹ : M ->ₗ[R] _) = ρ⁻¹ := rfl

@[coassoc_simps]
/--
lemma `symm_comp_lid_symm_assoc` / 引理 `symm_comp_lid_symm_assoc`

English:
lemma symm_comp_lid_symm_assoc
  given: (f : M ->ₗ[R] M')
  proof: rfl

@[coassoc_simps]

中文:
引理 symm_comp_lid_symm_assoc
  条件: (f : M ->ₗ[R] M')
  证明: rfl

@[coassoc_simps]
-/
lemma symm_comp_lid_symm_assoc (f : M ->ₗ[R] M') :
    β ∘ₗ fun⁻¹ ∘ₗ f = ρ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
/--
lemma `symm_comp_rid_symm` / 引理 `symm_comp_rid_symm`

English:
lemma symm_comp_rid_symm
  proof: rfl

@[coassoc_simps]

中文:
引理 symm_comp_rid_symm
  证明: rfl

@[coassoc_simps]
-/
lemma symm_comp_rid_symm :
    (β ∘ₗ ρ⁻¹ : M ->ₗ[R] _) = fun⁻¹ := rfl

@[coassoc_simps]
/--
lemma `symm_comp_rid_symm_assoc` / 引理 `symm_comp_rid_symm_assoc`

English:
lemma symm_comp_rid_symm_assoc
  given: (f : M ->ₗ[R] M')
  proof: rfl

@[coassoc_simps]

中文:
引理 symm_comp_rid_symm_assoc
  条件: (f : M ->ₗ[R] M')
  证明: rfl

@[coassoc_simps]
-/
lemma symm_comp_rid_symm_assoc (f : M ->ₗ[R] M') :
    β ∘ₗ ρ⁻¹ ∘ₗ f = fun⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
/--
lemma `symm_comp_map` / 引理 `symm_comp_map`

English:
lemma symm_comp_map
  given: (f : M ->ₗ[R] M') (g : N ->ₗ[R] N')
  proof: by ext; rfl

@[coassoc_simps]

中文:
引理 symm_comp_map
  条件: (f : M ->ₗ[R] M') (g : N ->ₗ[R] N')
  证明: by ext; rfl

@[coassoc_simps]
-/
lemma symm_comp_map (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') :
    β ∘ₗ (f otimesₘ g) = (g otimesₘ f) ∘ₗ β := by ext; rfl

@[coassoc_simps]
/--
lemma `symm_comp_map_assoc` / 引理 `symm_comp_map_assoc`

English:
lemma symm_comp_map_assoc
  given: (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') (h : P ->ₗ[R] M otimes[R] N)
  proof: by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]

中文:
引理 symm_comp_map_assoc
  条件: (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') (h : P ->ₗ[R] M otimes[R] N)
  证明: by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, symm_comp_map
-/
lemma symm_comp_map_assoc (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') (h : P ->ₗ[R] M otimes[R] N) :
    β ∘ₗ (f otimesₘ g) ∘ₗ h = (g otimesₘ f) ∘ₗ β ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]
/--
lemma `coassoc_left` / 引理 `coassoc_left`

English:
lemma coassoc_left
  given: [Coalgebra R M] (f : M ->ₗ[R] M')
  proof: by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]

中文:
引理 coassoc_left
  条件: [余algebra R M] (f : M ->ₗ[R] M')
  证明: by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, LinearMap.lTensor_def, coassoc, coassoc_simps, comp_assoc, lTensor_def, map_map_comp_assoc_eq, simp_rw
-/
lemma coassoc_left [Coalgebra R M] (f : M ->ₗ[R] M') :
    α ∘ₗ (δ otimesₘ f) ∘ₗ δ = (id otimesₘ (id otimesₘ f)) ∘ₗ (id otimesₘ δ) ∘ₗ δ := by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
/--
lemma `coassoc_left_assoc` / 引理 `coassoc_left_assoc`

English:
lemma coassoc_left_assoc
  given: [Coalgebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M)
  proof: by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]

中文:
引理 coassoc_left_assoc
  条件: [余algebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M)
  证明: by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc
-/
lemma coassoc_left_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M) :
    α ∘ₗ (δ otimesₘ f) ∘ₗ δ ∘ₗ g = (id otimesₘ (id otimesₘ f)) ∘ₗ (id otimesₘ δ) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]
/--
lemma `coassoc_right` / 引理 `coassoc_right`

English:
lemma coassoc_right
  given: [Coalgebra R M] (f : M ->ₗ[R] M')
  proof: by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]

中文:
引理 coassoc_right
  条件: [余algebra R M] (f : M ->ₗ[R] M')
  证明: by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, LinearMap.rTensor_def, coassoc_simps, coassoc_symm, comp_assoc, map_map_comp_assoc_symm_eq, rTensor_def, simp_rw
-/
lemma coassoc_right [Coalgebra R M] (f : M ->ₗ[R] M') :
    α⁻¹ ∘ₗ (f otimesₘ δ) ∘ₗ δ = ((f otimesₘ id) otimesₘ id) ∘ₗ (δ otimesₘ id) ∘ₗ δ := by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
/--
lemma `coassoc_right_assoc` / 引理 `coassoc_right_assoc`

English:
lemma coassoc_right_assoc
  given: [Coalgebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M)
  proof: by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

中文:
引理 coassoc_right_assoc
  条件: [余algebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M)
  证明: by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc
-/
lemma coassoc_right_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M) :
    α⁻¹ ∘ₗ (f otimesₘ δ) ∘ₗ δ ∘ₗ g = ((f otimesₘ id) otimesₘ id) ∘ₗ (δ otimesₘ id) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

/--
lemma `map_counit_comp_comul_left` / 引理 `map_counit_comp_comul_left`

English:
lemma map_counit_comp_comul_left
  given: [Coalgebra R M] (f : M ->ₗ[R] M')
  proof: by
  rw [← LinearMap.lTensor_comp_rTensor]; rw [LinearMap.comp_assoc]; rw [Coalgebra.rTensor_counit_comp_comul]
  rfl

中文:
引理 map_counit_comp_comul_left
  条件: [余algebra R M] (f : M ->ₗ[R] M')
  证明: by
  rw [← LinearMap.lTensor_comp_rTensor]; rw [LinearMap.comp_assoc]; rw [Coalgebra.rTensor_counit_comp_comul]
  rfl

Depends on / 依赖: Coalgebra, Coalgebra.rTensor_counit_comp_comul, LinearMap, LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor, comp_assoc, lTensor_comp_rTensor, rTensor_counit_comp_comul
-/
lemma map_counit_comp_comul_left [Coalgebra R M] (f : M ->ₗ[R] M') :
    (ε otimesₘ f) ∘ₗ δ = (id otimesₘ f) ∘ₗ fun⁻¹ := by
  rw [← LinearMap.lTensor_comp_rTensor]; rw [LinearMap.comp_assoc]; rw [Coalgebra.rTensor_counit_comp_comul]
  rfl

/--
lemma `map_counit_comp_comul_left_assoc` / 引理 `map_counit_comp_comul_left_assoc`

English:
lemma map_counit_comp_comul_left_assoc
  given: [Coalgebra R M] (f : M ->ₗ[R] M') (g : P ->ₗ[R] M)
  proof: by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]

中文:
引理 map_counit_comp_comul_left_assoc
  条件: [余algebra R M] (f : M ->ₗ[R] M') (g : P ->ₗ[R] M)
  证明: by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, map_counit_comp_comul_left, simp_rw
-/
lemma map_counit_comp_comul_left_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : P ->ₗ[R] M) :
    (ε otimesₘ f) ∘ₗ δ ∘ₗ g = (id otimesₘ f) ∘ₗ fun⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]

/--
lemma `map_counit_comp_comul_right` / 引理 `map_counit_comp_comul_right`

English:
lemma map_counit_comp_comul_right
  given: [Coalgebra R M] (f : M ->ₗ[R] M')
  proof: by
  rw [← LinearMap.rTensor_comp_lTensor]; rw [LinearMap.comp_assoc]; rw [Coalgebra.lTensor_counit_comp_comul]
  rfl

中文:
引理 map_counit_comp_comul_right
  条件: [余algebra R M] (f : M ->ₗ[R] M')
  证明: by
  rw [← LinearMap.rTensor_comp_lTensor]; rw [LinearMap.comp_assoc]; rw [Coalgebra.lTensor_counit_comp_comul]
  rfl

Depends on / 依赖: Coalgebra, Coalgebra.lTensor_counit_comp_comul, LinearMap, LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_lTensor
-/
lemma map_counit_comp_comul_right [Coalgebra R M] (f : M ->ₗ[R] M') :
    (f otimesₘ ε) ∘ₗ δ = (f otimesₘ id) ∘ₗ ρ⁻¹ := by
  rw [← LinearMap.rTensor_comp_lTensor]; rw [LinearMap.comp_assoc]; rw [Coalgebra.lTensor_counit_comp_comul]
  rfl

/--
lemma `map_counit_comp_comul_right_assoc` / 引理 `map_counit_comp_comul_right_assoc`

English:
lemma map_counit_comp_comul_right_assoc
  given: [Coalgebra R M] (f : M ->ₗ[R] M') (g : P ->ₗ[R] M)
  proof: by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

@[coassoc_simps]

中文:
引理 map_counit_comp_comul_right_assoc
  条件: [余algebra R M] (f : M ->ₗ[R] M') (g : P ->ₗ[R] M)
  证明: by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

@[coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, map_counit_comp_comul_right, simp_rw
-/
lemma map_counit_comp_comul_right_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : P ->ₗ[R] M) :
    (f otimesₘ ε) ∘ₗ δ ∘ₗ g = (f otimesₘ id) ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

@[coassoc_simps]
/--
lemma `assoc_comp_map_comm_comp_comul_comp_comul` / 引理 `assoc_comp_map_comm_comp_comul_comp_comul`

English:
lemma assoc_comp_map_comm_comp_comul_comp_comul
  given: [Coalgebra R M] (f : M ->ₗ[R] N)
  proof: by
  rw [← symm_comp_map_assoc]; rw [← LinearMap.lTensor_def]; rw [← LinearMap.lTensor_def]; rw [← LinearMap.lTensor_def]; rw [← Coalgebra.coassoc]; rw [← f.comp_id]; rw [TensorProduct.map_comp]; rw [← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]

中文:
引理 assoc_comp_map_comm_comp_comul_comp_comul
  条件: [余algebra R M] (f : M ->ₗ[R] N)
  证明: by
  rw [← symm_comp_map_assoc]; rw [← LinearMap.lTensor_def]; rw [← LinearMap.lTensor_def]; rw [← LinearMap.lTensor_def]; rw [← Coalgebra.coassoc]; rw [← f.comp_id]; rw [TensorProduct.map_comp]; rw [← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]

Depends on / 依赖: Coalgebra, Coalgebra.coassoc, LinearMap, LinearMap.comp_assoc, LinearMap.lTensor_def, LinearMap.rTensor_def, TensorProduct, TensorProduct.map_comp, coassoc, comp_assoc, comp_id, f.comp_id, lTensor_def, map_comp, rTensor_def, symm_comp_map_assoc
-/
lemma assoc_comp_map_comm_comp_comul_comp_comul [Coalgebra R M] (f : M ->ₗ[R] N) :
    α ∘ₗ ((β ∘ₗ δ) otimesₘ f) ∘ₗ δ = (id otimesₘ ((id otimesₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ otimesₘ id ∘ₗ β ∘ₗ δ := by
  rw [← symm_comp_map_assoc]; rw [← LinearMap.lTensor_def]; rw [← LinearMap.lTensor_def]; rw [← LinearMap.lTensor_def]; rw [← Coalgebra.coassoc]; rw [← f.comp_id]; rw [TensorProduct.map_comp]; rw [← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]
/--
lemma `assoc_comp_map_comm_comp_comul_comp_comul_assoc` / 引理 `assoc_comp_map_comm_comp_comul_comp_comul_assoc`

English:
lemma assoc_comp_map_comm_comp_comul_comp_comul_assoc
  proof: by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

中文:
引理 assoc_comp_map_comm_comp_comul_comp_comul_assoc
  证明: by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, coassoc_simps, comp_assoc, simp_rw
-/
lemma assoc_comp_map_comm_comp_comul_comp_comul_assoc
    [Coalgebra R M] (f : M ->ₗ[R] N) (h : Q ->ₗ[R] M) :
    α ∘ₗ ((β ∘ₗ δ) otimesₘ f) ∘ₗ δ ∘ₗ h = (id otimesₘ ((id otimesₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ otimesₘ id ∘ₗ β ∘ₗ δ ∘ₗ h := by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

end CoassocSimps
