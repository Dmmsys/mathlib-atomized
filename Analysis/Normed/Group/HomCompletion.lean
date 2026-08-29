/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : NormedAddGroupHom G H`,
we build and study a normed group hom
`f.completion : NormedAddGroupHom (completion G) (completion H)` such that the diagram

```
                   f
     G -----------> H

     | |
     | |
     | |
     V V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `NormedAddGroupHom.completion`: see the discussion above.
* `NormedAddCommGroup.toCompl : NormedAddGroupHom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `NormedAddGroupHom.completion_toCompl`: the above diagram indeed commutes.
* `NormedAddGroupHom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `NormedAddGroupHom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `NormedAddGroupHom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `NormedAddGroupHom.extension` : if `H` is complete, the extension of
  `f : NormedAddGroupHom G H` to a `NormedAddGroupHom (completion G) H`.
-/

@[expose] public section


noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type*} [SeminormedAddCommGroup G] {H : Type*} [SeminormedAddCommGroup H]
  {K : Type*} [SeminormedAddCommGroup K]

/--
Definition of `NormedAddGroupHom.completion` / `NormedAddGroupHom.completion` 的定义

English:
definition NormedAddGroupHom.completion
  signature: (f : NormedAddGroupHom G H)
  body: .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map

中文:
定义 赋范加群态射.completion
  签名: (f : 赋范加群态射 G H)
  定义体: .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map

Depends on / 依赖: completion, completion_map, continuous, f.continuous, f.lipschitz.completion_map, f.toAddMonoidHom.completion, lipschitz, ofLipschitz, toAddMonoidHom
-/
def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map

/--
theorem `NormedAddGroupHom.completion_def` / 定理 `NormedAddGroupHom.completion_def`

English:
theorem NormedAddGroupHom.completion_def
  given: (f : NormedAddGroupHom G H) (x : Completion G)
  proof: rfl

@[simp]

中文:
定理 赋范加群态射.completion_def
  条件: (f : 赋范加群态射 G H) (x : 完备化 G)
  证明: rfl

@[simp]
-/
theorem NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completion G) :
    f.completion x = Completion.map f x :=
  rfl

@[simp]
/--
theorem `NormedAddGroupHom.completion_coe_to_fun` / 定理 `NormedAddGroupHom.completion_coe_to_fun`

English:
theorem NormedAddGroupHom.completion_coe_to_fun
  given: (f : NormedAddGroupHom G H)
  proof: rfl

中文:
定理 赋范加群态射.completion_coe_to_fun
  条件: (f : 赋范加群态射 G H)
  证明: rfl
-/
theorem NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.completion : Completion G -> Completion H) = Completion.map f := rfl

/--
theorem `NormedAddGroupHom.completion_coe` / 定理 `NormedAddGroupHom.completion_coe`

English:
theorem NormedAddGroupHom.completion_coe
  given: (f : NormedAddGroupHom G H) (g : G)
  proof: Completion.map_coe f.uniformContinuous _

@[simp]

中文:
定理 赋范加群态射.completion_coe
  条件: (f : 赋范加群态射 G H) (g : G)
  证明: Completion.map_coe f.uniformContinuous _

@[simp]

Depends on / 依赖: Completion, Completion.map_coe, f.uniformContinuous, map_coe, uniformContinuous
-/
theorem NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) :
    f.completion g = f g :=
  Completion.map_coe f.uniformContinuous _

@[simp]
/--
theorem `NormedAddGroupHom.completion_coe'` / 定理 `NormedAddGroupHom.completion_coe'`

English:
theorem NormedAddGroupHom.completion_coe'
  given: (f : NormedAddGroupHom G H) (g : G)
  proof: f.completion_coe g

中文:
定理 赋范加群态射.completion_coe'
  条件: (f : 赋范加群态射 G H) (g : G)
  证明: f.completion_coe g

Depends on / 依赖: completion_coe, f.completion_coe
-/
theorem NormedAddGroupHom.completion_coe' (f : NormedAddGroupHom G H) (g : G) :
    Completion.map f g = f g :=
  f.completion_coe g

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
/--
Definition of `normedAddGroupHomCompletionHom` / `normedAddGroupHomCompletionHom` 的定义

English:
definition normedAddGroupHomCompletionHom
  signature: :
  body: NormedAddGroupHom.completion
  map_zero' := toAddMonoidHom_injective AddMonoidHom.completion_zero
map_add' f g := toAddMonoidHom_injective
    f.toAddMonoidHom.completion_add g.toAddMonoidHom f.continuous g.continuous

@[simp]

中文:
定义 normedAddGroupHomCompletionHom
  签名: :
  定义体: NormedAddGroupHom.completion
  map_zero' := toAddMonoidHom_injective AddMonoidHom.completion_zero
map_add' f g := toAddMonoidHom_injective
    f.toAddMonoidHom.completion_add g.toAddMonoidHom f.continuous g.continuous

@[simp]

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.completion, completion
-/
def normedAddGroupHomCompletionHom :
    NormedAddGroupHom G H ->+ NormedAddGroupHom (Completion G) (Completion H) where
  toFun := NormedAddGroupHom.completion
  map_zero' := toAddMonoidHom_injective AddMonoidHom.completion_zero
map_add' f g := toAddMonoidHom_injective
    f.toAddMonoidHom.completion_add g.toAddMonoidHom f.continuous g.continuous

@[simp]
/--
theorem `NormedAddGroupHom.completion_id` / 定理 `NormedAddGroupHom.completion_id`

English:
theorem NormedAddGroupHom.completion_id
  proof: by
  ext x
  rw [NormedAddGroupHom.completion_def]; rw [NormedAddGroupHom.coe_id]; rw [Completion.map_id]
  rfl

中文:
定理 赋范加群态射.completion_id
  证明: by
  ext x
  rw [NormedAddGroupHom.completion_def]; rw [NormedAddGroupHom.coe_id]; rw [Completion.map_id]
  rfl

Depends on / 依赖: Completion, Completion.map_id, NormedAddGroupHom, NormedAddGroupHom.coe_id, NormedAddGroupHom.completion_def, coe_id, completion_def, map_id
-/
theorem NormedAddGroupHom.completion_id :
    (NormedAddGroupHom.id G).completion = NormedAddGroupHom.id (Completion G) := by
  ext x
  rw [NormedAddGroupHom.completion_def]; rw [NormedAddGroupHom.coe_id]; rw [Completion.map_id]
  rfl

/--
theorem `NormedAddGroupHom.completion_comp` / 定理 `NormedAddGroupHom.completion_comp`

English:
theorem NormedAddGroupHom.completion_comp
  given: (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K)
  proof: by
  ext x
  rw [NormedAddGroupHom.coe_comp]; rw [NormedAddGroupHom.completion_def]; rw [NormedAddGroupHom.completion_coe_to_fun]; rw [NormedAddGroupHom.completion_coe_to_fun]; rw [Completion.map_comp g.uniformContinuous f.uniformContinuous]
  rfl

中文:
定理 赋范加群态射.completion_comp
  条件: (f : 赋范加群态射 G H) (g : 赋范加群态射 H K)
  证明: by
  ext x
  rw [NormedAddGroupHom.coe_comp]; rw [NormedAddGroupHom.completion_def]; rw [NormedAddGroupHom.completion_coe_to_fun]; rw [NormedAddGroupHom.completion_coe_to_fun]; rw [Completion.map_comp g.uniformContinuous f.uniformContinuous]
  rfl

Depends on / 依赖: Completion, Completion.map_comp, NormedAddGroupHom, NormedAddGroupHom.coe_comp, NormedAddGroupHom.completion_coe_to_fun, NormedAddGroupHom.completion_def, coe_comp, completion_coe_to_fun, completion_def, f.uniformContinuous, g.uniformContinuous, map_comp, uniformContinuous
-/
theorem NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K) :
    g.completion.comp f.completion = (g.comp f).completion := by
  ext x
  rw [NormedAddGroupHom.coe_comp]; rw [NormedAddGroupHom.completion_def]; rw [NormedAddGroupHom.completion_coe_to_fun]; rw [NormedAddGroupHom.completion_coe_to_fun]; rw [Completion.map_comp g.uniformContinuous f.uniformContinuous]
  rfl

/--
theorem `NormedAddGroupHom.completion_neg` / 定理 `NormedAddGroupHom.completion_neg`

English:
theorem NormedAddGroupHom.completion_neg
  given: (f : NormedAddGroupHom G H)
  proof: map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ _) f

中文:
定理 赋范加群态射.completion_neg
  条件: (f : 赋范加群态射 G H)
  证明: map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ _) f

Depends on / 依赖: NormedAddGroupHom, map_neg, normedAddGroupHomCompletionHom
-/
theorem NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) :
    (-f).completion = -f.completion :=
  map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ _) f

/--
theorem `NormedAddGroupHom.completion_add` / 定理 `NormedAddGroupHom.completion_add`

English:
theorem NormedAddGroupHom.completion_add
  given: (f g : NormedAddGroupHom G H)
  proof: normedAddGroupHomCompletionHom.map_add f g

中文:
定理 赋范加群态射.completion_add
  条件: (f g : 赋范加群态射 G H)
  证明: normedAddGroupHomCompletionHom.map_add f g

Depends on / 依赖: map_add, normedAddGroupHomCompletionHom, normedAddGroupHomCompletionHom.map_add
-/
theorem NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) :
    (f + g).completion = f.completion + g.completion :=
  normedAddGroupHomCompletionHom.map_add f g

/--
theorem `NormedAddGroupHom.completion_sub` / 定理 `NormedAddGroupHom.completion_sub`

English:
theorem NormedAddGroupHom.completion_sub
  given: (f g : NormedAddGroupHom G H)
  proof: map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ _) f g

@[simp]

中文:
定理 赋范加群态射.completion_sub
  条件: (f g : 赋范加群态射 G H)
  证明: map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ _) f g

@[simp]

Depends on / 依赖: NormedAddGroupHom, map_sub, normedAddGroupHomCompletionHom
-/
theorem NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) :
    (f - g).completion = f.completion - g.completion :=
  map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ _) f g

@[simp]
/--
theorem `NormedAddGroupHom.zero_completion` / 定理 `NormedAddGroupHom.zero_completion`

English:
theorem NormedAddGroupHom.zero_completion
  statement: (0 : NormedAddGroupHom G H).completion = 0
  proof: normedAddGroupHomCompletionHom.map_zero

中文:
定理 赋范加群态射.zero_completion
  结论: (0 : 赋范加群态射 G H).completion = 0
  证明: normedAddGroupHomCompletionHom.map_zero

Depends on / 依赖: map_zero, normedAddGroupHomCompletionHom, normedAddGroupHomCompletionHom.map_zero
-/
theorem NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).completion = 0 :=
  normedAddGroupHomCompletionHom.map_zero

/-- The map from a normed group to its completion, as a normed group hom. -/
@[simps]
/--
Definition of `NormedAddCommGroup.toCompl` / `NormedAddCommGroup.toCompl` 的定义

English:
definition NormedAddCommGroup.toCompl
  signature: : NormedAddGroupHom G (Completion G) where
  body: (↑)
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp⟩

中文:
定义 赋范交换加群.toCompl
  签名: : 赋范加群态射 G (完备化 G) where
  定义体: (↑)
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp⟩
-/
def NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G) where
  toFun := (↑)
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp⟩

open NormedAddCommGroup

/--
theorem `NormedAddCommGroup.norm_toCompl` / 定理 `NormedAddCommGroup.norm_toCompl`

English:
theorem NormedAddCommGroup.norm_toCompl
  given: (x : G)
  statement: ‖toCompl x‖ = ‖x‖
  proof: Completion.norm_coe x

中文:
定理 赋范交换加群.norm_toCompl
  条件: (x : G)
  结论: ‖toCompl x‖ = ‖x‖
  证明: Completion.norm_coe x

Depends on / 依赖: Completion, Completion.norm_coe, norm_coe
-/
theorem NormedAddCommGroup.norm_toCompl (x : G) : ‖toCompl x‖ = ‖x‖ :=
  Completion.norm_coe x

/--
theorem `NormedAddCommGroup.denseRange_toCompl` / 定理 `NormedAddCommGroup.denseRange_toCompl`

English:
theorem NormedAddCommGroup.denseRange_toCompl
  statement: DenseRange (toCompl : G -> Completion G)
  proof: Completion.isDenseInducing_coe.dense

@[simp]

中文:
定理 赋范交换加群.denseRange_toCompl
  结论: DenseRange (toCompl : G -> 完备化 G)
  证明: Completion.isDenseInducing_coe.dense

@[simp]

Depends on / 依赖: Completion, Completion.isDenseInducing_coe.dense, isDenseInducing_coe
-/
theorem NormedAddCommGroup.denseRange_toCompl : DenseRange (toCompl : G -> Completion G) :=
  Completion.isDenseInducing_coe.dense

@[simp]
/--
theorem `NormedAddGroupHom.completion_toCompl` / 定理 `NormedAddGroupHom.completion_toCompl`

English:
theorem NormedAddGroupHom.completion_toCompl
  given: (f : NormedAddGroupHom G H)
  proof: by ext x; simp

@[simp]

中文:
定理 赋范加群态射.completion_toCompl
  条件: (f : 赋范加群态射 G H)
  证明: by ext x; simp

@[simp]
-/
theorem NormedAddGroupHom.completion_toCompl (f : NormedAddGroupHom G H) :
    f.completion.comp toCompl = toCompl.comp f := by ext x; simp

@[simp]
/--
theorem `NormedAddGroupHom.norm_completion` / 定理 `NormedAddGroupHom.norm_completion`

English:
theorem NormedAddGroupHom.norm_completion
  given: (f : NormedAddGroupHom G H)
  statement: ‖f.completion‖ = ‖f‖
  proof: le_antisymm (ofLipschitz_norm_le _ _) opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using f.completion.le_opNorm x

中文:
定理 赋范加群态射.norm_completion
  条件: (f : 赋范加群态射 G H)
  结论: ‖f.completion‖ = ‖f‖
  证明: le_antisymm (ofLipschitz_norm_le _ _) opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using f.completion.le_opNorm x

Depends on / 依赖: completion, f.completion.le_opNorm, le_antisymm, le_opNorm, norm_nonneg, ofLipschitz_norm_le, opNorm_le_bound
-/
theorem NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.completion‖ = ‖f‖ :=
le_antisymm (ofLipschitz_norm_le _ _) opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using f.completion.le_opNorm x

/--
theorem `NormedAddGroupHom.ker_le_ker_completion` / 定理 `NormedAddGroupHom.ker_le_ker_completion`

English:
theorem NormedAddGroupHom.ker_le_ker_completion
  given: (f : NormedAddGroupHom G H)
  proof: by
  rintro _ ⟨⟨g, h₀ : f g = 0⟩, rfl⟩
  simp [h₀, mem_ker, Completion.coe_zero]

中文:
定理 赋范加群态射.ker_le_ker_completion
  条件: (f : 赋范加群态射 G H)
  证明: by
  rintro _ ⟨⟨g, h₀ : f g = 0⟩, rfl⟩
  simp [h₀, mem_ker, Completion.coe_zero]

Depends on / 依赖: Completion, Completion.coe_zero, coe_zero, mem_ker
-/
theorem NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) :
    (toCompl.comp <| incl f.ker).range <= f.completion.ker := by
  rintro _ ⟨⟨g, h₀ : f g = 0⟩, rfl⟩
  simp [h₀, mem_ker, Completion.coe_zero]

/--
theorem `NormedAddGroupHom.ker_completion` / 定理 `NormedAddGroupHom.ker_completion`

English:
theorem NormedAddGroupHom.ker_completion
  statement: {f : NormedAddGroupHom G H} {C : Real}
  proof: by
  refine le_antisymm ?_ (closure_minimal f.ker_le_ker_completion f.completion.isClosed_ker)
  rintro hatg (hatg_in : f.completion hatg = 0)
  rw [SeminormedAddCommGroup.mem_closure_iff]
  intro ε ε_pos
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  rcases exists_pos_mul_lt ε_pos (1 + C' * ‖f‖) with ⟨δ, δ_pos, hδ⟩
  obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp (Completion.isDenseInducing_coe.dense hatg) δ δ_pos
  obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ <= C' * ‖f g‖⟩ := hC' (f g) (mem_range_self _ g)
  have mem_ker : g - g' in f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
  refine ⟨_, ⟨⟨g - g', mem_ker⟩, rfl⟩, ?_⟩
  have : ‖f g‖ <= ‖f‖ * δ := calc
    ‖f g‖ <= ‖f‖ * ‖hatg - g‖ := by
      simpa [map_sub, hatg_in] using f.completion.le_opNorm (hatg - g)
    _ <= ‖f‖ * δ := by gcongr
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ <= ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ <= δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ

中文:
定理 赋范加群态射.ker_completion
  结论: {f : 赋范加群态射 G H} {C : 实数}
  证明: by
  refine le_antisymm ?_ (closure_minimal f.ker_le_ker_completion f.completion.isClosed_ker)
  rintro hatg (hatg_in : f.completion hatg = 0)
  rw [SeminormedAddCommGroup.mem_closure_iff]
  intro ε ε_pos
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  rcases exists_pos_mul_lt ε_pos (1 + C' * ‖f‖) with ⟨δ, δ_pos, hδ⟩
  obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp (Completion.isDenseInducing_coe.dense hatg) δ δ_pos
  obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ <= C' * ‖f g‖⟩ := hC' (f g) (mem_range_self _ g)
  have mem_ker : g - g' in f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
  refine ⟨_, ⟨⟨g - g', mem_ker⟩, rfl⟩, ?_⟩
  have : ‖f g‖ <= ‖f‖ * δ := calc
    ‖f g‖ <= ‖f‖ * ‖hatg - g‖ := by
      simpa [map_sub, hatg_in] using f.completion.le_opNorm (hatg - g)
    _ <= ‖f‖ * δ := by gcongr
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ <= ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ <= δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ

Depends on / 依赖: Completion, Completion.isDenseInducing_coe.dense, SeminormedAddCommGroup, SeminormedAddCommGroup.mem_closure_iff, SeminormedAddCommGroup.mem_closure_iff.mp, _pos, closure_minimal, completion, exists_pos, exists_pos_mul_lt, f.completion, f.completion.isClosed_ker, f.ker_le_ker_completion, h.exists_pos, hatg_in, isClosed_ker, isDenseInducing_coe, ker_le_ker_completion, le_antisymm, mem_closure_iff
-/
theorem NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : Real}
    (h : f.SurjectiveOnWith f.range C) :
    (f.completion.ker : Set <| Completion G) = closure (toCompl.comp <| incl f.ker).range := by
  refine le_antisymm ?_ (closure_minimal f.ker_le_ker_completion f.completion.isClosed_ker)
  rintro hatg (hatg_in : f.completion hatg = 0)
  rw [SeminormedAddCommGroup.mem_closure_iff]
  intro ε ε_pos
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  rcases exists_pos_mul_lt ε_pos (1 + C' * ‖f‖) with ⟨δ, δ_pos, hδ⟩
  obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp (Completion.isDenseInducing_coe.dense hatg) δ δ_pos
  obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ <= C' * ‖f g‖⟩ := hC' (f g) (mem_range_self _ g)
  have mem_ker : g - g' in f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
  refine ⟨_, ⟨⟨g - g', mem_ker⟩, rfl⟩, ?_⟩
  have : ‖f g‖ <= ‖f‖ * δ := calc
    ‖f g‖ <= ‖f‖ * ‖hatg - g‖ := by
      simpa [map_sub, hatg_in] using f.completion.le_opNorm (hatg - g)
    _ <= ‖f‖ * δ := by gcongr
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ <= ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ <= δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ

end Completion

section Extension

variable {G : Type*} [SeminormedAddCommGroup G]
variable {H : Type*} [SeminormedAddCommGroup H] [T0Space H] [CompleteSpace H]

/--
Definition of `NormedAddGroupHom.extension` / `NormedAddGroupHom.extension` 的定义

English:
definition NormedAddGroupHom.extension
  signature: (f : NormedAddGroupHom G H)
  body: .ofLipschitz (f.toAddMonoidHom.extension f.continuous)
    let _ := MetricSpace.ofT0PseudoMetricSpace H
    f.lipschitz.completion_extension

中文:
定义 赋范加群态射.extension
  签名: (f : 赋范加群态射 G H)
  定义体: .ofLipschitz (f.toAddMonoidHom.extension f.continuous)
    let _ := MetricSpace.ofT0PseudoMetricSpace H
    f.lipschitz.completion_extension

Depends on / 依赖: MetricSpace, MetricSpace.ofT0PseudoMetricSpace, completion_extension, continuous, extension, f.continuous, f.lipschitz.completion_extension, f.toAddMonoidHom.extension, lipschitz, ofLipschitz, ofT0PseudoMetricSpace, toAddMonoidHom
-/
def NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHom (Completion G) H :=
.ofLipschitz (f.toAddMonoidHom.extension f.continuous)
    let _ := MetricSpace.ofT0PseudoMetricSpace H
    f.lipschitz.completion_extension

/--
theorem `NormedAddGroupHom.extension_def` / 定理 `NormedAddGroupHom.extension_def`

English:
theorem NormedAddGroupHom.extension_def
  given: (f : NormedAddGroupHom G H) (v : G)
  proof: rfl

@[simp]

中文:
定理 赋范加群态射.extension_def
  条件: (f : 赋范加群态射 G H) (v : G)
  证明: rfl

@[simp]
-/
theorem NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) :
    f.extension v = Completion.extension f v :=
  rfl

@[simp]
/--
theorem `NormedAddGroupHom.extension_coe` / 定理 `NormedAddGroupHom.extension_coe`

English:
theorem NormedAddGroupHom.extension_coe
  given: (f : NormedAddGroupHom G H) (v : G)
  statement: f.extension v = f v
  proof: AddMonoidHom.extension_coe _ f.continuous _

中文:
定理 赋范加群态射.extension_coe
  条件: (f : 赋范加群态射 G H) (v : G)
  结论: f.extension v = f v
  证明: AddMonoidHom.extension_coe _ f.continuous _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.extension_coe, continuous, extension_coe, f.continuous
-/
theorem NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.continuous _

/--
theorem `NormedAddGroupHom.extension_coe_to_fun` / 定理 `NormedAddGroupHom.extension_coe_to_fun`

English:
theorem NormedAddGroupHom.extension_coe_to_fun
  given: (f : NormedAddGroupHom G H)
  proof: rfl

中文:
定理 赋范加群态射.extension_coe_to_fun
  条件: (f : 赋范加群态射 G H)
  证明: rfl
-/
theorem NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.extension : Completion G -> H) = Completion.extension f :=
  rfl

/--
theorem `NormedAddGroupHom.extension_unique` / 定理 `NormedAddGroupHom.extension_unique`

English:
theorem NormedAddGroupHom.extension_unique
  statement: (f : NormedAddGroupHom G H)
  proof: by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun]; rw [Completion.extension_unique f.uniformContinuous g.uniformContinuous fun a => hg a]

中文:
定理 赋范加群态射.extension_unique
  结论: (f : 赋范加群态射 G H)
  证明: by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun]; rw [Completion.extension_unique f.uniformContinuous g.uniformContinuous fun a => hg a]

Depends on / 依赖: Completion, Completion.extension_unique, NormedAddGroupHom, NormedAddGroupHom.extension_coe_to_fun, extension_coe_to_fun, extension_unique, f.uniformContinuous, g.uniformContinuous, uniformContinuous
-/
theorem NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H)
    {g : NormedAddGroupHom (Completion G) H} (hg : forall v, f v = g v) : f.extension = g := by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun]; rw [Completion.extension_unique f.uniformContinuous g.uniformContinuous fun a => hg a]

end Extension
