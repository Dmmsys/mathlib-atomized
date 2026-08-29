/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Asymptotics in the completion of a normed space

In this file we prove lemmas relating `f = O(g)` etc
for composition of functions with coercion of a seminormed group to its completion.
-/

public section

variable {α E F : Type*} [Norm E] [SeminormedAddCommGroup F]
  {f : α -> E} {g : α -> F} {l : Filter α}

local postfix:100 "̂" => UniformSpace.Completion

open UniformSpace.Completion

namespace Asymptotics

@[simp, norm_cast]
/--
lemma `isBigO_completion_left` / 引理 `isBigO_completion_left`

English:
lemma isBigO_completion_left
  statement: (fun x => g x : α -> F̂) =O[l] f ↔ g =O[l] f
  proof: by
  simp only [isBigO_iff, norm_coe]

@[simp, norm_cast]

中文:
引理 isBigO_completion_left
  结论: (fun x => g x : α -> F̂) =O[l] f ↔ g =O[l] f
  证明: by
  simp only [isBigO_iff, norm_coe]

@[simp, norm_cast]

Depends on / 依赖: isBigO_iff, norm_coe
-/
lemma isBigO_completion_left : (fun x => g x : α -> F̂) =O[l] f ↔ g =O[l] f := by
  simp only [isBigO_iff, norm_coe]

@[simp, norm_cast]
/--
lemma `isBigO_completion_right` / 引理 `isBigO_completion_right`

English:
lemma isBigO_completion_right
  statement: f =O[l] (fun x => g x : α -> F̂) ↔ f =O[l] g
  proof: by
  simp only [isBigO_iff, norm_coe]

@[simp, norm_cast]

中文:
引理 isBigO_completion_right
  结论: f =O[l] (fun x => g x : α -> F̂) ↔ f =O[l] g
  证明: by
  simp only [isBigO_iff, norm_coe]

@[simp, norm_cast]

Depends on / 依赖: isBigO_iff, norm_coe
-/
lemma isBigO_completion_right : f =O[l] (fun x => g x : α -> F̂) ↔ f =O[l] g := by
  simp only [isBigO_iff, norm_coe]

@[simp, norm_cast]
/--
lemma `isTheta_completion_left` / 引理 `isTheta_completion_left`

English:
lemma isTheta_completion_left
  statement: (fun x => g x : α -> F̂) =Θ[l] f ↔ g =Θ[l] f
  proof: and_congr isBigO_completion_left isBigO_completion_right

@[simp, norm_cast]

中文:
引理 isTheta_completion_left
  结论: (fun x => g x : α -> F̂) =Θ[l] f ↔ g =Θ[l] f
  证明: and_congr isBigO_completion_left isBigO_completion_right

@[simp, norm_cast]

Depends on / 依赖: and_congr, isBigO_completion_left, isBigO_completion_right
-/
lemma isTheta_completion_left : (fun x => g x : α -> F̂) =Θ[l] f ↔ g =Θ[l] f :=
  and_congr isBigO_completion_left isBigO_completion_right

@[simp, norm_cast]
/--
lemma `isTheta_completion_right` / 引理 `isTheta_completion_right`

English:
lemma isTheta_completion_right
  statement: f =Θ[l] (fun x => g x : α -> F̂) ↔ f =Θ[l] g
  proof: and_congr isBigO_completion_right isBigO_completion_left

@[simp, norm_cast]

中文:
引理 isTheta_completion_right
  结论: f =Θ[l] (fun x => g x : α -> F̂) ↔ f =Θ[l] g
  证明: and_congr isBigO_completion_right isBigO_completion_left

@[simp, norm_cast]

Depends on / 依赖: and_congr, isBigO_completion_left, isBigO_completion_right
-/
lemma isTheta_completion_right : f =Θ[l] (fun x => g x : α -> F̂) ↔ f =Θ[l] g :=
  and_congr isBigO_completion_right isBigO_completion_left

@[simp, norm_cast]
/--
lemma `isLittleO_completion_left` / 引理 `isLittleO_completion_left`

English:
lemma isLittleO_completion_left
  statement: (fun x => g x : α -> F̂) =o[l] f ↔ g =o[l] f
  proof: by
  simp only [isLittleO_iff, norm_coe]

@[simp, norm_cast]

中文:
引理 isLittleO_completion_left
  结论: (fun x => g x : α -> F̂) =o[l] f ↔ g =o[l] f
  证明: by
  simp only [isLittleO_iff, norm_coe]

@[simp, norm_cast]

Depends on / 依赖: isLittleO_iff, norm_coe
-/
lemma isLittleO_completion_left : (fun x => g x : α -> F̂) =o[l] f ↔ g =o[l] f := by
  simp only [isLittleO_iff, norm_coe]

@[simp, norm_cast]
/--
lemma `isLittleO_completion_right` / 引理 `isLittleO_completion_right`

English:
lemma isLittleO_completion_right
  statement: f =o[l] (fun x => g x : α -> F̂) ↔ f =o[l] g
  proof: by
  simp only [isLittleO_iff, norm_coe]

中文:
引理 isLittleO_completion_right
  结论: f =o[l] (fun x => g x : α -> F̂) ↔ f =o[l] g
  证明: by
  simp only [isLittleO_iff, norm_coe]

Depends on / 依赖: isLittleO_iff, norm_coe
-/
lemma isLittleO_completion_right : f =o[l] (fun x => g x : α -> F̂) ↔ f =o[l] g := by
  simp only [isLittleO_iff, norm_coe]

end Asymptotics
